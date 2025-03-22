"use strict";

import type { Ace } from "ace-builds";

const AceRange = ace.require("ace/range").Range;

window.gobraBookEditorContext = new Map<string, Context>();

const DEFAULT_LANGUAGE = "gobra";
const GOBRA_INLINE = /\/\*@.*@\*\//g;
const GOBRA_COMMENT = /\/\/\s*?@/;
const GOBRA_PLAYGROUND = new URL("https://gobra.void.gschall.ch/verify");
const GO_PLAYGROUND = new URL("https://gobra.void.gschall.ch/run");

function fetch_with_timeout(
  url: URL,
  options: RequestInit,
  timeout = 20000,
): Promise<any> {
  return Promise.race([
    fetch(url, options),
    new Promise((_, reject) =>
      setTimeout(() => reject(new Error("timeout")), timeout),
    ),
  ]);
}

function verifyGobra(code: string): Promise<any> {
  return fetch_with_timeout(GOBRA_PLAYGROUND, {
    headers: {
      Accept: "application/json, text/javascript, */*; q=0.01",
      "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    },
    body: new URLSearchParams({ body: code }),
    method: "POST",
  })
}

function runGo(code: string): Promise<any> {
  return fetch_with_timeout(GO_PLAYGROUND, {
    headers: {
      Accept: "application/json, text/javascript, */*; q=0.01",
      "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    },
    body: new URLSearchParams({
      version: "2",
      body: code,
      withVet: "true",
    }),
    method: "POST",
  })
}

function language_of(block: HTMLElement) {
  let languages = Array.from(block.classList)
    .filter((cls) => cls.startsWith("language-"))
    .map((cls) => cls.replace("language-", ""));
  if (languages.length == 0) {
    console.warn(
      "no language detected for code block. using default " + DEFAULT_LANGUAGE,
    );
    return DEFAULT_LANGUAGE;
  } else {
    return languages[0];
  }
}

function preprocessHidden(code: string): [string, string] {
  let hiddenCode = code
    .split("\n")
    .filter((line: string) => !/^\s*~/.test(line))
    .join("\n");
  let fullCode = code.replaceAll("~", "");
  return [hiddenCode, fullCode]
}

function simpleButton(class1: string, title: string,
  callback: (ctxt: Context) => any,
  id: string) {
  const button = document.createElement("button");
  button.className = "fa " + class1;
  button.title = title;
  button.setAttribute("aria-label", title);
  button.addEventListener("click", () => {
    callback(window.gobraBookEditorContext.get(id)!)
  });
  return button
}

function toggleButton(class1: string, class2: string, title: string,
  callback1: (ctxt: Context) => any,
  callback2: (ctxt: Context) => any,
  id: string): HTMLButtonElement {
  const button = document.createElement("button");
  button.className = "fa " + class1;
  button.title = title;
  button.setAttribute("aria-label", title);

  function toggler() {
    let toggled = true;
    return function (e: Event) {
      const t = e.target as HTMLButtonElement
      if (toggled) {
        t.classList.replace(class1, class2);
        callback1(window.gobraBookEditorContext.get(id)!)
      } else {
        t.classList.replace(class2, class1);
        callback2(window.gobraBookEditorContext.get(id)!)
      }
      toggled = !toggled;
    };
  }
  button.addEventListener("click", toggler());
  return button
}

const hiddenLinesToggler = (id: string) => toggleButton("fa-eye", "fa-eye-slash", "Show hidden lines",
  (ctxt: Context) => {
    let session = ctxt.editor.getSession()
    session.setValue(ctxt.originalCode);
  },
  (ctxt: Context) => {
    let session = ctxt.editor.getSession()
    session.setValue(ctxt.hiddenCode);
  },
  id
)

const clipboardButton = (id: string) => simpleButton("fa-copy", "Copy to clipboard",
  (ctxt: Context) => {
    const code = ctxt.editor.getSession().getValue()
    navigator.clipboard.writeText(code)
  },
  id
)

const resetButton = (id: string) => simpleButton("fa-history", "Reset to initial example",
  (ctxt: Context) => {
    const code = ctxt.originalCode
    ctxt.editor.getSession().setValue(code)
  },
  id
)

interface GoPlaygroundResult {
  Errors: string,
  Events: {
    Message: string,
    Kind: string,
    Delay: number,
  }[],
  Status: number,
  IsTest: boolean,
  TestsFailed: number,
  VetOK: boolean,
}

const runButton = (id: string) => simpleButton("fa-play", "Run this Go code",
  (ctxt: Context) => {
    const code = ctxt.editor.getSession().getValue()

    const container = ctxt.editor.container.parentNode
    let result_block = container.querySelector(".result");
    if (!result_block) {
      result_block = document.createElement("code");
      result_block.className = "result hljs language-bash";
      container.append(result_block);
    }
    result_block.innerText = "Running...";

    runGo(code)
      .then((response) => response.json())
      .then((response: GoPlaygroundResult) => {
        if (response.Errors) {
          throw new Error(response.Errors);
        } else if (!response.Events.length) {
          result_block.innerText = "No output";
          result_block.classList.add("result-no-output");
        } else {
          result_block.innerText = response.Events.map((e) => e.Message).join(
            "\n",
          );
          result_block.classList.remove("result-no-output");
        }
      })
      .catch(
        (error) =>
        (result_block.innerText =
          "Playground Communication: " + error.message),
      );
  },
  id
)
interface VerificationError {
  message: string,
  position: {
    line: number,
    char: number,
  }
}
const verifyButton = (id: string) => simpleButton("fa-check-circle-o", "Verify with Gobra",
  (ctxt: Context) => {
    const code = ctxt.editor.getSession().getValue()

    const container = ctxt.editor.container.parentNode
    let result_block = container.querySelector(".result");
    if (!result_block) {
      result_block = document.createElement("code");
      result_block.className = "result hljs language-bash";
      container.append(result_block);
    }
    result_block.innerText = "Verifying...";

    verifyGobra(code)
      .then((response) => response.json())
      .then(({ verified, timeout, errors, duration }) => {
        duration = Number(duration).toFixed(2) + " seconds";
        if (verified) {
          result_block.innerHTML = `<i class="fa fa-check-circle-o" aria-hidden="true"></i>`;
          result_block.innerHTML += `<span> Verified successfully in ${duration}</span>`;
        } else if (timeout) {
          result_block.innerHTML = `<i class="fa fa-clock-o" aria-hidden="true"></i>`;
          result_block.innerHTML += `<span> Timeout after ${duration}</span>`;
        } else {
          result_block.innerHTML = `<i class="fa fa-times" aria-hidden="true"></i>`;
          result_block.innerHTML += `<span> Verification failed, taking ${duration}</span>`;
          result_block.innerHTML += errors
            .map((err: VerificationError) => {
              // let position = `(${err.Position.line}, ${err.Position.char})`
              // TODO highlight in editor
              return `<p>ERROR: ${err.message}</p>`;
            })
            .join("");
        }
      })
      .catch(
        (error) =>
        (result_block.innerText =
          "Playground Communication: " + error.message),
      );
  },
  id
)

function initBlock(code_block: HTMLElement) {
  let uuid = crypto.randomUUID();
  code_block.id = uuid;

  let language = language_of(code_block);
  let readonly = !code_block.classList.contains("editable");

  let editor = ace.edit(code_block);
  let session = editor.getSession();
  let display_line_numbers = window.playground_line_numbers || false;


  // Configure the editor
  editor.setOptions({
    readOnly: readonly,
    highlightGutterLine: readonly,
    showPrintMargin: false,
    showLineNumbers: display_line_numbers,
    showGutter: display_line_numbers,
    maxLines: Infinity,
    fontSize: "0.875em", // please adjust the font size of the code in general.css
  });
  if (readonly) {
    editor.renderer.$cursorLayer.element.style.opacity = 0;
  }

  editor.$blockScrolling = Infinity;

  // Preprocess the source code
  const [fullCode, hiddenCode] = preprocessHidden(session.getValue())
  if (readonly) {
    session.setValue(hiddenCode);
  }
  // TODO extract error information

  // Bind Commands to keybindings
  editor.commands.addCommand({
    name: "highlightSpecs",
    bindKey: { win: "Ctrl-L", mac: "Cmd-L" },
    exec: specsToggler(),
  });
  editor.commands.addCommand({
    name: "runGo",
    bindKey: {
      win: "Ctrl-Shift-Enter",
      mac: "Ctrl-Shift-Enter",
    },
    exec: (editor: Ace.Editor) => runGo(editor.getSession().getValue()),
  });
  editor.commands.addCommand({
    name: "verifyGobra",
    bindKey: {
      win: "Ctrl-Enter",
      mac: "Ctrl-Enter",
    },
    exec: (editor: Ace.Editor) => verifyGobra(editor.getSession().getValue()),
  });


  if (language === "go") {
    language = "golang";
  }
  session.setMode(`ace/mode/${language}`);
  // Make the editor theme consistent with the mdbook-theme
  let theme = localStorage.getItem("mdbook-theme") || "light";
  let ace_theme = "ace/theme/dawn";
  if (theme == "coal" || theme == "navy") {
    ace_theme = "ace/theme/tomorrow_night";
  } else if (theme == "ayu") {
    ace_theme = "ace/theme/tomorrow_night";
  } else {
    ace_theme = "ace/theme/dawn";
  }
  editor.setTheme(ace_theme);
  // Update the context mapping
  window.gobraBookEditorContext.set(uuid, {
    editor,
    originalCode: fullCode,
    hiddenCode,
    language,
    readonly,
  });

  // Add buttons
  const pre_block = code_block.parentNode!;
  const buttons = document.createElement("div");
  buttons.className = "buttons";
  pre_block.insertBefore(buttons, pre_block.firstChild);

  buttons.appendChild(clipboardButton(uuid))
  if (readonly) {
    buttons.appendChild(hiddenLinesToggler(uuid))
  } else {
    buttons.appendChild(runButton(uuid))
    buttons.appendChild(verifyButton(uuid))
    buttons.appendChild(resetButton(uuid))
  }
}

function initializeCodeBlocks() {
  if (typeof ace === "undefined" || !ace) {
    console.warn("Ace editor is not avaible!")
    return;
  }

  let code_nodes: HTMLElement[] = Array.from(document.querySelectorAll("code")).filter(
    (n) => n.parentElement !== null && n.parentElement.tagName == "PRE",
  );

  code_nodes.forEach(initBlock)
}

addEventListener("DOMContentLoaded", () => {
  initializeCodeBlocks();
});


// Showcases the use of Marker and Range,
// in the following form this wont be a useful functionality
// Toggle the display of Gobra annotations within Go files
// Handle line comments starting with //@
// and inline comments of the form /*@ ... @*/
function specsToggler() {
  var hidden = false;
  var markers: number[] = [];
  return (editor: Ace.Editor) => {
    console.log("Toggling specs display");
    var session = editor.getSession();
    hidden = !hidden;
    markers.forEach((marker) => editor.getSession().removeMarker(marker));
    markers = [];
    if (!hidden) {
      return;
    }
    var doc = session.getDocument();
    var lines = doc.getAllLines();
    lines.forEach((line: string, line_number: number) => {
      let match = line.match(GOBRA_COMMENT);
      if (match) {
        console.debug("Found gobra line: ", line);
        markers.push(
          session.addMarker(
            new AceRange(line_number, match.index, line_number, line.length + 1),
            "errorHighlight",
            "fullLine",
          ),
        );
      }
      let matches = line.match(GOBRA_INLINE);
      if (matches) {
        matches.forEach((match) => {
          let start = line.indexOf(match);
          let end = start + match.length;
          console.debug(
            "Found gobra annotation: ",
            match,
            line_number,
            start,
            end,
          );
          markers.push(
            session.addMarker(
              new AceRange(line_number, start, line_number, end),
              "errorHighlight",
              "text",
            ),
          );
        });
      }
    });
  };
}
