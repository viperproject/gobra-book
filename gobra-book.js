"use strict";
const AceRange = ace.require("ace/range").Range;
window.gobraBookEditorContext = new Map();

// Configuration
const GOBRA_PLAYGROUND = new URL("https://gobra.void.gschall.ch/verify");
const GO_PLAYGROUND = new URL("https://gobra.void.gschall.ch/run");
// based on theme/book.js from mdbook
// extracted and refactored elements
// Added functionality to support Go and Gobra
const DEFAULT_LANGUAGE = "text";

function fetch_with_timeout(url, options, timeout = 20000) {
  return Promise.race([
    fetch(url, options),
    new Promise((_, reject) =>
      setTimeout(() => reject(new Error("timeout")), timeout),
    ),
  ]);
}
function verifyGobra(code) {
  return fetch_with_timeout(GOBRA_PLAYGROUND, {
    headers: {
      Accept: "application/json, text/javascript, */*; q=0.01",
      "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    },
    body: new URLSearchParams({ body: code }),
    method: "POST",
  });
}
function runGo(code) {
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
  });
}
function language_of(block) {
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
function preprocessHidden(code) {
  let hiddenCode = code
    .split("\n")
    .filter((line) => !/^\s*~/.test(line))
    .join("\n");
  let fullCode = code.replaceAll("~", "");
  return [hiddenCode.trimRight(), fullCode.trimRight()];
}
function simpleButton(class1, title, callback, id) {
  const button = document.createElement("button");
  button.className = "fa " + class1;
  button.title = title;
  button.setAttribute("aria-label", title);
  button.addEventListener("click", () => {
    callback(window.gobraBookEditorContext.get(id));
  });
  return button;
}
function toggleButton(class1, class2, title, callback1, callback2, id) {
  const button = document.createElement("button");
  button.className = "fa " + class1;
  button.title = title;
  button.setAttribute("aria-label", title);
  function toggler() {
    let toggled = true;
    return function (e) {
      const t = e.target;
      if (toggled) {
        t.classList.replace(class1, class2);
        callback1(window.gobraBookEditorContext.get(id));
      } else {
        t.classList.replace(class2, class1);
        callback2(window.gobraBookEditorContext.get(id));
      }
      toggled = !toggled;
    };
  }
  button.addEventListener("click", toggler());
  return button;
}
const hiddenLinesToggler = (id) =>
  toggleButton(
    "fa-eye",
    "fa-eye-slash",
    "Show hidden lines",
    (ctxt) => {
      let session = ctxt.editor.getSession();
      session.setValue(ctxt.originalCode);
    },
    (ctxt) => {
      let session = ctxt.editor.getSession();
      session.setValue(ctxt.hiddenCode);
    },
    id,
  );
const clipboardButton = (id) =>
  simpleButton(
    "fa-copy",
    "Copy to clipboard",
    (ctxt) => {
      const code = ctxt.editor.getSession().getValue();
      navigator.clipboard.writeText(code);
    },
    id,
  );
const resetButton = (id) =>
  simpleButton(
    "fa-history",
    "Reset to initial example",
    (ctxt) => {
      const code = ctxt.originalCode;
      ctxt.editor.getSession().setValue(code);
    },
    id,
  );
const runButton = (id) =>
  simpleButton(
    "fa-play",
    "Run this Go code",
    (ctxt) => {
      const code = ctxt.editor.getSession().getValue();
      const container = ctxt.editor.container.parentNode;
      let result_block = container.querySelector(".result");
      if (!result_block) {
        result_block = document.createElement("code");
        result_block.className = "result hljs language-bash";
        container.append(result_block);
      }
      result_block.innerText = "Running...";
      runGo(code)
        .then((response) => response.json())
        .then((response) => {
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
    id,
  );
const verifyButton = (id) =>
  simpleButton(
    "fa-check-circle-o",
    "Verify with Gobra",
    (ctxt) => {
      const session = ctxt.editor.getSession();
      const code = session.getValue();
      const container = ctxt.editor.container.parentNode;
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
              .map((err) => {
                const line = err.Position.line - 1;
                const char = err.Position.char - 1;
                const codeLines = code.split("\n");
                if (0 <= line && line < codeLines.length) {
                  const lineLen = codeLines[line].length + 1;
                  // also clear it again...
                  session.addMarker(
                    new AceRange(line, char, line, lineLen),
                    "errorHighlight",
                    "singleLine",
                  );
                  let position = `${err.Position.line},${err.Position.char}`;
                  return `<p>ERROR (${position}): ${err.message}</p>`;
                }
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
    id,
  );
function initBlock(code_block) {
  let uuid = crypto.randomUUID();
  code_block.id = uuid;
  let language = language_of(code_block);
  let noEdit = !code_block.classList.contains("editable");
  // supported languages
  if (language != "go" && language != "gobra") {
    code_block.classList.add("hljs");
    code_block.classList.add("language-" + language);
    return;
  }
  let editor = ace.edit(code_block);
  let session = editor.getSession();
  session.on("change", function () {
    // clear error highlights
    session.clearAnnotations();
    Object.keys(session.getMarkers()).forEach((markerId) =>
      session.removeMarker(markerId),
    );
  });
  const showLines = window.playground_line_numbers || !noEdit;
  // Configure the editor
  editor.setOptions({
    readOnly: noEdit,
    highlightGutterLine: false,
    showPrintMargin: false,
    showLineNumbers: showLines,
    showGutter: showLines,
    maxLines: Infinity,
    fontSize: "0.875em", // please adjust the font size of the code in general.css
  });
  if (noEdit) {
    editor.renderer.$cursorLayer.element.style.opacity = 0;
  }
  editor.$blockScrolling = Infinity;
  // Preprocess the source code
  const [fullCode, hiddenCode] = preprocessHidden(session.getValue());
  if (noEdit) {
    session.setValue(hiddenCode);
  }
  // Bind Commands to keybindings
  editor.commands.addCommand({
    name: "runGo",
    bindKey: {
      win: "Ctrl-Shift-Enter",
      mac: "Ctrl-Shift-Enter",
    },
    exec: (editor) => runGo(editor.getSession().getValue()),
  });
  editor.commands.addCommand({
    name: "verifyGobra",
    bindKey: {
      win: "Ctrl-Enter",
      mac: "Ctrl-Enter",
    },
    exec: (editor) => verifyGobra(editor.getSession().getValue()),
  });
  // the ace editor mode uses golang instead of go
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
    readonly: noEdit,
  });
  // Add buttons
  const pre_block = code_block.parentNode;
  const buttons = document.createElement("div");
  buttons.className = "buttons";
  pre_block.insertBefore(buttons, pre_block.firstChild);
  buttons.appendChild(clipboardButton(uuid));
  if (noEdit) {
    if (fullCode != hiddenCode) {
      buttons.appendChild(hiddenLinesToggler(uuid));
    }
  } else {
    buttons.appendChild(runButton(uuid));
    buttons.appendChild(verifyButton(uuid));
    buttons.appendChild(resetButton(uuid));
  }
}
function initializeCodeBlocks() {
  if (typeof ace === "undefined" || !ace) {
    console.warn("Ace editor is not avaible!");
    return;
  }
  let code_nodes = Array.from(document.querySelectorAll("code")).filter(
    (n) => n.parentElement !== null && n.parentElement.tagName == "PRE",
  );
  code_nodes.forEach(initBlock);
}
addEventListener("DOMContentLoaded", () => {
  initializeCodeBlocks();
});


// original source of ferris.js
// https://github.com/cognitive-engineering-lab/rust-book/blob/main/ferris.js
// MIT license https://opensource.org/licenses/MIT

// @ts-check
/**
 * @typedef {{ attr: string, title: string }} FerrisType
 */

/** @type {Array<FerrisType>} */
const FERRIS_TYPES = [
  {
    attr: "does_not_compile",
    title: "This Go code does not compile!",
  },
  {
    attr: "does_not_verify",
    title: "Gobra does not verify this code!",
  },
  {
    attr: "not_efficient",
    title: "Gobra does not verify this code in reasonable time!",
  },
  {
    attr: "panics",
    title: "This code panics!",
  },
  {
    attr: "verifies",
    title: "Gobra verifies this code.",
  },
];

document.addEventListener("DOMContentLoaded", () => {
  for (let ferrisType of FERRIS_TYPES) {
    attachFerrises(ferrisType);
  }
});

/**
 * @param {FerrisType} type
 */
function attachFerrises(type) {
  let elements = document.getElementsByClassName(type.attr);

  for (let codeBlock of elements) {
    // Skip SVG etc.: in principle, these should never be attached to those, but
    // this means if someone happens to have a browser extension which *is*
    // attaching them, it will not break the code.
    if (!(codeBlock instanceof HTMLElement)) {
      continue;
    }

    let lines = codeBlock.innerText.replace(/\n$/, "").split(/\n/).length;

    /** @type {'small' | 'large'} */
    let size = lines < 10 ? "small" : "large";

    let container = prepareFerrisContainer(codeBlock, size == "small");
    if (!container) {
      continue;
    }

    container.appendChild(createFerris(type, size));
  }
}

/**
 * @param {HTMLElement} element - Code block element to attach a Ferris to.
 * @param {boolean} useButtons - Whether to attach to existing buttons.
 * @returns {Element | null} - The container element to use.
 */
function prepareFerrisContainer(element, useButtons) {
  let foundButtons = element.parentElement?.querySelector(".buttons");
  if (useButtons && foundButtons) {
    return foundButtons;
  }

  let div = document.createElement("div");
  div.classList.add("ferris-container");

  if (!element.parentElement) {
    console.error(
      `Could not install Ferris on ${element}, which is missing a parent`,
    );
    return null;
  }

  element.parentElement.insertBefore(div, element);

  return div;
}

/**
 * @param {FerrisType} type
 * @param {'small' | 'large'} size
 * @returns {HTMLAnchorElement} - The generated anchor element.
 */
function createFerris(type, size) {
  let a = document.createElement("a");
  // TODO add a similar page where we explain the meaning?
  // a.setAttribute("href", "ch00-00-introduction.html#ferris");
  a.setAttribute("target", "_blank");

  let img = document.createElement("img");
  img.setAttribute(
    "src",
    window.path_to_root + "assets/ferris/" + type.attr + ".svg",
  );
  img.setAttribute("title", type.title);
  img.classList.add("ferris");
  img.classList.add("ferris-" + size);

  a.appendChild(img);

  return a;
}

export {};
