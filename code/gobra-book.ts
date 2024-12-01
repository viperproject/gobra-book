"use strict";


import type { Range } from "ace-builds";
import type { Ace } from "ace-builds";

const AceRange = ace.require("ace/range").Range;

window.gobraBookEditorContext = new Map<string, Context>();

var language_default = "gobra";
var GOBRA_INLINE = /\/\*@.*@\*\//g;
var GOBRA_COMMENT = "//@";


function language_of(block: HTMLElement) {
  let languages = Array.from(block.classList)
    .filter((cls) => cls.startsWith("language-"))
    .map((cls) => cls.replace("language-", ""));
  if (languages.length == 0) {
    console.warn(
      "no language detected for code block. using default " + language_default,
    );
    return language_default;
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
      t.title = title
      t.setAttribute("aria-label", title);
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

function initializeCodeBlocks() {
  if (typeof ace === "undefined" || !ace) {
    return;
  }

  let code_nodes: HTMLElement[] = Array.from(document.querySelectorAll("code")).filter(
    (n) => n.parentElement !== null && n.parentElement.tagName == "PRE",
  );

  code_nodes.forEach(function (code_block) {
    let uuid = crypto.randomUUID();
    code_block.id = uuid;

    let language = language_of(code_block);
    let readonly = !code_block.classList.contains("editable");

    let editor = ace.edit(code_block);
    let session = editor.getSession();
    let display_line_numbers = window.playground_line_numbers || false;



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
    const [fullCode, hiddenCode] =
      preprocessHidden(session.getValue())
    if (readonly) {
      session.setValue(hiddenCode);
    }

    editor.commands.addCommand({
      name: "highlightSpecs",
      bindKey: { win: "Ctrl-L", mac: "Cmd-L" },
      exec: specsToggler(),
    });

    if (language === "go") {
      language = "golang";
    }
    session.setMode(`ace/mode/${language}`);
    // TODO this should not be done here
    editor.setTheme("ace/theme/tomorrow_night");

    window.gobraBookEditorContext.set(uuid, {
      editor,
      originalCode: fullCode,
      hiddenCode,
      language,
      readonly,
    });

    // Button Container
    const pre_block = code_block.parentNode!;
    const buttons = document.createElement("div");
    buttons.className = "buttons";
    pre_block.insertBefore(buttons, pre_block.firstChild);

    buttons.appendChild(hiddenLinesToggler(uuid))

  });

}

initializeCodeBlocks();




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
    // TODO should remove the markers again editor.getSession().removeMarker(erroneousLine);
    lines.forEach((line: string, line_number: number) => {
      let match = line.match(GOBRA_COMMENT);
      if (match) {
        console.debug("Found gobra line: ", line);
        // session.addGutterDecoration(line_number, "hide-line");
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
