"use strict";


import type { Range } from "ace-builds";
import type { Ace } from "ace-builds";

const AceRange = ace.require("ace/range").Range;

window.gobraBookEditorContext = new Map<string, Context>();

var language_default = "gobra";
var GOBRA_INLINE = /\/\*@.*@\*\//g;
var GOBRA_COMMENT = "//@";


function language_of(block: HTMLElement) {
  let languages = Array(...block.classList)
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

    if (readonly) {
      let code = session.getValue();
      let hiddenCode = code
        .split("\n")
        .filter((line: string) => !/^\s*~/.test(line))
        .join("\n");
      let fullCode = code.replaceAll("~", "");
      session.setValue(hiddenCode);
      let hidden = true;
      editor.commands.addCommand({
        name: "toggleCommentedLines",
        bindKey: { win: "Ctrl-L", mac: "Cmd-L" },
        exec: () => {
          console.log("Toggling hidden lines");
          if (hidden) {
            session.setValue(fullCode);
          } else {
            session.setValue(hiddenCode);
          }
          hidden = !hidden;
        },
      }); AceRange
    } else {
      editor.commands.addCommand({
        name: "toggleCommentedLines",
        bindKey: { win: "Ctrl-L", mac: "Cmd-L" },
        exec: specsToggler(),
      });
    }

    if (language === "go") {
      language = "golang";
    }
    session.setMode(`ace/mode/${language}`);
    // TODO this should not be done here
    editor.setTheme("ace/theme/tomorrow_night");
    editor.originalCode = session.getValue();

    window.gobraBookEditorContext.set(uuid, {
      editor,
      language: language_of(code_block),
      readonly: readonly,
    });
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
