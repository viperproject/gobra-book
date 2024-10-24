"use strict";
window.editors = [];

var language_default = "gobra";

function language_of(block) {
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

(function (editors) {
  if (typeof ace === "undefined" || !ace) {
    return;
  }

  let code_nodes = Array.from(document.querySelectorAll("code")).filter(
    (n) => n.parentElement.tagName == "PRE",
  );

  code_nodes.forEach(function (code_block) {
    let language = language_of(code_block);
    let readonly = code_block.classList.contains("noedit");

    let editor = ace.edit(code_block);
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

    if (language === "go") {
      language = "golang";
    }
    editor.getSession().setMode(`ace/mode/${language}`);

    editor.originalCode = editor.getValue();
    editor.commands.addCommand({
      name: "toggleCommentedLines",
      bindKey: { win: "Ctrl-L", mac: "Cmd-L" },
      exec: toggleCommentedLines,
    });

    editors.push(editor);
  });
})(window.editors);

var GOBRA_INLINE = /\/\*@.*@\*\//g;
var GOBRA_COMMENT = "//@";
// Toggle the display of Gobra annotations within Go files
// Handle line comments starting with //@
// and inline comments of the form /*@ ... @*/
function toggleCommentedLines(editor) {
  console.log("Toggling hidden lines");
  var Range = ace.require("ace/range").Range;
  var hidden = false;
  var session = editor.getSession();
  // session.clearDecorations();
  hidden = !hidden;
  if (!hidden) {
    return;
  }
  var doc = session.getDocument();
  var lines = doc.getAllLines();
  // TODO should remove the markers again editor.getSession().removeMarker(erroneousLine);
  lines.forEach((line, line_number) => {
    if (line.trim().startsWith(GOBRA_COMMENT)) {
      console.debug("Found gobra line: ", line);
      session.addGutterDecoration(line_number, "hide-line");
      session.addMarker(
        new Range(line_number, 0, line_number, line.length),
        "ace_hidden_line",
        "text",
      );
    }
    Array(...line.matchAll(GOBRA_INLINE)).forEach(([match, start, _]) => {
      console.debug("Found gobra annotation: ", match);
      let end = start + match.length;
      session.addMarker(
        new Range(line_number, start, line_number, end),
        "hidden-inline",
        "errorHighlight",
      );
    });
  });
}
