"use strict";
window.editors = [];

var language_default = "gobra";
var Range = ace.require("ace/range").Range;

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
      exec: specsToggler(),
    });

    editors.push(editor);
  });
})(window.editors);

var GOBRA_INLINE = /\/\*@.*@\*\//g;
var GOBRA_COMMENT = "//@";
// Toggle the display of Gobra annotations within Go files
// Handle line comments starting with //@
// and inline comments of the form /*@ ... @*/
function specsToggler() {
  var hidden = false;
  var markers = [];
  return (editor) => {
    console.log("Toggling hidden lines");
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
    lines.forEach((line, line_number) => {
      let match = line.match(GOBRA_COMMENT);
      if (match) {
        console.debug("Found gobra line: ", line);
        // session.addGutterDecoration(line_number, "hide-line");
        markers.push(
          session.addMarker(
            new Range(line_number, match.index, line_number, line.length + 1),
            "errorHighlight",
            "background",
          ),
        );
      }
      Array(...line.matchAll(GOBRA_INLINE)).forEach((match) => {
        let start = match.index;
        let end = start + match[0].length;
        console.debug(
          "Found gobra annotation: ",
          match[0],
          line_number,
          start,
          end,
        );
        markers.push(
          session.addMarker(
            new Range(line_number, start, line_number, end),
            "errorHighlight",
            "background",
          ),
        );
      });
    });
  };
}
