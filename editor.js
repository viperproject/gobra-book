"use strict";
window.editors = [];
(function(editors) {
    if (typeof(ace) === 'undefined' || !ace) {
        return;
    }

    let code_nodes = Array
        .from(document.querySelectorAll('code'))
        .filter(n => n.parentElement.tagName == "PRE")

    code_nodes.forEach(function(code_block) {

        // Extract the language of the code block from the class name
        let language = "gobra"
        let editable = code_block.classList.contains("editable")
        for (const cls of new Array(...code_block.classList)) {
            if (cls.startsWith("language-"))  {
                language = cls.replace("language-", "")
            }
        }
        if (language === "go") {
            language = "golang"
        }

        let hide = code_block.classList.contains("hide-boring")
        if (hide) {
            code_block.classList.add('hljs')
            // code_block.classList.remove('language-gobra')
            // code_block.classList.remove('language-go')
            // hljs.highlightBlock(code_block)
            return
        }

        let editor = ace.edit(code_block);
        let display_line_numbers = window.playground_line_numbers || false;

        editor.setOptions({
            readOnly: editable,
            highlightActiveLine: editable,
            highlightGutterLine: editable,
            showPrintMargin: false,
            showLineNumbers: display_line_numbers,
            showGutter: display_line_numbers,
            maxLines: Infinity,
            fontSize: "0.875em" // please adjust the font size of the code in general.css
        });
        if (editable) {
            editor.renderer.$cursorLayer.element.style.opacity=0
        }

        editor.$blockScrolling = Infinity;

        editor.getSession().setMode(`ace/mode/${language}`);

        editor.originalCode = editor.getValue();

        editors.push(editor);
    });
})(window.editors);
