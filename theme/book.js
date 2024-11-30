"use strict";

// Fix back button cache problem
window.onunload = function () {};

(function codeSnippets() {
  function fetch_with_timeout(url, options, timeout = 20000) {
    return Promise.race([
      fetch(url, options),
      new Promise((_, reject) =>
        setTimeout(() => reject(new Error("timeout")), timeout),
      ),
    ]);
  }

  function verify_gobra_code(code_block) {
    let result_block = code_block.querySelector(".result");
    if (!result_block) {
      result_block = document.createElement("code");
      result_block.className = "result hljs language-bash";
      code_block.append(result_block);
    }
    result_block.innerText = "Verifying...";

    fetch_with_timeout("https://gobra.void.gschall.ch/verify", {
      headers: {
        Accept: "application/json, text/javascript, */*; q=0.01",
        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
      },
      body: new URLSearchParams({ body: playground_text(code_block) }),
      method: "POST",
    })
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
            .map((err, i) => {
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
  }

  function run_go_code(code_block) {
    let result_block = code_block.querySelector(".result");
    if (!result_block) {
      result_block = document.createElement("code");
      result_block.className = "result hljs language-bash";
      code_block.append(result_block);
    }
    result_block.innerText = "Running...";

    fetch_with_timeout("https://gobra.void.gschall.ch/run", {
      headers: {
        Accept: "application/json, text/javascript, */*; q=0.01",
        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
      },
      body: new URLSearchParams({
        version: 2,
        body: playground_text(code_block),
        withVet: true,
      }),
      method: "POST",
    })
      .then((response) => response.json())
      .then((response) => {
        // {"Errors":"","Events":[{"Message":"Hello, 世界\n","Kind":"stdout","Delay":0}],"Status":0,"IsTest":false,"TestsFailed":0,"VetOK":true}
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
  }

  hljs.registerLanguage("gobra", function (hljs) {
    var gobra_keywords =
      "invariant|requires|ensures|preserves|trusted|share|opaque|reveal|outline|pred|pure|exists|assume|apply|inhale|exhale|assert|ghost|implements|unfolding|let|fold|unfold|decreases";
    var GO_KEYWORDS = {
      keyword:
        "package import func var const type struct interface map chan go defer return break continue for range if else switch case default select fallthrough " +
        gobra_keywords.split("|").join(" "),
      literal: "true false iota nil",
      built_in:
        "append cap close complex copy delete imag len make new panic print println real recover",
    };

    // Extend the Go language rules
    return {
      name: "Gobra",
      aliases: ["gobra"],
      keywords: GO_KEYWORDS,
      contains: [
        // Special line comment: //@
        {
          className: "comment",
          begin: "//@", // Start with //@
          end: "$", // End of the line
        },

        // Special inline comment: /*@ ... @*/
        {
          className: "comment",
          begin: "/\\*@", // Start with /*@
          end: "@\\*/", // End with @*/
        },
        {
          className: "string",
          begin: '"',
          end: '"',
          illegal: "\\n",
          contains: [hljs.BACKSLASH_ESCAPE],
        },
        {
          className: "number",
          begin: hljs.C_NUMBER_RE,
          relevance: 0,
        },
        {
          className: "operator",
          begin: /:=|\+\+|--|&&|\|\||<-|=>|<==>|<==|::|in|===|!==/,
        },
        hljs.HASH_COMMENT_MODE, // Example for an additional comment style if needed
        hljs.C_LINE_COMMENT_MODE,
        hljs.C_BLOCK_COMMENT_MODE,
      ],
    };
  });

  // Syntax highlighting Configuration
  // hljs.configure({
  //   tabReplace: "    ", // 4 spaces
  //   languages: [], // Languages used for auto-detection
  // });

  // Don't highlight `inline code` blocks in headers.
  let code_nodes = Array.from(document.querySelectorAll("code")).filter(
    (n) => n.parentElement.tagName == "PRE",
  );

  // code_nodes.forEach((node) => {
  //   if (window.ace && node.classList.contains("editable")) {
  //     // language-rust class needs to be removed for editable
  //     // blocks or highlightjs will capture events
  //     node.classList.remove("language-rust");
  //     node.classList.remove("language-gobra");
  //     node.classList.remove("language-go");
  //   } else {
  //     hljs.highlightBlock(node);
  //   }
  // });

  // code_nodes.forEach((block) => {
  //   // Adding the hljs class gives code blocks the color css
  //   // even if highlighting doesn't apply
  //   // block.classList.add("hljs");
  // });

  code_nodes.forEach((block) => {
    const pre_block = block.parentNode;
    const buttons = document.createElement("div");
    buttons.className = "buttons";
    pre_block.insertBefore(buttons, pre_block.firstChild);

    addButtonHidden(block, buttons);
    addButtonClipboard(block, buttons);
    addButtonRun(block, buttons);
    addButtonVerify(block, buttons);
    addButtonUndo(block, buttons);
  });

  function addButtonHidden(block, buttons) {
    const button = document.createElement("button");
    button.className = "fa fa-eye";
    button.title = "Show hidden lines";
    button.setAttribute("aria-label", button.title);

    buttons.insertBefore(button, buttons.firstChild);
    var editor = ace.edit(block);
    function toggler() {
      let hidden = true;
      return function (e) {
        const t = e.target;

        let temp = editor.getReadOnly();
        editor.setReadOnly(false);
        editor.commands.exec("toggleCommentedLines", editor);
        editor.setReadOnly(temp);

        t.setAttribute("aria-label", t.title);
        if (hidden) {
          t.classList.replace("fa-eye", "fa-eye-slash");
          block.classList.remove("hide-boring");
        } else {
          t.classList.replace("fa-eye-slash", "fa-eye");
          block.classList.add("hide-boring");
        }
        hidden = !hidden;
      };
    }
    button.addEventListener("click", toggler());
  }

  function addButtonClipboard(block, buttons) {
    if (!window.playground_copyable) {
      return;
    }
    const button = document.createElement("button");
    button.className = "fa fa-copy clip-button";
    button.title = "Copy to clipboard";
    button.setAttribute("aria-label", button.title);
    button.innerHTML = '<i class="tooltiptext"></i>';

    buttons.insertBefore(button, buttons.firstChild);
  }

  function addButtonRun(block, buttons) {
    if (block.classList.contains("no_run")) {
      return;
    }
    if (block.classList.contains("language-gobra")) {
      return;
    }
    const button = document.createElement("button");
    button.className = "fa fa-play play-button";
    button.title = "Run this code";
    button.setAttribute("aria-label", button.title);
    button.addEventListener("click", (e) => run_go_code(buttons.parentNode));

    buttons.insertBefore(button, buttons.firstChild);

    if (block.classList.contains("editable")) {
      let editor = window.ace.edit(block);
      editor.commands.addCommand({
        name: "run",
        bindKey: {
          win: "Ctrl-Enter",
          mac: "Ctrl-Enter",
        },
        exec: (_editor) => run_go_code(block),
      });
    }
  }

  function addButtonVerify(block, buttons) {
    if (block.classList.contains("no_run")) {
      return;
    }
    const button = document.createElement("button");
    button.className = "fa fa-check-circle-o verify-button";
    button.title = "Verify this code";
    button.setAttribute("aria-label", button.title);
    button.addEventListener("click", (e) =>
      verify_gobra_code(buttons.parentNode),
    );

    buttons.insertBefore(button, buttons.firstChild);

    if (block.classList.contains("editable")) {
      let editor = window.ace.edit(block);
      // editor.commands.addCommand({
      //         name: "run",
      //         bindKey: {
      //             win: "Ctrl-Enter",
      //             mac: "Ctrl-Enter"
      //         },
      //         exec: _editor => run_go_code(block)
      // });
    }
  }

  function addButtonUndo(block, buttons) {
    if (!window.ace || !block.classList.contains("editable")) {
      return;
    }
    const button = document.createElement("button");
    button.className = "fa fa-history reset-button";
    button.title = "Undo changes";
    button.setAttribute("aria-label", button.title);
    buttons.insertBefore(button, buttons.firstChild);

    button.addEventListener("click", () => {
      let editor = window.ace.edit(block);
      editor.setValue(editor.originalCode);
      editor.clearSelection();
    });
  }
})();

// Global variable, shared between modules
function playground_text(playground, hidden = true) {
  let code_block = playground.querySelector("code");
  if (window.ace) {
    let editor = window.ace.edit(code_block);
    return editor.getValue();
  } else if (hidden) {
    return code_block.textContent;
  } else {
    return code_block.innerText;
  }
}

(function themes() {
  var html = document.querySelector("html");
  var themeToggleButton = document.getElementById("theme-toggle");
  var themePopup = document.getElementById("theme-list");
  var themeColorMetaTag = document.querySelector('meta[name="theme-color"]');
  var stylesheets = {
    ayuHighlight: document.querySelector("[href$='ayu-highlight.css']"),
    tomorrowNight: document.querySelector("[href$='tomorrow-night.css']"),
    highlight: document.querySelector("[href$='highlight.css']"),
  };

  function showThemes() {
    themePopup.style.display = "block";
    themeToggleButton.setAttribute("aria-expanded", true);
    themePopup.querySelector("button#" + get_theme()).focus();
  }

  function updateThemeSelected() {
    themePopup.querySelectorAll(".theme-selected").forEach(function (el) {
      el.classList.remove("theme-selected");
    });
    themePopup
      .querySelector("button#" + get_theme())
      .classList.add("theme-selected");
  }

  function hideThemes() {
    themePopup.style.display = "none";
    themeToggleButton.setAttribute("aria-expanded", false);
    themeToggleButton.focus();
  }

  function get_theme() {
    var theme;
    try {
      theme = localStorage.getItem("mdbook-theme");
    } catch (e) {}
    if (theme === null || theme === undefined) {
      return default_theme;
    } else {
      return theme;
    }
  }

  function set_theme(theme, store = true) {
    let ace_theme;

    if (theme == "coal" || theme == "navy") {
      stylesheets.ayuHighlight.disabled = true;
      stylesheets.tomorrowNight.disabled = false;
      stylesheets.highlight.disabled = true;

      ace_theme = "ace/theme/tomorrow_night";
    } else if (theme == "ayu") {
      stylesheets.ayuHighlight.disabled = false;
      stylesheets.tomorrowNight.disabled = true;
      stylesheets.highlight.disabled = true;
      ace_theme = "ace/theme/tomorrow_night";
    } else {
      stylesheets.ayuHighlight.disabled = true;
      stylesheets.tomorrowNight.disabled = true;
      stylesheets.highlight.disabled = false;
      ace_theme = "ace/theme/dawn";
    }

    setTimeout(function () {
      themeColorMetaTag.content = getComputedStyle(
        document.documentElement,
      ).backgroundColor;
    }, 1);

    if (window.ace && window.editors) {
      window.editors.forEach(function (editor) {
        editor.setTheme(ace_theme);
      });
    }

    var previousTheme = get_theme();

    if (store) {
      try {
        localStorage.setItem("mdbook-theme", theme);
      } catch (e) {}
    }

    html.classList.remove(previousTheme);
    html.classList.add(theme);
    updateThemeSelected();
  }

  // Set theme
  var theme = get_theme();

  set_theme(theme, false);

  themeToggleButton.addEventListener("click", function () {
    if (themePopup.style.display === "block") {
      hideThemes();
    } else {
      showThemes();
    }
  });

  themePopup.addEventListener("click", function (e) {
    var theme;
    if (e.target.className === "theme") {
      theme = e.target.id;
    } else if (e.target.parentElement.className === "theme") {
      theme = e.target.parentElement.id;
    } else {
      return;
    }
    set_theme(theme);
  });

  themePopup.addEventListener("focusout", function (e) {
    // e.relatedTarget is null in Safari and Firefox on macOS (see workaround below)
    if (
      !!e.relatedTarget &&
      !themeToggleButton.contains(e.relatedTarget) &&
      !themePopup.contains(e.relatedTarget)
    ) {
      hideThemes();
    }
  });

  // Should not be needed, but it works around an issue on macOS & iOS: https://github.com/rust-lang/mdBook/issues/628
  document.addEventListener("click", function (e) {
    if (
      themePopup.style.display === "block" &&
      !themeToggleButton.contains(e.target) &&
      !themePopup.contains(e.target)
    ) {
      hideThemes();
    }
  });

  document.addEventListener("keydown", function (e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) {
      return;
    }
    if (!themePopup.contains(e.target)) {
      return;
    }

    switch (e.key) {
      case "Escape":
        e.preventDefault();
        hideThemes();
        break;
      case "ArrowUp":
        e.preventDefault();
        var li = document.activeElement.parentElement;
        if (li && li.previousElementSibling) {
          li.previousElementSibling.querySelector("button").focus();
        }
        break;
      case "ArrowDown":
        e.preventDefault();
        var li = document.activeElement.parentElement;
        if (li && li.nextElementSibling) {
          li.nextElementSibling.querySelector("button").focus();
        }
        break;
      case "Home":
        e.preventDefault();
        themePopup.querySelector("li:first-child button").focus();
        break;
      case "End":
        e.preventDefault();
        themePopup.querySelector("li:last-child button").focus();
        break;
    }
  });
})();

(function sidebar() {
  var body = document.querySelector("body");
  var sidebar = document.getElementById("sidebar");
  var sidebarLinks = document.querySelectorAll("#sidebar a");
  var sidebarToggleButton = document.getElementById("sidebar-toggle");
  var sidebarResizeHandle = document.getElementById("sidebar-resize-handle");
  var firstContact = null;

  function showSidebar() {
    body.classList.remove("sidebar-hidden");
    body.classList.add("sidebar-visible");
    Array.from(sidebarLinks).forEach(function (link) {
      link.setAttribute("tabIndex", 0);
    });
    sidebarToggleButton.setAttribute("aria-expanded", true);
    sidebar.setAttribute("aria-hidden", false);
    try {
      localStorage.setItem("mdbook-sidebar", "visible");
    } catch (e) {}
  }

  var sidebarAnchorToggles = document.querySelectorAll("#sidebar a.toggle");

  function toggleSection(ev) {
    ev.currentTarget.parentElement.classList.toggle("expanded");
  }

  Array.from(sidebarAnchorToggles).forEach(function (el) {
    el.addEventListener("click", toggleSection);
  });

  function hideSidebar() {
    body.classList.remove("sidebar-visible");
    body.classList.add("sidebar-hidden");
    Array.from(sidebarLinks).forEach(function (link) {
      link.setAttribute("tabIndex", -1);
    });
    sidebarToggleButton.setAttribute("aria-expanded", false);
    sidebar.setAttribute("aria-hidden", true);
    try {
      localStorage.setItem("mdbook-sidebar", "hidden");
    } catch (e) {}
  }

  // Toggle sidebar
  sidebarToggleButton.addEventListener("click", function sidebarToggle() {
    if (body.classList.contains("sidebar-hidden")) {
      var current_width = parseInt(
        document.documentElement.style.getPropertyValue("--sidebar-width"),
        10,
      );
      if (current_width < 150) {
        document.documentElement.style.setProperty("--sidebar-width", "150px");
      }
      showSidebar();
    } else if (body.classList.contains("sidebar-visible")) {
      hideSidebar();
    } else {
      if (getComputedStyle(sidebar)["transform"] === "none") {
        hideSidebar();
      } else {
        showSidebar();
      }
    }
  });

  sidebarResizeHandle.addEventListener("mousedown", initResize, false);

  function initResize(e) {
    window.addEventListener("mousemove", resize, false);
    window.addEventListener("mouseup", stopResize, false);
    body.classList.add("sidebar-resizing");
  }
  function resize(e) {
    var pos = e.clientX - sidebar.offsetLeft;
    if (pos < 20) {
      hideSidebar();
    } else {
      if (body.classList.contains("sidebar-hidden")) {
        showSidebar();
      }
      pos = Math.min(pos, window.innerWidth - 100);
      document.documentElement.style.setProperty("--sidebar-width", pos + "px");
    }
  }
  //on mouseup remove windows functions mousemove & mouseup
  function stopResize(e) {
    body.classList.remove("sidebar-resizing");
    window.removeEventListener("mousemove", resize, false);
    window.removeEventListener("mouseup", stopResize, false);
  }

  document.addEventListener(
    "touchstart",
    function (e) {
      firstContact = {
        x: e.touches[0].clientX,
        time: Date.now(),
      };
    },
    { passive: true },
  );

  document.addEventListener(
    "touchmove",
    function (e) {
      if (!firstContact) return;

      var curX = e.touches[0].clientX;
      var xDiff = curX - firstContact.x,
        tDiff = Date.now() - firstContact.time;

      if (tDiff < 250 && Math.abs(xDiff) >= 150) {
        if (
          xDiff >= 0 &&
          firstContact.x < Math.min(document.body.clientWidth * 0.25, 300)
        )
          showSidebar();
        else if (xDiff < 0 && curX < 300) hideSidebar();

        firstContact = null;
      }
    },
    { passive: true },
  );
})();

(function chapterNavigation() {
  document.addEventListener("keydown", function (e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) {
      return;
    }
    if (window.search && window.search.hasFocus()) {
      return;
    }
    var html = document.querySelector("html");

    function next() {
      var nextButton = document.querySelector(".nav-chapters.next");
      if (nextButton) {
        window.location.href = nextButton.href;
      }
    }
    function prev() {
      var previousButton = document.querySelector(".nav-chapters.previous");
      if (previousButton) {
        window.location.href = previousButton.href;
      }
    }
    switch (e.key) {
      case "ArrowRight":
        e.preventDefault();
        if (html.dir == "rtl") {
          prev();
        } else {
          next();
        }
        break;
      case "ArrowLeft":
        e.preventDefault();
        if (html.dir == "rtl") {
          next();
        } else {
          prev();
        }
        break;
    }
  });
})();

(function clipboard() {
  var clipButtons = document.querySelectorAll(".clip-button");

  function hideTooltip(elem) {
    elem.firstChild.innerText = "";
    elem.className = "fa fa-copy clip-button";
  }

  function showTooltip(elem, msg) {
    elem.firstChild.innerText = msg;
    elem.className = "fa fa-copy tooltipped";
  }

  var clipboardSnippets = new ClipboardJS(".clip-button", {
    text: function (trigger) {
      hideTooltip(trigger);
      let playground = trigger.closest("pre");
      return playground_text(playground, false);
    },
  });

  Array.from(clipButtons).forEach(function (clipButton) {
    clipButton.addEventListener("mouseout", function (e) {
      hideTooltip(e.currentTarget);
    });
  });

  clipboardSnippets.on("success", function (e) {
    e.clearSelection();
    showTooltip(e.trigger, "Copied!");
  });

  clipboardSnippets.on("error", function (e) {
    showTooltip(e.trigger, "Clipboard error!");
  });
})();

(function scrollToTop() {
  var menuTitle = document.querySelector(".menu-title");

  menuTitle.addEventListener("click", function () {
    document.scrollingElement.scrollTo({ top: 0, behavior: "smooth" });
  });
})();

(function controllMenu() {
  var menu = document.getElementById("menu-bar");

  (function controllPosition() {
    var scrollTop = document.scrollingElement.scrollTop;
    var prevScrollTop = scrollTop;
    var minMenuY = -menu.clientHeight - 50;
    // When the script loads, the page can be at any scroll (e.g. if you reforesh it).
    menu.style.top = scrollTop + "px";
    // Same as parseInt(menu.style.top.slice(0, -2), but faster
    var topCache = menu.style.top.slice(0, -2);
    menu.classList.remove("sticky");
    var stickyCache = false; // Same as menu.classList.contains('sticky'), but faster
    document.addEventListener(
      "scroll",
      function () {
        scrollTop = Math.max(document.scrollingElement.scrollTop, 0);
        // `null` means that it doesn't need to be updated
        var nextSticky = null;
        var nextTop = null;
        var scrollDown = scrollTop > prevScrollTop;
        var menuPosAbsoluteY = topCache - scrollTop;
        if (scrollDown) {
          nextSticky = false;
          if (menuPosAbsoluteY > 0) {
            nextTop = prevScrollTop;
          }
        } else {
          if (menuPosAbsoluteY > 0) {
            nextSticky = true;
          } else if (menuPosAbsoluteY < minMenuY) {
            nextTop = prevScrollTop + minMenuY;
          }
        }
        if (nextSticky === true && stickyCache === false) {
          menu.classList.add("sticky");
          stickyCache = true;
        } else if (nextSticky === false && stickyCache === true) {
          menu.classList.remove("sticky");
          stickyCache = false;
        }
        if (nextTop !== null) {
          menu.style.top = nextTop + "px";
          topCache = nextTop;
        }
        prevScrollTop = scrollTop;
      },
      { passive: true },
    );
  })();
  (function controllBorder() {
    function updateBorder() {
      if (menu.offsetTop === 0) {
        menu.classList.remove("bordered");
      } else {
        menu.classList.add("bordered");
      }
    }
    updateBorder();
    document.addEventListener("scroll", updateBorder, { passive: true });
  })();
})();
