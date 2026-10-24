(function () {
  "use strict";

  const state = {
    catalog: [],
    selectedSlug: "",
    book: null,
    items: [],
    selectedKey: "",
    context: null,
    reviews: new Map(),
    reviewRevision: 0,
    draft: null,
    history: null,
    session: null,
    csrf: null,
    bookSearch: "",
    itemSearch: "",
    kindFilter: "all",
    availabilityFilter: "all",
    subjectFilters: new Set(),
    itemTypeFilter: "all",
    itemSectionFilter: "all",
    reviewFilter: "all",
    reviewLimit: 80,
    evidenceView: "graph",
    evidenceReturn: null,
    mobileView: "queue",
    pollTimer: null,
    bookRequest: 0,
    contextRequest: 0,
    historyRequest: 0,
    frameHistory: {
      docs: { entries: [], index: -1, pendingReset: false, pendingAction: null },
      verso: { entries: [], index: -1, pendingReset: false, pendingAction: null },
    },
    graphScopeByBook: new Map(),
    graphDependencyByBook: new Map(),
    relationDependencyMode: "proof",
    statementSourceOpen: false,
    statementCopyTimer: null,
    catalogCollapsed: false,
    queueCollapsed: false,
    reviewCollapsed: false,
  };

  const REVIEW_STATUSES = ["unreviewed", "accepted", "mismatch", "other"];
  const SEVERITY = ["mismatch", "other", "accepted"];

  function detectBasePath() {
    const pathname = window.location.pathname || "/";
    const marker = "/books/";
    const index = pathname.indexOf(marker);
    const base = index >= 0 ? pathname.slice(0, index) : pathname === "/" ? "" : pathname;
    return base.replace(/\/+$/, "");
  }

  const BASE_PATH = detectBasePath();
  const appUrl = (path) => `${BASE_PATH}${String(path || "").startsWith("/") ? path : `/${path}`}` || "/";

  const refs = {
    appShell: document.querySelector(".app-shell"),
    workspaceMain: document.getElementById("workspaceMain"),
    catalogPanel: document.getElementById("catalogPanel"),
    evidencePanel: document.getElementById("evidencePanel"),
    reviewPanel: document.getElementById("reviewPanel"),
    skipLink: document.getElementById("skipLink"),
    mobileButtons: [...document.querySelectorAll("button[data-mobile-view]")],
    catalogList: document.getElementById("catalogList"),
    bookCount: document.getElementById("bookCount"),
    bookSearch: document.getElementById("bookSearch"),
    kindFilter: document.getElementById("kindFilter"),
    availabilityFilter: document.getElementById("availabilityFilter"),
    subjectOptions: document.getElementById("subjectOptions"),
    subjectSummary: document.getElementById("subjectSummary"),
    clearSubjectFilters: document.getElementById("clearSubjectFilters"),
    brandLink: document.getElementById("brandLink"),
    authState: document.getElementById("authState"),
    loginLink: document.getElementById("loginLink"),
    logoutButton: document.getElementById("logoutButton"),
    exportLink: document.getElementById("exportLink"),
    toggleCatalog: document.getElementById("toggleCatalog"),
    toggleQueue: document.getElementById("toggleQueue"),
    queueRailToggle: document.getElementById("queueRailToggle"),
    queuePanelToggle: document.getElementById("queuePanelToggle"),
    reviewPanelToggle: document.getElementById("reviewPanelToggle"),
    reviewRailToggle: document.getElementById("reviewRailToggle"),
    catalogPanelToggle: document.getElementById("catalogPanelToggle"),
    toggleReview: document.getElementById("toggleReview"),
    catalogResize: document.getElementById("catalogResize"),
    queueResize: document.getElementById("queueResize"),
    reviewResize: document.getElementById("reviewResize"),
    bookSync: document.getElementById("bookSync"),
    currentBookTitle: document.getElementById("currentBookTitle"),
    currentBookMeta: document.getElementById("currentBookMeta"),
    bookOverview: document.getElementById("bookOverview"),
    itemSearch: document.getElementById("itemSearch"),
    itemTypeFilter: document.getElementById("itemTypeFilter"),
    itemSectionFilter: document.getElementById("itemSectionFilter"),
    reviewFilter: document.getElementById("reviewFilter"),
    clearItemFilters: document.getElementById("clearItemFilters"),
    itemResultCount: document.getElementById("itemResultCount"),
    reviewQueue: document.getElementById("reviewQueue"),
    evidenceStats: document.getElementById("evidenceStats"),
    graphView: document.getElementById("graphView"),
    graphFrame: document.getElementById("graphFrame"),
    versoTab: document.getElementById("versoTab"),
    graphFallback: document.getElementById("graphFallback"),
    graphMessage: document.getElementById("graphMessage"),
    evidenceHistoryControls: document.getElementById("evidenceHistoryControls"),
    evidenceBack: document.getElementById("evidenceBack"),
    evidenceForward: document.getElementById("evidenceForward"),
    graphCanvas: document.getElementById("graphCanvas"),
    sourceView: document.getElementById("sourceView"),
    sourceMeta: document.getElementById("sourceMeta"),
    sourceCode: document.getElementById("sourceCode"),
    docsView: document.getElementById("docsView"),
    docsFrame: document.getElementById("docsFrame"),
    docsEmpty: document.getElementById("docsEmpty"),
    versoView: document.getElementById("versoView"),
    versoFrame: document.getElementById("versoFrame"),
    versoEmpty: document.getElementById("versoEmpty"),
    detailEmpty: document.getElementById("detailEmpty"),
    detailContent: document.getElementById("detailContent"),
    detailKind: document.getElementById("detailKind"),
    detailTitle: document.getElementById("detailTitle"),
    detailStatus: document.getElementById("detailStatus"),
    detailTags: document.getElementById("detailTags"),
    detailStatementLabel: document.getElementById("detailStatementLabel"),
    detailStatement: document.getElementById("detailStatement"),
    statementPanel: document.getElementById("statementPanel"),
    statementSourceToggle: document.getElementById("statementSourceToggle"),
    statementSourcePreview: document.getElementById("statementSourcePreview"),
    copyStatementSource: document.getElementById("copyStatementSource"),
    relationSection: document.getElementById("relationSection"),
    relationFilters: document.getElementById("relationFilters"),
    relationStats: document.getElementById("relationStats"),
    upstreamRelations: document.getElementById("upstreamRelations"),
    downstreamRelations: document.getElementById("downstreamRelations"),
    leanContract: document.getElementById("leanContract"),
    leanCode: document.getElementById("leanCode"),
    reviewerCards: document.getElementById("reviewerCards"),
    reviewControls: document.getElementById("reviewControls"),
    reviewAccessNotice: document.getElementById("reviewAccessNotice"),
    reviewComment: document.getElementById("reviewComment"),
    saveReview: document.getElementById("saveReview"),
    saveState: document.getElementById("saveState"),
    historySection: document.getElementById("historySection"),
    historyList: document.getElementById("historyList"),
  };

  const escapeHtml = (value) => String(value ?? "").replace(/[&<>"']/g, (char) => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;",
  })[char]);

  function highlightLean(value) {
    const source = String(value ?? "");
    const keywords = new Set([
      "abbrev", "axiom", "by", "class", "def", "deriving", "else", "example", "extends",
      "forall", "fun", "if", "in", "inductive", "instance", "lemma", "let", "match",
      "namespace", "opaque", "open", "private", "protected", "section", "structure", "theorem",
      "then", "universe", "variable", "where", "with", "Prop", "Sort", "Type"
    ]);
    const commands = new Set(["#check", "#eval", "#print", "#reduce", "#synth", "#guard"]);
    const symbols = /[∀∃λΠΣ→←↔↦∧∨⊢⊣:=<>+\-*/=|!?.;,()[\]{}]/;
    const ident = (char) => /[\p{L}\p{N}_'.]/u.test(char);
    const span = (className, text) => `<span class="${className}">${escapeHtml(text)}</span>`;
    let html = "";
    let index = 0;
    while (index < source.length) {
      const rest = source.slice(index);
      const char = source[index];
      if (rest.startsWith("--")) {
        const end = source.indexOf("\n", index);
        const next = end < 0 ? source.length : end;
        html += span("lean-comment", source.slice(index, next)); index = next; continue;
      }
      if (rest.startsWith("/-")) {
        let depth = 0; let cursor = index;
        while (cursor < source.length) {
          if (source.startsWith("/-", cursor)) { depth += 1; cursor += 2; continue; }
          if (source.startsWith("-/", cursor)) { depth -= 1; cursor += 2; if (!depth) break; continue; }
          cursor += 1;
        }
        html += span("lean-comment", source.slice(index, cursor)); index = cursor; continue;
      }
      if (char === '"') {
        let cursor = index + 1;
        while (cursor < source.length) {
          if (source[cursor] === "\\") { cursor += 2; continue; }
          if (source[cursor] === '"') { cursor += 1; break; }
          cursor += 1;
        }
        html += span("lean-string", source.slice(index, cursor)); index = cursor; continue;
      }
      if (rest.startsWith("@[")) {
        const end = source.indexOf("]", index + 2);
        const next = end < 0 ? source.length : end + 1;
        html += span("lean-attribute", source.slice(index, next)); index = next; continue;
      }
      if (char === "#" || /[\p{L}_]/u.test(char)) {
        let cursor = index + 1;
        while (cursor < source.length && ident(source[cursor])) cursor += 1;
        const token = source.slice(index, cursor);
        const shortToken = token.includes(".") ? token.slice(token.lastIndexOf(".") + 1) : token;
        html += commands.has(token) ? span("lean-command", token)
          : keywords.has(token) || keywords.has(shortToken) ? span("lean-keyword", token)
            : token.includes(".") ? span("lean-constant", token) : escapeHtml(token);
        index = cursor; continue;
      }
      if (/\d/.test(char)) {
        let cursor = index + 1;
        while (cursor < source.length && /[\d_]/.test(source[cursor])) cursor += 1;
        html += span("lean-number", source.slice(index, cursor)); index = cursor; continue;
      }
      if (symbols.test(char)) { html += span("lean-symbol", char); index += 1; continue; }
      html += escapeHtml(char); index += 1;
    }
    return html;
  }

  function isMobile() { return window.matchMedia("(max-width: 1279px)").matches; }
  function statusLabel(status) { return status === "unreviewed" ? "Open" : status[0].toUpperCase() + status.slice(1); }
  function statusClass(status) { return REVIEW_STATUSES.includes(status) ? status : "unreviewed"; }
  function itemKind(item) { return String(item?.kind || "declaration").replace(/^./, (char) => char.toUpperCase()); }
  function isStacksBook() { return state.selectedSlug === "stacks_project"; }

  function stackTags(item) {
    const values = Array.isArray(item?.tags) ? item.tags : item?.tag ? [item.tag] : [];
    return values.map((value) => typeof value === "string" ? value : value?.tag).filter(Boolean).map(String);
  }

  function stackReference(item) {
    const stem = String(item?.sourcePath || "").split("/").pop()?.replace(/\.lean$/i, "") || "";
    const match = stem.match(/(?:^|_)(\d+(?:_\d+)+)(?:_|$)/);
    return match ? match[1].split("_").join(".") : "";
  }

  function bookState(book) {
    return String(book?.reviewIndex?.state || book?.cache?.state || "not-built");
  }

  function statementParts(item) {
    const raw = String(item?.statement || "").trim();
    const label = String(item?.label || "").trim();
    const title = String(item?.title || "").trim();
    let body = raw;
    let parentheticalTitle = "";
    if (label && body.startsWith(label)) {
      body = body.slice(label.length).trim();
      if (body.startsWith("(")) {
        let depth = 0;
        let close = -1;
        for (let index = 0; index < body.length; index += 1) {
          if (body[index] === "(") depth += 1;
          if (body[index] === ")") {
            depth -= 1;
            if (depth === 0) {
              close = index;
              break;
            }
          }
        }
        if (close >= 0) {
          parentheticalTitle = body.slice(1, close).trim();
          body = body.slice(close + 1).trim();
        }
      }
      body = body.replace(/^:\s*/, "").replace(/^[.;]\s*/, "").trim();
    }
    const heading = label
      ? parentheticalTitle ? `${label} (${parentheticalTitle})` : label
      : title;
    return { heading, body, raw };
  }

  function leanMathToTex(value) {
    const original = String(value || "").trim();
    // Already-authored TeX is not Lean notation: never escape its grouping braces.
    if (/\\(?:[A-Za-z]+|[{}])/u.test(original)) return original;
    const source = original.replace(/\b((?:[A-Za-z]\s+)+[A-Za-z])\s*:/g,
      (_, names) => `${names.trim().split(/\s+/).join(", ")} :`);
    const symbols = {
      "ℕ": "\\mathbb{N}", "ℤ": "\\mathbb{Z}", "ℚ": "\\mathbb{Q}",
      "ℝ": "\\mathbb{R}", "ℂ": "\\mathbb{C}", "∞": "\\infty ",
      "→": "\\to ", "←": "\\leftarrow ", "↔": "\\leftrightarrow ",
      "↦": "\\mapsto ", "≥": "\\ge ", "≤": "\\le ", "≠": "\\ne ",
      "∈": "\\in ", "∉": "\\notin ", "⊆": "\\subseteq ", "⊂": "\\subset ",
      "∪": "\\cup ", "∩": "\\cap ", "∅": "\\varnothing ",
      "∀": "\\forall ", "∃": "\\exists ", "∧": "\\land ", "∨": "\\lor ",
      "¬": "\\neg ", "×": "\\times ", "∑": "\\sum ", "∏": "\\prod ",
      "π": "\\pi ", "α": "\\alpha ", "β": "\\beta ", "ε": "\\varepsilon ",
      "δ": "\\delta ", "λ": "\\lambda ", "μ": "\\mu ", "σ": "\\sigma ",
      "θ": "\\theta ", "φ": "\\varphi ", "ω": "\\omega ", "∥": "\\Vert ",
      "*": " \\cdot ", "{": "\\{", "}": "\\}", "%": "\\%", "&": "\\&", "#": "\\#",
    };
    const sub = "₀₁₂₃₄₅₆₇₈₉", sup = "⁰¹²³⁴⁵⁶⁷⁸⁹";
    let offset = 0;
    const parse = (closing = "") => {
      let result = "";
      while (offset < source.length) {
        const char = source[offset];
        if (closing && char === closing) { offset += 1; break; }
        const operator = source.slice(offset).match(/^(>=|<=|!=|\.\.\.)/);
        const sum = source.slice(offset).match(/^[∑∏]\s+([A-Za-z])\s*,/u);
        if (sum) {
          result += `${char === "∑" ? "\\sum" : "\\prod"}_{${sum[1]}} `;
          offset += sum[0].length;
        } else if (operator) {
          result += { ">=": "\\ge ", "<=": "\\le ", "!=": "\\ne ", "...": "\\ldots " }[operator[0]];
          offset += operator[0].length;
        } else if (char === "^" || char === "_") {
          offset += 1;
          while (/\s/.test(source[offset] || "") && offset < source.length) offset += 1;
          let script = "";
          if (source[offset] === "{" || source[offset] === "(") {
            const end = source[offset++] === "{" ? "}" : ")";
            script = parse(end);
          } else if (source.slice(offset).startsWith("infty")) {
            offset += 5; script = "\\infty";
          } else if (offset < source.length) {
            script = symbols[source[offset]] || source[offset]; offset += 1;
          }
          result += `${char}{${script}}`;
        } else if (sub.includes(char) || sup.includes(char)) {
          const digits = sub.includes(char) ? sub : sup;
          let script = "";
          while (offset < source.length && digits.includes(source[offset])) script += digits.indexOf(source[offset++]);
          result += `${digits === sub ? "_" : "^"}{${script}}`;
        } else if (char === "(" && closing) {
          offset += 1; result += `(${parse(")")})`;
        } else {
          const word = source.slice(offset).match(/^[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9_]*)*/);
          if (word) {
            const name = word[0]; offset += name.length;
            result += name === "infty" ? "\\infty " : name.length === 1 ? name
              : `\\operatorname{${name.replace(/_/g, "\\_")}}`;
          } else {
            // TeX discards spaces; retain application spacing instead of merging
            // the Lean tokens `a i` into the visually different identifier `ai`.
            result += /\s/.test(char) && /[A-Za-z0-9}]/.test(result.slice(-1))
              && /[A-Za-zℕℤℚℝℂ]/.test(source[offset + 1] || "") ? "\\," : symbols[char] || char;
            offset += 1;
          }
        }
      }
      return result;
    };
    return parse();
  }

  function displayStatementHeading(value) {
    return String(value || "").replace(/--/g, "‑").replace(/\s+/g, " ").trim();
  }

  function compactDeclarationName(item) {
    const name = String(item?.name || "").trim();
    if (name) return name;
    const key = String(item?.key || "").trim();
    const prefix = state.selectedSlug ? `${state.selectedSlug}.` : "";
    const withoutBook = prefix && key.startsWith(prefix) ? key.slice(prefix.length) : key;
    return withoutBook.split(".").pop() || "Untitled declaration";
  }

  function itemLocation(item) {
    const sourcePath = String(item?.sourcePath || "").replace(/\\/g, "/");
    const stem = (sourcePath.split("/").pop() || "").replace(/\.lean$/i, "");
    const chapterMatch = sourcePath.match(/(?:^|\/)Chap(?:ter)?0*(\d+)(?:\/|$)/i)
      || String(item?.section || "").match(/^chapter-(\d+)$/i);
    const explicitSection = stem.match(/^section0*(\d+)(?:_part0*(\d+))?$/i);
    const numberedSection = stem.match(/(?:^|_)(\d+)_(\d+)_(\d+)(?:_|$)/);
    const chapter = chapterMatch ? String(Number(chapterMatch[1])) : "";
    let section = explicitSection ? String(Number(explicitSection[1])) : "";
    const part = explicitSection?.[2] ? String(Number(explicitSection[2])) : "";
    if (!section && numberedSection && (!chapter || Number(numberedSection[1]) === Number(chapter))) {
      section = String(Number(numberedSection[2]));
    }
    return [
      chapter ? `Chapter ${chapter}` : "",
      section ? `Section ${section}` : "",
      part ? `Part ${part}` : "",
    ].filter(Boolean);
  }

  function statementMathHtml(value) {
    const source = String(value || "").replace(/^\s*\/[-*]+!?\s*/, "").replace(/\s*[-*]+\/\s*$/, "").trim();
    if (!source) return "";
    const rendered = [];
    let paragraph = [];
    const flushParagraph = () => {
      const text = paragraph.join(" ").trim();
      paragraph = [];
      if (!text) return;
      const parts = text.split(/(`[^`]*`)/g);
      const inline = parts.map((part) => {
        if (part.startsWith("`") && part.endsWith("`") && part.length >= 2) {
          const content = part.slice(1, -1);
          if (/(?:\b(?:by|def|lemma|theorem|fun|let|have|exact|simp)\b|:=|=>)/.test(content)) {
            return `<code class="statement-inline-code">${escapeHtml(content)}</code>`;
          }
          return `\\(${escapeHtml(leanMathToTex(content))}\\)`;
        }
        return escapeHtml(part);
      }).join("");
      rendered.push(`<div class="statement-line">${inline}</div>`);
    };
    const lines = source.split(/\r?\n/);
    let fenced = null;
    lines.forEach((line, index) => {
      const text = line.trim();
      if (/^```/.test(text)) {
        flushParagraph();
        if (fenced !== null) {
          rendered.push(`<pre class="statement-code"><code>${escapeHtml(fenced.join("\n"))}</code></pre>`);
          fenced = null;
        } else fenced = [];
        return;
      }
      if (fenced !== null) { fenced.push(line); return; }
      const standaloneMatch = text.match(/^`([^`]*)`([.,;:!?。；，]?)$/u);
      // A source-editor line wrap does not turn an inline formula into a display.
      if (standaloneMatch && !paragraph.length && (!lines[index + 1]?.trim())
          && !/(?:\b(?:by|def|lemma|theorem|fun|let)\b|:=|=>)/.test(standaloneMatch[1])) {
        flushParagraph();
        const punctuation = standaloneMatch[2];
        const mathPunctuation = punctuation && !/[.,;:!?]/.test(punctuation)
          ? `\\text{${punctuation}}`
          : punctuation;
        rendered.push(`<div class="statement-formula">\\[${escapeHtml(leanMathToTex(standaloneMatch[1]))}${escapeHtml(mathPunctuation)}\\]</div>`);
      } else if (!text) {
        flushParagraph();
      } else {
        paragraph.push(text);
      }
    });
    if (fenced !== null) rendered.push(`<pre class="statement-code"><code>${escapeHtml(fenced.join("\n"))}</code></pre>`);
    flushParagraph();
    return rendered.join("");
  }

  function typesetMath(root) {
    if (!root || !window.MathJax || typeof window.MathJax.typesetPromise !== "function") return;
    try {
      if (typeof window.MathJax.typesetClear === "function") window.MathJax.typesetClear([root]);
    } catch (_) {
      // MathJax cleanup is best effort; the text fallback remains readable.
    }
    window.MathJax.typesetPromise([root]).catch((error) => {
      console.error("MathJax statement typeset failed", error);
    });
  }

  function renderStatementSource(item) {
    const source = String(item?.statement || "").trim();
    refs.statementPanel.hidden = !source;
    refs.statementSourcePreview.querySelector("code").textContent = source;
    refs.statementSourcePreview.hidden = !state.statementSourceOpen;
    refs.statementSourceToggle.disabled = !source;
    refs.copyStatementSource.disabled = !source;
    refs.statementSourceToggle.setAttribute("aria-expanded", String(state.statementSourceOpen));
    refs.statementSourceToggle.textContent = state.statementSourceOpen ? "Hide source" : "View source";
  }

  function copyWithTextarea(value) {
    const textarea = document.createElement("textarea");
    textarea.value = value;
    textarea.setAttribute("readonly", "");
    textarea.style.position = "fixed";
    textarea.style.opacity = "0";
    document.body.appendChild(textarea);
    textarea.select();
    const copied = document.execCommand("copy");
    textarea.remove();
    if (!copied) throw new Error("Copy command was rejected.");
  }

  async function copyStatementSource() {
    const item = state.items.find((value) => value.key === state.selectedKey);
    const source = String(item?.statement || "").trim();
    if (!source) return;
    if (state.statementCopyTimer) window.clearTimeout(state.statementCopyTimer);
    try {
      if (navigator.clipboard?.writeText) await navigator.clipboard.writeText(source);
      else copyWithTextarea(source);
      refs.copyStatementSource.textContent = "Copied";
    } catch (_) {
      refs.copyStatementSource.textContent = "Copy failed";
    }
    state.statementCopyTimer = window.setTimeout(() => {
      refs.copyStatementSource.textContent = "Copy source";
      state.statementCopyTimer = null;
    }, 1800);
  }

  async function api(path, options = {}) {
    const response = await fetch(String(path).startsWith("/") ? appUrl(path) : path, {
      cache: "no-store",
      ...options,
    });
    const payload = await response.json().catch(() => ({}));
    if (!response.ok) {
      const detail = typeof payload.detail === "string"
        ? payload.detail
        : payload.detail && typeof payload.detail.message === "string"
          ? payload.detail.message
          : payload.error;
      throw new Error(detail || `Request failed (${response.status})`);
    }
    return payload;
  }

  function setSync(text, mode = "") {
    refs.bookSync.textContent = text;
    refs.bookSync.className = `sync-state ${mode}`.trim();
  }

  function setMobileView(view, persist = true) {
    const next = ["catalog", "queue", "evidence", "review"].includes(view) ? view : "queue";
    state.mobileView = next;
    refs.appShell.dataset.mobileView = next;
    refs.mobileButtons.forEach((button) => button.setAttribute("aria-pressed", String(button.dataset.mobileView === next)));
    if (persist) localStorage.setItem("reasbook-reviewer:mobile-view", next);
    if (next === "evidence" && state.evidenceView === "graph") {
      // A graph loaded in a hidden mobile pane has no usable viewport yet.
      requestAnimationFrame(() => refs.graphFrame.contentWindow?.dispatchEvent(new Event("resize")));
    }
  }

  function panelPreferenceKey(panel) {
    return `reasbook-reviewer:${panel}-collapsed`;
  }

  function readPanelPreference(panel) {
    try {
      return localStorage.getItem(panelPreferenceKey(panel)) === "true";
    } catch (_) {
      return false;
    }
  }

  function setPanelCollapsed(panel, collapsed, persist = true) {
    if (!["catalog", "queue", "review"].includes(panel)) return;
    const isCatalog = panel === "catalog";
    const isQueue = panel === "queue";
    const key = isCatalog ? "catalogCollapsed" : isQueue ? "queueCollapsed" : "reviewCollapsed";
    const buttons = isCatalog
      ? [refs.toggleCatalog, refs.catalogPanelToggle]
      : isQueue
        ? [refs.toggleQueue, refs.queueRailToggle, refs.queuePanelToggle]
        : [refs.toggleReview, refs.reviewPanelToggle, refs.reviewRailToggle];
    const target = isCatalog ? refs.catalogPanel : isQueue ? refs.evidencePanel : refs.reviewPanel;
    const label = isCatalog ? "catalog" : isQueue ? "queue" : "review panel";
    const next = Boolean(collapsed);
    state[key] = next;
    refs.appShell.dataset[`${panel}Collapsed`] = String(next);
    buttons.forEach((button) => {
      button.setAttribute("aria-expanded", String(!next));
      button.setAttribute("aria-label", `${next ? "Show" : "Hide"} ${label}`);
      button.title = `${next ? "Show" : "Hide"} ${label}`;
      button.classList.toggle("is-collapsed", next);
    });
    if (persist) {
      try {
        localStorage.setItem(panelPreferenceKey(panel), String(next));
      } catch (_) {
        // Layout preferences are optional when storage is unavailable.
      }
    }
    if (next && target.contains(document.activeElement)) {
      (isCatalog ? refs.catalogPanelToggle : isQueue ? refs.queueRailToggle : refs.reviewRailToggle).focus();
    }
  }

  const PANE_WIDTHS = {
    catalog: { property: "--catalog-width", min: 220, max: 520, fallback: 324 },
    queue: { property: "--queue-width", min: 280, max: 720, fallback: 380 },
    review: { property: "--review-width", min: 300, max: 680, fallback: 400 },
  };

  function paneWidthKey(panel) {
    return `reasbook-reviewer:${panel}-width`;
  }

  function setPaneWidth(panel, value, persist = true) {
    const config = PANE_WIDTHS[panel];
    if (!config) return;
    const width = Math.round(Math.max(config.min, Math.min(config.max, Number(value) || config.fallback)));
    refs.appShell.style.setProperty(config.property, `${width}px`);
    const separator = panel === "catalog" ? refs.catalogResize : panel === "queue" ? refs.queueResize : refs.reviewResize;
    separator.setAttribute("aria-valuenow", String(width));
    separator.setAttribute("aria-valuetext", `${width} pixels`);
    if (persist) {
      try {
        localStorage.setItem(paneWidthKey(panel), String(width));
      } catch (_) {
        // The current width still applies when storage is restricted.
      }
    }
  }

  function initializePaneWidths() {
    Object.entries(PANE_WIDTHS).forEach(([panel, config]) => {
      const compactDefaults = { catalog: 260, queue: 340, review: 360 };
      let width = window.innerWidth < 1400 ? compactDefaults[panel] : config.fallback;
      try {
        width = Number(localStorage.getItem(paneWidthKey(panel))) || width;
      } catch (_) {
        // Defaults remain usable when storage is restricted.
      }
      setPaneWidth(panel, width, false);
    });
  }

  function bindPaneResizer(separator, panel) {
    const config = PANE_WIDTHS[panel];
    const widthFromPointer = (clientX) => {
      if (panel === "catalog") return clientX - refs.appShell.getBoundingClientRect().left;
      const workspace = separator.parentElement.getBoundingClientRect();
      return panel === "queue" ? clientX - workspace.left : workspace.right - clientX;
    };
    separator.addEventListener("pointerdown", (event) => {
      if (isMobile()) return;
      event.preventDefault();
      separator.setPointerCapture(event.pointerId);
      document.body.classList.add("is-resizing-pane");
      setPaneWidth(panel, widthFromPointer(event.clientX), false);
    });
    separator.addEventListener("pointermove", (event) => {
      if (!separator.hasPointerCapture(event.pointerId)) return;
      setPaneWidth(panel, widthFromPointer(event.clientX), false);
    });
    const finish = (event) => {
      if (!separator.hasPointerCapture(event.pointerId)) return;
      separator.releasePointerCapture(event.pointerId);
      document.body.classList.remove("is-resizing-pane");
      const value = parseInt(separator.getAttribute("aria-valuenow") || config.fallback, 10);
      setPaneWidth(panel, value, true);
    };
    separator.addEventListener("pointerup", finish);
    separator.addEventListener("pointercancel", finish);
    separator.addEventListener("keydown", (event) => {
      if (event.key !== "ArrowLeft" && event.key !== "ArrowRight") return;
      event.preventDefault();
      const current = parseInt(separator.getAttribute("aria-valuenow") || config.fallback, 10);
      const direction = (event.key === "ArrowRight" ? 1 : -1) * (panel === "review" ? -1 : 1);
      setPaneWidth(panel, current + direction * (event.shiftKey ? 40 : 10));
    });
  }

  function initializePanelState() {
    setPanelCollapsed("catalog", readPanelPreference("catalog"), false);
    setPanelCollapsed("queue", readPanelPreference("queue"), false);
    // Evidence is always present on desktop; discard the retired preference.
    try { localStorage.removeItem(panelPreferenceKey("canvas")); } catch (_) { /* Optional storage. */ }
    delete refs.appShell.dataset.canvasCollapsed;
    setPanelCollapsed("review", readPanelPreference("review"), false);
  }

  function reviewRows(key) {
    return [...(state.reviews.get(key)?.values() || [])];
  }

  function mineReview(key) {
    const rows = reviewRows(key);
    const id = state.session?.user?.id;
    return rows.find((row) => id && row.actorId === id) || {
      itemKey: key, status: "unreviewed", comment: "", revision: 0, actorId: "",
    };
  }

  function aggregateReview(key) {
    const rows = reviewRows(key).filter((row) => row.status !== "unreviewed");
    for (const status of SEVERITY) {
      const matches = rows.filter((row) => row.status === status);
      if (matches.length) return {
        status,
        count: matches.length,
        reviewers: [...new Set(rows.map((row) => row.reviewer).filter(Boolean))],
      };
    }
    return { status: "unreviewed", count: 0, reviewers: [] };
  }

  function mergeReviews(rows) {
    (rows || []).forEach((row) => {
      if (!row || !row.itemKey) return;
      const map = state.reviews.get(row.itemKey) || new Map();
      map.set(row.actorId || row.reviewer || "unknown", row);
      state.reviews.set(row.itemKey, map);
    });
  }

  const SUBJECT_LABELS = {
    "analysis": "Analysis",
    "algebra": "Algebra",
    "geometry-topology": "Geometry & topology",
    "optimization": "Optimization",
    "numerical-analysis": "Numerical analysis",
    "probability": "Probability & statistics",
    "general": "General"
  };

  // Explicit, cross-listed disciplines for the published catalog. Resource
  // type (book/paper) is deliberately independent of mathematical subject.
  const BOOK_SUBJECTS = {
    "algebraictopology_may_1999": ["geometry-topology", "algebra"],
    "analysis2_tao_2022": ["analysis"],
    "combinatorialgrouptheory_magnus_2004": ["algebra"],
    "computationalmethodsinverseproblems_vogel_2002": ["numerical-analysis", "analysis"],
    "convexanalysis_rockafellar_1970": ["analysis", "optimization"],
    "convexanalysismonotoneoperators_bauschkecombettes_2017": ["analysis", "optimization"],
    "firstordermethodsoptimization_beck_2017": ["optimization", "numerical-analysis"],
    "integerprogramming_conforti_2014": ["optimization"],
    "introductiontorealanalysisvolumei_jirilebl_2025": ["analysis"],
    "introductorylecturesonconvexoptimization_nesterov_2004": ["optimization"],
    "optimizationtheoryandmethods_sunyuan_2006": ["optimization", "numerical-analysis"],
    "probabilitytheory_klenke_2020": ["probability", "analysis"],
    "riemannsurfaces_forster_1981": ["geometry-topology", "analysis"],
    "stacks_project": ["algebra", "geometry-topology"],
    "onsomelocalrings_maassaran_2025": ["algebra"],
    "smoothminimization_nesterov_2004": ["optimization", "analysis"],
    "tr_lalm_theory": ["optimization", "numerical-analysis"]
  };

  function bookSubjects(book) {
    return BOOK_SUBJECTS[book.slug] || ["general"];
  }

  function renderCatalog() {
    const query = state.bookSearch.trim().toLowerCase();
    const visible = state.catalog.filter((book) => {
      if (state.kindFilter !== "all" && book.kind !== state.kindFilter) return false;
      if (state.availabilityFilter === "ready" && bookState(book) !== "ready") return false;
      if (state.availabilityFilter === "pending" && bookState(book) === "ready") return false;
      const subjects = bookSubjects(book);
      if (state.subjectFilters.size && !subjects.some((subject) => state.subjectFilters.has(subject))) return false;
      const text = `${book.title} ${book.authors} ${book.slug} ${subjects.map((subject) => SUBJECT_LABELS[subject]).join(" ")}`.toLowerCase();
      return !query || text.includes(query);
    });
    refs.bookCount.textContent = `${visible.length} of ${state.catalog.length} resources`;
    refs.subjectSummary.textContent = state.subjectFilters.size
      ? [...state.subjectFilters].map((subject) => SUBJECT_LABELS[subject]).join(", ") : "All subjects";
    refs.subjectSummary.title = refs.subjectSummary.textContent;
    refs.clearSubjectFilters.hidden = state.subjectFilters.size === 0;
    refs.catalogList.setAttribute("aria-busy", "false");
    const renderBook = (book) => {
        const selected = book.slug === state.selectedSlug;
        const stateText = bookState(book) === "ready" ? "Ready" : "Pending";
        return `<button class="catalog-item" type="button" aria-pressed="${selected}" data-book-slug="${escapeHtml(book.slug)}">
          <span class="catalog-item-title">${escapeHtml(book.title)}</span>
          <span class="catalog-item-subjects">${bookSubjects(book).map((subject) => escapeHtml(SUBJECT_LABELS[subject])).join(" · ")}</span>
          <span class="catalog-item-meta"><span>${escapeHtml(book.authors || "Author unavailable")}</span><span class="catalog-item-state">${stateText}</span></span>
        </button>`;
    };
    const groups = [
      ["book", "Books"],
      ["paper", "Papers"],
    ].map(([kind, label]) => [label, visible.filter((book) => book.kind === kind)])
      .filter(([, books]) => books.length);
    refs.catalogList.innerHTML = groups.length
      ? groups.map(([label, books]) => `<section class="catalog-group" aria-label="${label}">
          <div class="catalog-group-heading"><span>${label}</span><span>${books.length}</span></div>
          ${books.map(renderBook).join("")}
        </section>`).join("")
      : `<div class="catalog-empty">No matching resources.</div>`;
    refs.catalogList.querySelectorAll("[data-book-slug]").forEach((button) => {
      button.addEventListener("click", () => selectBook(button.dataset.bookSlug, true));
    });
  }

  function renderAuth() {
    const session = state.session || {};
    refs.brandLink.href = appUrl("/");
    refs.loginLink.hidden = Boolean(session.user);
    refs.logoutButton.hidden = !session.canLogout;
    refs.exportLink.hidden = !session.canExport;
    refs.exportLink.href = appUrl("/api/reviews/export.jsonl");
    if (session.canLogin) {
      refs.loginLink.href = appUrl(`/api/auth/oauth/start?return_to=${encodeURIComponent(window.location.pathname + window.location.search)}`);
      refs.loginLink.removeAttribute("aria-disabled");
      refs.loginLink.title = "Sign in to review";
      refs.authState.textContent = "Review access available";
    } else if (session.user) {
      refs.authState.textContent = session.user.displayName || session.user.id || "Signed in";
    } else if (session.authConfigured === false) {
      refs.loginLink.removeAttribute("href");
      refs.loginLink.setAttribute("aria-disabled", "true");
      refs.loginLink.title = "Authentication is not configured for this deployment";
      refs.authState.textContent = "Identity setup pending";
    } else {
      refs.loginLink.removeAttribute("href");
      refs.loginLink.setAttribute("aria-disabled", "true");
      refs.loginLink.title = "Sign in is unavailable";
      refs.authState.textContent = "Read-only";
    }
  }

  function evidenceStatuses(context, selectedKey) {
    const labels = ["Graph", "Source", "Docs", "Verso"];
    const pending = !selectedKey ? "not selected" : context?.error ? "check failed" : "checking";
    // Never carry book-wide directory availability into declaration status.
    if (!context?.item || context.item.key !== selectedKey) {
      return labels.map((label) => [label, pending]);
    }
    const resources = context.resources || {};
    const graph = context.graph || {};
    const mode = graph.generation?.mode || "";
    const graphStatus = !resources.graph?.url || !graph.available ? "unavailable"
      : !graph.selected ? "not indexed"
      : graph.selectedDependencyEvidence === "source-only" || mode === "source-fallback" ? "source only"
      : mode.startsWith("lean-environment") ? "ready" : "unverified";
    return [
      ["Graph", graphStatus],
      ["Source", context.source?.available ? "ready" : "unavailable"],
      ["Docs", resources.docs?.available && resources.docs?.url ? "ready" : "unavailable"],
      ["Verso", resources.verso?.available && resources.verso?.url ? "ready" : "unavailable"],
    ];
  }

  function renderBookOverview() {
    const book = state.book;
    if (!book) {
      refs.bookOverview.innerHTML = `<div class="detail-empty">Select a book to load its review index.</div>`;
      return;
    }
    const count = state.items.length;
    const counts = state.items.reduce((acc, item) => { acc[aggregateReview(item.key).status] += 1; return acc; }, { accepted: 0, mismatch: 0, other: 0, unreviewed: 0 });
    const evidence = evidenceStatuses(state.context, state.selectedKey)
      .filter(([label]) => label !== "Verso" || !isStacksBook());
    refs.bookOverview.innerHTML = `<div class="book-overview-row" aria-label="Book and evidence status">
      <span class="meta-chip meta-chip-state">${bookState(book) === "ready" ? "Index ready" : "Index pending"}</span>
      <span class="meta-chip">${count} declarations</span>
      ${(book.branches || []).map((branch) => `<span class="meta-chip">${escapeHtml(branch)}</span>`).join("")}
      ${evidence.map(([label, status]) => `<span class="meta-chip evidence-chip ${status === "ready" ? "available" : "unavailable"}" data-evidence-kind="${label.toLowerCase()}" title="Evidence for the selected declaration in the selected release">${escapeHtml(label)} ${escapeHtml(status)}</span>`).join("")}
      <span class="meta-chip review-summary-chip">${counts.unreviewed} open · ${counts.accepted} accepted · ${counts.mismatch + counts.other} flagged</span>
    </div>`;
  }

  function updateTypeFilter() {
    const values = [...new Set(state.items.map((item) => item.kind).filter(Boolean))].sort();
    const current = state.itemTypeFilter;
    refs.itemTypeFilter.innerHTML = `<option value="all">All types</option>${values.map((value) => `<option value="${escapeHtml(value)}">${escapeHtml(itemKind({ kind: value }))}</option>`).join("")}`;
    refs.itemTypeFilter.value = values.includes(current) ? current : "all";
    state.itemTypeFilter = refs.itemTypeFilter.value;
    const sections = [...new Set(state.items.map((item) => item.section).filter(Boolean))].sort();
    const currentSection = state.itemSectionFilter;
    refs.itemSectionFilter.innerHTML = `<option value="all">All sections</option>${sections.map((value) => `<option value="${escapeHtml(value)}">${escapeHtml(value.replace(/^chapter-/, "Chapter "))}</option>`).join("")}`;
    refs.itemSectionFilter.value = sections.includes(currentSection) ? currentSection : "all";
    state.itemSectionFilter = refs.itemSectionFilter.value;
  }

  function visibleItems() {
    const query = state.itemSearch.trim().toLowerCase();
    return state.items.filter((item) => {
      const status = aggregateReview(item.key).status;
      if (state.reviewFilter !== "all" && status !== state.reviewFilter) return false;
      if (state.itemTypeFilter !== "all" && item.kind !== state.itemTypeFilter) return false;
      if (state.itemSectionFilter !== "all" && item.section !== state.itemSectionFilter) return false;
      const tags = stackTags(item).join(" ");
      const text = `${item.key} ${item.name || ""} ${item.title || ""} ${item.label || ""} ${item.statement || ""} ${item.sourcePath || ""} ${tags}`.toLowerCase();
      return !query || text.includes(query);
    });
  }

  function renderQueue() {
    const items = visibleItems();
    const shown = items.slice(0, state.reviewLimit);
    const hasFilters = Boolean(
      state.itemSearch.trim()
      || state.itemTypeFilter !== "all"
      || state.itemSectionFilter !== "all"
      || state.reviewFilter !== "all"
    );
    refs.itemResultCount.textContent = `${items.length} match${items.length === 1 ? "" : "es"}`;
    refs.clearItemFilters.hidden = !hasFilters;
    refs.reviewQueue.innerHTML = shown.length ? shown.map((item) => {
      const aggregate = aggregateReview(item.key);
      const reviewers = aggregate.reviewers.length ? `reviewed by ${aggregate.reviewers.slice(0, 2).join(", ")}` : "";
      const declarationName = compactDeclarationName(item);
      const stacksMode = isStacksBook();
      const tags = stacksMode ? stackTags(item) : [];
      const title = String(stacksMode ? declarationName : item.title || declarationName).trim();
      const queueLabel = stacksMode ? (tags.join(" / ") || "No tag") : String(item.label || declarationName).trim();
      const queueReference = stacksMode ? stackReference(item) : (item.line ? `L${item.line}` : item.kind || "");
      const location = itemLocation(item);
      const ariaLabel = [queueLabel, queueReference, declarationName, title, ...location, item.line ? `line ${item.line}` : ""].filter(Boolean).join(": ");
      return `<button type="button" role="option" aria-label="${escapeHtml(ariaLabel)}" title="${escapeHtml(item.key || declarationName)}" aria-selected="${item.key === state.selectedKey}" tabindex="${item.key === state.selectedKey ? 0 : -1}" class="queue-row${stacksMode ? " stacks-queue-row" : ""} status-${statusClass(aggregate.status)} ${item.key === state.selectedKey ? "active" : ""}" data-item-key="${escapeHtml(item.key)}">
        <div class="queue-row-heading"><span class="queue-key${stacksMode && !tags.length ? " queue-key-muted" : ""}" title="${escapeHtml(declarationName)}">${escapeHtml(queueLabel)}</span><span class="queue-ref">${escapeHtml(queueReference)}</span></div>
        <div class="queue-title" title="${escapeHtml(item.title || title)}">${escapeHtml(title)}</div>
        ${location.length ? `<div class="queue-location" title="${escapeHtml(item.sourcePath || "")}">${location.map((value) => `<span>${escapeHtml(value)}</span>`).join("")}</div>` : ""}
        <div class="queue-meta"><span class="queue-badge ${statusClass(aggregate.status)}">${statusLabel(aggregate.status)}${aggregate.count > 1 ? ` x${aggregate.count}` : ""}</span><span class="queue-badge">${escapeHtml(itemKind(item))}</span>${reviewers ? `<span class="queue-badge reviewer">${escapeHtml(reviewers)}</span>` : ""}</div>
      </button>`;
    }).join("") : `<div class="empty-state">No declarations match these filters.</div>`;
    if (items.length > shown.length) {
      const more = document.createElement("button");
      more.className = "button button-quiet";
      more.type = "button";
      more.textContent = `Load ${Math.min(80, items.length - shown.length)} more`;
      more.addEventListener("click", () => { state.reviewLimit += 80; renderQueue(); });
      refs.reviewQueue.appendChild(more);
    }
    refs.reviewQueue.querySelectorAll("[data-item-key]").forEach((button) => {
      button.addEventListener("click", () => selectItem(button.dataset.itemKey, true));
    });
    refs.reviewQueue.setAttribute("aria-label", `${items.length} declarations shown`);
  }

  function renderToolbar() {
    const book = state.book;
    refs.currentBookTitle.textContent = book?.title || "ReasBook Review";
    refs.currentBookMeta.textContent = book ? `${book.branches?.join(", ") || "unversioned"} / ${state.items.length} declarations / ${state.items.filter((item) => item.hasSorry).length} with sorry` : "Select a book";
    refs.currentBookMeta.title = refs.currentBookMeta.textContent;
  }

  function evidenceFrame(kind) {
    return kind === "docs" ? refs.docsFrame : kind === "verso" ? refs.versoFrame : null;
  }

  function evidenceFrameLocation(kind) {
    const frame = evidenceFrame(kind);
    if (!frame) return "";
    try {
      return String(frame.contentWindow?.location?.href || frame.src || "");
    } catch (_) {
      return String(frame.src || "");
    }
  }

  function currentEvidenceHistoryKind() {
    return state.evidenceView === "docs" || state.evidenceView === "verso" ? state.evidenceView : "";
  }

  function selectedEvidenceItem() {
    return state.items.find((item) => item.key === state.selectedKey) || null;
  }

  function clearEvidenceTarget(frameDocument) {
    frameDocument.querySelectorAll(".reasbook-reviewer-target").forEach((node) => node.classList.remove("reasbook-reviewer-target"));
  }

  function markEvidenceTarget(frameDocument, target) {
    if (!target) return false;
    clearEvidenceTarget(frameDocument);
    target.classList.add("reasbook-reviewer-target");
    target.scrollIntoView({ block: "center", inline: "nearest", behavior: "auto" });
    return true;
  }

  function focusDocsDeclaration() {
    const item = selectedEvidenceItem();
    const frameDocument = refs.docsFrame.contentDocument;
    if (!item || !frameDocument) return false;
    return markEvidenceTarget(frameDocument, frameDocument.getElementById(item.name));
  }

  function focusVersoDeclaration() {
    const item = selectedEvidenceItem();
    const frame = refs.versoFrame;
    const frameDocument = frame.contentDocument;
    if (!item || !frameDocument) return false;
    let target = null;
    frameDocument.querySelectorAll("a[href]").forEach((anchor) => {
      if (target) return;
      try {
        const url = new URL(anchor.getAttribute("href") || "", frame.contentWindow.location.href);
        if (url.searchParams.get("pattern") === item.name) target = anchor.closest("code.hl.lean.block, .declaration") || anchor;
      } catch (_) {
        // Ignore malformed generated links and continue with the text fallback.
      }
    });
    if (!target) {
      target = [...frameDocument.querySelectorAll("code.hl.lean.block")]
        .find((block) => String(block.textContent || "").includes(item.name)) || null;
    }
    return markEvidenceTarget(frameDocument, target);
  }

  function focusCurrentEvidenceDeclaration(kind) {
    return kind === "docs" ? focusDocsDeclaration() : kind === "verso" ? focusVersoDeclaration() : false;
  }

  function updateEvidenceHistoryControls() {
    const kind = currentEvidenceHistoryKind();
    const navigation = kind ? state.frameHistory[kind] : null;
    const canReturnToEvidence = state.evidenceView === "source" && state.evidenceReturn?.view;
    const visible = Boolean((navigation && navigation.entries.length) || canReturnToEvidence);
    refs.evidenceHistoryControls.hidden = !visible;
    if (!kind) {
      refs.evidenceBack.disabled = !canReturnToEvidence;
      refs.evidenceForward.disabled = true;
      refs.evidenceBack.title = canReturnToEvidence ? `Back to ${state.evidenceReturn.view === "verso" ? "Verso" : "Docs"}` : "Back";
      refs.evidenceForward.title = "Forward";
      return;
    }
    const busy = Boolean(navigation?.pendingAction);
    refs.evidenceBack.disabled = !navigation || busy || navigation.index <= 0;
    refs.evidenceForward.disabled = !navigation || busy || navigation.index >= navigation.entries.length - 1;
    refs.evidenceBack.title = busy ? "Loading page" : "Back";
    refs.evidenceForward.title = busy ? "Loading page" : "Forward";
  }

  function resetEvidenceFrameHistory(kind, url) {
    const navigation = state.frameHistory[kind];
    navigation.entries = url ? [url] : [];
    navigation.index = url ? 0 : -1;
    navigation.pendingReset = Boolean(url);
    navigation.pendingAction = null;
    updateEvidenceHistoryControls();
  }

  function recordEvidenceFrameLocation(kind) {
    const navigation = state.frameHistory[kind];
    const url = evidenceFrameLocation(kind);
    if (!navigation || !url || url === "about:blank") return;
    if (navigation.pendingReset) {
      navigation.entries = [url];
      navigation.index = 0;
      navigation.pendingReset = false;
      navigation.pendingAction = null;
      updateEvidenceHistoryControls();
      return;
    }
    const knownIndex = navigation.entries.indexOf(url);
    if (knownIndex >= 0) {
      navigation.index = knownIndex;
    } else {
      navigation.entries = navigation.entries.slice(0, navigation.index + 1);
      navigation.entries.push(url);
      navigation.index = navigation.entries.length - 1;
    }
    navigation.pendingAction = null;
    updateEvidenceHistoryControls();
  }

  function bindEvidenceFrameHistory(kind) {
    const frame = evidenceFrame(kind);
    if (!frame) return;
    try {
      const frameWindow = frame.contentWindow;
      if (!frameWindow) return;
      const marker = "__reasbookReviewerHistoryBound";
      if (!frameWindow[marker]) {
        frameWindow.addEventListener("hashchange", () => recordEvidenceFrameLocation(kind));
        frameWindow.addEventListener("popstate", () => recordEvidenceFrameLocation(kind));
        frameWindow[marker] = true;
      }
    } catch (_) {
      // A sandbox or cross-origin policy can deny access until the next load.
    }
    recordEvidenceFrameLocation(kind);
  }

  function navigateEvidenceHistory(kind, direction) {
    if (!kind) {
      if (direction < 0 && state.evidenceReturn?.view) {
        const destination = state.evidenceReturn;
        state.evidenceReturn = null;
        setEvidenceView(destination.view);
        if (destination.url) {
          const frame = evidenceFrame(destination.view);
          if (frame && evidenceFrameLocation(destination.view) !== destination.url) {
            resetEvidenceFrameHistory(destination.view, destination.url);
            frame.src = destination.url;
          }
        }
      }
      return;
    }
    const navigation = state.frameHistory[kind];
    const frame = evidenceFrame(kind);
    if (!navigation || !frame || navigation.pendingAction) return;
    const nextIndex = navigation.index + direction;
    if (nextIndex < 0 || nextIndex >= navigation.entries.length) return;
    navigation.pendingAction = direction < 0 ? "back" : "forward";
    updateEvidenceHistoryControls();
    try {
      frame.contentWindow.history.go(direction);
      window.setTimeout(() => {
        if (!navigation.pendingAction) return;
        const currentUrl = evidenceFrameLocation(kind);
        const expectedUrl = navigation.entries[nextIndex];
        if (currentUrl && currentUrl !== navigation.entries[navigation.index] && (!expectedUrl || currentUrl === expectedUrl)) {
          recordEvidenceFrameLocation(kind);
        }
      }, 250);
    } catch (_) {
      navigation.pendingAction = null;
      updateEvidenceHistoryControls();
    }
  }

  function setEvidenceView(view) {
    const requestedView = ["graph", "source", "docs", "verso"].includes(view) ? view : "graph";
    state.evidenceView = isStacksBook() && requestedView === "verso" ? "graph" : requestedView;
    if (state.evidenceView !== "source") state.evidenceReturn = null;
    document.querySelectorAll("[data-evidence-view]").forEach((button) => button.setAttribute("aria-selected", String(button.dataset.evidenceView === state.evidenceView)));
    refs.graphView.hidden = state.evidenceView !== "graph";
    refs.sourceView.hidden = state.evidenceView !== "source";
    refs.docsView.hidden = state.evidenceView !== "docs";
    refs.versoView.hidden = state.evidenceView !== "verso";
    updateEvidenceHistoryControls();
    syncGraphScopeControls();
    if (state.evidenceView === "docs" || state.evidenceView === "verso") {
      window.setTimeout(() => focusCurrentEvidenceDeclaration(state.evidenceView), 0);
    }
  }

  function renderGraph() {
    syncGraphScopeControls();
    const item = state.items.find((value) => value.key === state.selectedKey);
    const graphUrl = state.context?.resources?.graph?.url || "";
    if (graphUrl && state.context) {
      refs.graphFallback.hidden = true;
      refs.graphFrame.hidden = false;
      const graph = state.context.graph || {};
      const graphMode = graph.generation?.mode || "";
      const dependencyCoverage = graph.generation?.dependencyCoverage || "";
      const partialCoverage = dependencyCoverage === "partial" || graphMode === "lean-environment-partial";
      const evidenceLabel = graphMode === "source-fallback"
        ? "Source index · dependency evidence unavailable"
        : graphMode === "curated" || graphMode === "curated-static"
          ? "Curated · reviewed dependency links"
        : partialCoverage
          ? `Compiled · partial coverage (${graph.generation?.compiledItemCount || 0}/${graph.generation?.mergedItemCount || graph.totalNodes || 0})`
        : graph.typedDependencies
          ? "Compiled · statement / proof edges"
          : "Compiled · legacy union edges";
      refs.evidenceStats.innerHTML = `<span class="stat-chip${graphMode === "source-fallback" || partialCoverage ? " warn" : ""}">${escapeHtml(evidenceLabel)}</span>`;
      const absolute = new URL(appUrl(graphUrl), window.location.origin).href;
      const graphId = state.context.graph?.selected || item?.graphId || "";
      const hash = graphId ? `#${encodeURIComponent(graphId)}` : "";
      const currentBase = refs.graphFrame.src.split("#")[0];
      if (currentBase !== absolute) {
        refs.graphFrame.dataset.graphScopeBook = state.selectedSlug;
        refs.graphFrame.dataset.graphScopeDesired = graphScopePreference(state.selectedSlug);
        refs.graphFrame.dataset.graphScopePending = "true";
        refs.graphFrame.src = `${absolute}${hash}`;
      } else if (hash) {
        try {
          if (refs.graphFrame.contentWindow.location.hash !== hash) refs.graphFrame.contentWindow.location.hash = hash;
        } catch (_) {
          refs.graphFrame.src = `${absolute}${hash}`;
        }
      }
      return;
    }
    refs.graphFrame.hidden = true;
    refs.graphFallback.hidden = false;
    if (!state.context) {
      refs.graphMessage.textContent = state.selectedKey ? "Loading evidence…" : "Select a statement to inspect its dependencies.";
      refs.graphCanvas.innerHTML = "";
      refs.evidenceStats.innerHTML = "";
      return;
    }
    const graph = state.context?.graph;
    if (!graph?.available) {
      refs.graphMessage.textContent = "No theorem graph is available for this statement.";
      refs.graphCanvas.innerHTML = "";
      refs.evidenceStats.innerHTML = `<span class="stat-chip">graph unavailable</span>`;
      return;
    }
    refs.graphMessage.textContent = graph.edges?.length ? "" : "Source-fallback graph: no dependency edges were emitted for this release.";
    refs.evidenceStats.innerHTML = `<span class="stat-chip">${graph.nodes?.length || 0} nearby nodes</span><span class="stat-chip">${graph.edges?.length || 0} edges</span>${graph.totalNodes ? `<span class="stat-chip">${graph.totalNodes} mapped</span>` : ""}`;
    const selected = (graph.nodes || []).filter((node) => node.selected);
    const nearby = (graph.nodes || []).filter((node) => !node.selected);
    const renderNode = (node) => `<button type="button" class="graph-node ${node.selected ? "selected" : ""}" data-graph-name="${escapeHtml(node.declaration || node.name || "")}"><strong>${escapeHtml(node.declaration || node.name || "unknown")}</strong><span>${escapeHtml(node.label || node.title || node.file || "")}</span></button>`;
    refs.graphCanvas.innerHTML = `<div class="graph-lane"><h3>Selected</h3>${selected.length ? selected.map(renderNode).join("") : `<div class="empty-state">No selected node.</div>`}</div><div class="graph-lane"><h3>Same source file</h3>${nearby.slice(0, 8).map(renderNode).join("") || `<div class="empty-state">No nearby nodes.</div>`}</div><div class="graph-lane"><h3>Dependencies</h3>${(graph.edges || []).map((edge) => `<span class="queue-badge">${escapeHtml(edge.source)} -> ${escapeHtml(edge.target)}</span>`).join("") || `<div class="empty-state">No recorded edges.</div>`}</div>`;
    refs.graphCanvas.querySelectorAll("[data-graph-name]").forEach((button) => {
      button.addEventListener("click", () => {
        const name = button.dataset.graphName;
        const match = state.items.find((item) => item.name === name);
        if (match) selectItem(match.key, false);
      });
    });
  }

  function selectGraphItemFromFrame(id, revealOnMobile = false) {
    const match = state.items.find((item) => item.graphId === id || item.name === id);
    if (!match) return;
    if (match.key !== state.selectedKey) {
      selectItem(match.key, false);
      window.requestAnimationFrame(() => {
        const row = [...refs.reviewQueue.querySelectorAll("[data-item-key]")]
          .find((candidate) => candidate.dataset.itemKey === match.key);
        row?.scrollIntoView({ block: "nearest", inline: "nearest" });
      });
    }
    if (revealOnMobile && isMobile()) setMobileView("review");
  }

  function loadedGraphBookSlug() {
    try {
      const pathname = refs.graphFrame.contentWindow?.location?.pathname || "";
      const match = pathname.match(/\/api\/books\/([^/]+)\/evidence\/graph(?:\/|$)/);
      return match ? decodeURIComponent(match[1]) : "";
    } catch (_) {
      return "";
    }
  }

  function graphScopePreference(slug) {
    const inMemory = state.graphScopeByBook.get(slug);
    if (inMemory === "full" || inMemory === "focus") return inMemory;
    try {
      const stored = localStorage.getItem(`reasbook-reviewer:graph-scope-v2:${slug}`);
      if (stored === "full" || stored === "focus") return stored;
    } catch (_) {
      // Per-book graph preferences are optional in restricted storage contexts.
    }
    return "focus";
  }

  function rememberGraphScope(slug, mode) {
    if (!slug) return;
    const normalized = mode === "focus" ? "focus" : "full";
    state.graphScopeByBook.set(slug, normalized);
    try {
      localStorage.setItem(`reasbook-reviewer:graph-scope-v2:${slug}`, normalized);
    } catch (_) {
      // The in-memory preference still keeps books isolated for this session.
    }
  }

  function graphDependencyPreference(slug) {
    const inMemory = state.graphDependencyByBook.get(slug);
    if (inMemory === "all") return "statement-edges";
    if (["statement-edges", "statement", "proof"].includes(inMemory)) return inMemory;
    try {
      const stored = localStorage.getItem(`reasbook-reviewer:graph-dependencies:${slug}`);
      if (stored === "all") return "statement-edges";
      if (["statement-edges", "statement", "proof"].includes(stored)) return stored;
    } catch (_) {
      // Per-book graph preferences are optional in restricted storage contexts.
    }
    return "proof";
  }

  function rememberGraphDependency(slug, mode) {
    if (!slug) return;
    const normalized = ["statement-edges", "statement", "proof"].includes(mode) ? mode : "proof";
    state.graphDependencyByBook.set(slug, normalized);
    try {
      localStorage.setItem(`reasbook-reviewer:graph-dependencies:${slug}`, normalized);
    } catch (_) {
      // The in-memory preference still keeps books isolated for this session.
    }
  }

  function applyOriginalGraphDependencyFilter(frameDocument, loadedSlug, mode) {
    if (/^curated/.test(state.context?.graph?.generation?.mode || "")) return;
    const normalized = ["statement-edges", "statement", "proof"].includes(mode) ? mode : "proof";
    frameDocument.body.dataset.dependencyFilter = normalized;
    rememberGraphDependency(loadedSlug, normalized);
    frameDocument.querySelectorAll("[data-dependency-mode]").forEach((button) => {
      const active = button.dataset.dependencyMode === normalized;
      button.classList.toggle("active", active);
      button.setAttribute("aria-pressed", String(active));
    });
    // The renderer filters adjacency before computing depth or either layout.
    // Its setter is idempotent, including calls from the SVG mutation observer.
    frameDocument.defaultView?.__reasbookTheoremMapDependencies?.setMode(normalized);
  }

  function enforceGraphScope(frameWindow, frameDocument, loadedSlug, attempt = 0) {
    if (loadedGraphBookSlug() !== loadedSlug) return;
    const fullButton = frameDocument.getElementById("fullGraphButton");
    const focusButton = frameDocument.getElementById("focusGraphButton");
    const initialized = fullButton?.classList.contains("active") || focusButton?.classList.contains("active");
    const rendererReady = initialized && Boolean(frameDocument.querySelector("[data-node-id]"));
    if (!rendererReady) {
      if (attempt < 200) frameWindow.setTimeout(() => enforceGraphScope(frameWindow, frameDocument, loadedSlug, attempt + 1), 25);
      return;
    }
    const pendingBook = refs.graphFrame.dataset.graphScopeBook || "";
    const pendingScope = refs.graphFrame.dataset.graphScopeDesired || "";
    const rememberedScope = pendingBook === loadedSlug && (pendingScope === "full" || pendingScope === "focus")
      ? pendingScope
      : graphScopePreference(loadedSlug);
    rememberGraphScope(loadedSlug, rememberedScope);
    const scopeButton = rememberedScope === "focus" ? focusButton : fullButton;
    if (scopeButton && !scopeButton.classList.contains("active")) scopeButton.click();
    if (pendingBook === loadedSlug) refs.graphFrame.dataset.graphScopePending = "false";
    compactOriginalGraphNodes(frameDocument);
    syncGraphScopeControls();
  }

  function syncGraphScopeControls() {
    const frameDocument = refs.graphFrame.contentDocument;
    const fullButton = frameDocument?.getElementById("fullGraphButton");
    const focusButton = frameDocument?.getElementById("focusGraphButton");
    const loadedSlug = loadedGraphBookSlug();
    const initialized = fullButton?.classList.contains("active") || focusButton?.classList.contains("active");
    const scopePending = refs.graphFrame.dataset.graphScopeBook === loadedSlug
      && refs.graphFrame.dataset.graphScopePending === "true";
    if (loadedSlug !== state.selectedSlug || !initialized || scopePending) return;
    const focus = focusButton.classList.contains("active");
    rememberGraphScope(loadedSlug, focus ? "focus" : "full");
  }

  function compactOriginalGraphNodes(frameDocument) {
    // A new book replaces state.items. Reuse its lookup between graph updates
    // instead of doing one linear catalogue scan for every rendered node.
    if (compactOriginalGraphNodes.items !== state.items) {
      compactOriginalGraphNodes.items = state.items;
      compactOriginalGraphNodes.lookup = new Map();
      state.items.forEach((item) => {
        if (item.graphId) compactOriginalGraphNodes.lookup.set(item.graphId, item);
        if (item.name) compactOriginalGraphNodes.lookup.set(item.name, item);
      });
    }
    frameDocument.querySelectorAll("[data-node-id]").forEach((node) => {
      const id = node.dataset.nodeId || "";
      const item = compactOriginalGraphNodes.lookup.get(id);
      const compact = item
        ? [item.label, item.name].filter(Boolean).join(" / ")
        : String(node.querySelector(".node-label")?.textContent || id).trim();
      const title = node.querySelector("title");
      if (title && title.textContent !== compact) title.textContent = compact;
      if (compact && node.getAttribute("aria-label") !== compact) node.setAttribute("aria-label", compact);
    });
  }

  function installOriginalGraphLayoutControls(frameWindow, frameDocument, loadedSlug, attempt = 0) {
    if (loadedGraphBookSlug() !== loadedSlug) return;
    const layoutApi = frameWindow.__reasbookTheoremMapLayout;
    const toolbar = frameDocument.querySelector(".graph-toolbar");
    if (!layoutApi || !toolbar) {
      if (attempt < 200) {
        frameWindow.setTimeout(
          () => installOriginalGraphLayoutControls(frameWindow, frameDocument, loadedSlug, attempt + 1),
          25,
        );
      }
      return;
    }
    let controls = frameDocument.getElementById("reviewerLayoutControls");
    if (!controls) {
      controls = frameDocument.createElement("div");
      controls.id = "reviewerLayoutControls";
      controls.className = "segmented reviewer-layout-controls";
      controls.setAttribute("role", "group");
      controls.setAttribute("aria-label", "Graph layout");
      [
        ["layered", "Layered"],
        ["natural", "Natural"],
      ].forEach(([mode, label]) => {
        const button = frameDocument.createElement("button");
        button.type = "button";
        button.dataset.layoutMode = mode;
        button.textContent = label;
        controls.appendChild(button);
      });
      toolbar.appendChild(controls);
    }
    const sync = () => {
      const current = layoutApi.getMode() === "natural" ? "natural" : "layered";
      controls.querySelectorAll("[data-layout-mode]").forEach((button) => {
        const active = button.dataset.layoutMode === current;
        button.classList.toggle("active", active);
        button.setAttribute("aria-pressed", String(active));
      });
    };
    if (controls.dataset.bound !== "true") {
      controls.addEventListener("click", (event) => {
        const button = event.target.closest?.("[data-layout-mode]");
        if (button) layoutApi.setMode(button.dataset.layoutMode);
      });
      frameWindow.addEventListener("reasbook-layoutchange", sync);
      controls.dataset.bound = "true";
    }
    sync();
  }

  function installOriginalGraphDependencyControls(frameDocument, loadedSlug) {
    const toolbar = frameDocument.querySelector(".graph-toolbar");
    if (!toolbar) return;
    // Curated edges have no compiled statement/proof classification. Do not
    // mislabel the original hand-reviewed union as proof evidence.
    if (/^curated/.test(state.context?.graph?.generation?.mode || "")) return;
    let controls = frameDocument.getElementById("reviewerDependencyControls");
    if (!controls) {
      controls = frameDocument.createElement("div");
      controls.id = "reviewerDependencyControls";
      controls.className = "segmented reviewer-dependency-controls";
      controls.setAttribute("role", "group");
      controls.setAttribute("aria-label", "Dependency evidence");
      [
        ["statement-edges", "Stmt edges"],
        ["statement", "Stmt"],
        ["proof", "Proof"],
      ].forEach(([mode, label]) => {
        const button = frameDocument.createElement("button");
        button.type = "button";
        button.dataset.dependencyMode = mode;
        button.title = {
          "statement-edges": "Keep statement and proof/body dependency nodes within Layers; show only statement edges",
          statement: "Dependencies in declaration types/statements",
          proof: "Dependencies in proofs/definition bodies; may overlap with statement dependencies",
        }[mode];
        button.innerHTML = `<span class="dependency-swatch dependency-swatch-${mode}" aria-hidden="true"></span>${label}`;
        controls.appendChild(button);
      });
      controls.addEventListener("click", (event) => {
        const button = event.target.closest?.("[data-dependency-mode]");
        if (button) applyOriginalGraphDependencyFilter(frameDocument, loadedSlug, button.dataset.dependencyMode);
      });
      toolbar.appendChild(controls);
    }
    applyOriginalGraphDependencyFilter(frameDocument, loadedSlug, graphDependencyPreference(loadedSlug));
  }

  function bindOriginalGraphFrame() {
    try {
      const frameWindow = refs.graphFrame.contentWindow;
      const frameDocument = refs.graphFrame.contentDocument;
      if (!frameWindow || !frameDocument) return;
      const loadedSlug = loadedGraphBookSlug();
      if (!loadedSlug || loadedSlug !== state.selectedSlug) return;
      const embedStyleId = "reasbook-reviewer-graph-embed-style";
      if (!frameDocument.getElementById(embedStyleId)) {
        const style = frameDocument.createElement("style");
        style.id = embedStyleId;
        style.textContent = `
          html, body { overflow: hidden !important; }
          #appShell, .app-shell { grid-template-columns: minmax(0, 1fr) !important; grid-template-rows: minmax(0, 1fr) !important; height: 100% !important; }
          #sidebar, .sidebar, #detailPanel, .detail-panel, .mobile-view-switch { display: none !important; }
          .toolbar-title { display: none !important; }
          .toolbar { min-height: 48px !important; padding: 6px 10px !important; justify-content: flex-end !important; }
          .toolbar-actions { width: 100% !important; min-width: 0 !important; gap: 6px !important; justify-content: flex-start !important; flex-wrap: nowrap !important; overflow-x: auto !important; }
          .graph-scope-heading { width: auto; display: flex !important; align-items: center; gap: 8px; flex: 1 0 auto; min-width: max-content; }
          .graph-selection-label { font-size: 12px !important; }
          .graph-scope-heading > .segmented { display: inline-flex !important; }
          .graph-scope-heading > .segmented button { min-height: 30px !important; padding: 0 6px !important; font-size: 11px; }
          .toolbar-actions .icon-button { width: 28px; height: 30px; min-height: 30px; }
          .toolbar-actions .fit-button { width: 32px; }
          .graph-depth-control { gap: 4px; }
          .graph-depth-control select { width: 40px; }
          .main-panel { height: 100% !important; grid-template-rows: auto minmax(0, 1fr) !important; }
          .workspace { display: block !important; height: 100% !important; min-height: 0 !important; }
          .graph-panel { width: 100% !important; height: 100% !important; min-width: 0 !important; min-height: 0 !important; }
          .graph-viewport { width: 100% !important; min-width: 0 !important; min-height: 0 !important; }
          .graph-toolbar { min-height: 40px !important; height: auto !important; flex-wrap: wrap !important; gap: 5px 8px !important; padding: 5px 10px !important; }
          .graph-stats { min-width: 0 !important; overflow: hidden !important; white-space: nowrap !important; }
          .legend { display: none !important; }
          .reviewer-layout-controls { flex: 0 0 auto !important; margin-left: auto !important; }
          .reviewer-layout-controls button { min-height: 28px !important; padding: 0 9px !important; }
          .reviewer-dependency-controls { flex: 0 0 auto !important; }
          .reviewer-dependency-controls button { display: inline-flex !important; align-items: center !important; gap: 5px !important; min-height: 28px !important; padding: 0 8px !important; }
          .dependency-swatch { width: 10px; height: 3px; border-radius: 1px; background: #aab5bf; }
          .dependency-swatch-statement { background: #7654a6; }
          .dependency-swatch-statement-edges { background: #7654a6; }
          .dependency-swatch-proof { background: #28768a; }
          @media (max-width: 560px) {
            .reviewer-dependency-controls { margin-left: auto !important; }
            .reviewer-dependency-controls button { padding: 0 7px !important; }
          }
        `;
        frameDocument.head.appendChild(style);
      }
      const observerMarker = "__reasbookReviewerGraphCopyObserver";
      if (!frameWindow[observerMarker]) {
        const scene = frameDocument.getElementById("graphScene") || frameDocument.body;
        let pending = false;
        const observer = new frameWindow.MutationObserver(() => {
          if (pending) return;
          pending = true;
          frameWindow.requestAnimationFrame(() => {
            pending = false;
            if (loadedGraphBookSlug() !== loadedSlug) return;
            compactOriginalGraphNodes(frameDocument);
            applyOriginalGraphDependencyFilter(frameDocument, loadedSlug, graphDependencyPreference(loadedSlug));
          });
        });
        observer.observe(scene, { childList: true, subtree: true });
        frameWindow[observerMarker] = observer;
      }
      const syncSelectedNode = () => {
        const id = decodeURIComponent(String(frameWindow.location.hash || "").replace(/^#/, ""));
        if (id) selectGraphItemFromFrame(id);
      };
      const marker = "__reasbookReviewerGraphBound";
      if (!frameWindow[marker]) {
        frameWindow.addEventListener("hashchange", syncSelectedNode);
        frameDocument.addEventListener("click", (event) => {
          const scopeButton = event.target?.closest?.("#fullGraphButton, #focusGraphButton");
          if (scopeButton) frameWindow.setTimeout(syncGraphScopeControls, 0);
          const node = event.target?.closest?.("[data-node-id]");
          if (node?.dataset.nodeId) frameWindow.setTimeout(() => selectGraphItemFromFrame(node.dataset.nodeId, true), 0);
        }, true);
        frameDocument.addEventListener("keydown", (event) => {
          if (event.key !== "Enter" && event.key !== " ") return;
          const node = event.target?.closest?.("[data-node-id]");
          if (node?.dataset.nodeId) frameWindow.setTimeout(() => selectGraphItemFromFrame(node.dataset.nodeId, true), 0);
        }, true);
        frameWindow[marker] = true;
      }
      compactOriginalGraphNodes(frameDocument);
      syncSelectedNode();
      syncGraphScopeControls();
      installOriginalGraphLayoutControls(frameWindow, frameDocument, loadedSlug);
      installOriginalGraphDependencyControls(frameDocument, loadedSlug);
      enforceGraphScope(frameWindow, frameDocument, loadedSlug);
    } catch (_) {
      // The evidence frame is optional; a sandbox/browser policy may deny access.
    }
  }

  function bindDocsFrame() {
    try {
      const frameDocument = refs.docsFrame.contentDocument;
      if (!frameDocument) return;
      const styleId = "reasbook-reviewer-docs-embed-style";
      if (!frameDocument.getElementById(styleId)) {
        const style = frameDocument.createElement("style");
        style.id = styleId;
        style.textContent = `
          .reasbook-reviewer-target { outline: 2px solid #3157c8 !important; outline-offset: 4px !important; background: rgba(233, 237, 251, .55) !important; }
        `;
        frameDocument.head.appendChild(style);
      }
      focusDocsDeclaration();
    } catch (_) {
      // The evidence frame is optional; a sandbox/browser policy may deny access.
    }
  }

  function bindVersoFrame() {
    try {
      const frameDocument = refs.versoFrame.contentDocument;
      if (!frameDocument) return;
      if (!frameDocument.getElementById("reasbook-reviewer-verso-embed-style")) {
        const style = frameDocument.createElement("style");
        style.id = "reasbook-reviewer-verso-embed-style";
        style.textContent = `
          html, body { width: 100% !important; min-width: 0 !important; margin: 0 !important; overflow-x: hidden !important; }
          header, #sidebar-nav-root { display: none !important; }
          div.main { width: 100% !important; max-width: none !important; margin: 0 !important; }
          div.main > .wrap { width: 100% !important; max-width: 920px !important; margin: 0 auto !important; padding: 24px clamp(16px, 4vw, 48px) 72px !important; box-sizing: border-box !important; }
          div.main article { width: 100% !important; max-width: 780px !important; margin: 0 auto !important; overflow-wrap: anywhere !important; }
          div.main article h1 { font-size: clamp(1.35rem, 3vw, 2.15rem) !important; line-height: 1.18 !important; overflow-wrap: anywhere !important; }
          code.hl.lean.block { display: block !important; max-width: 100% !important; overflow-x: auto !important; white-space: pre-wrap !important; overflow-wrap: anywhere !important; line-height: 1.55 !important; }
          code.hl.lean.inline { white-space: normal !important; overflow-wrap: anywhere !important; }
          .declaration, .declaration > * { max-width: 100% !important; overflow-wrap: anywhere !important; }
          table, img, svg, pre { max-width: 100% !important; height: auto !important; }
          .reasbook-reviewer-target { outline: 2px solid #3157c8 !important; outline-offset: 4px !important; background: rgba(233, 237, 251, .55) !important; }
        `;
        frameDocument.head.appendChild(style);
      }
      focusVersoDeclaration();
      window.setTimeout(focusVersoDeclaration, 120);
    } catch (_) {
      // The evidence frame is optional; a sandbox/browser policy may deny access.
    }
  }

  async function handleEvidenceMessage(event) {
    if (event.origin !== window.location.origin || event.source !== refs.docsFrame.contentWindow) return;
    const data = event.data;
    if (!data || data.type !== "reasbook-source-jump" || typeof data.sourcePath !== "string") return;
    const line = Number(data.line) || 1;
    const candidates = state.items.filter((item) => item.sourcePath === data.sourcePath);
    const item = candidates.sort((left, right) => Math.abs(Number(left.line || 0) - line) - Math.abs(Number(right.line || 0) - line))[0];
    if (!item) return;
    const returnView = currentEvidenceHistoryKind();
    const returnUrl = returnView ? evidenceFrameLocation(returnView) : "";
    await selectItem(item.key, false);
    state.evidenceReturn = returnView ? { view: returnView, url: returnUrl } : null;
    setEvidenceView("source");
  }

  function renderSource() {
    if (!state.context) {
      refs.sourceMeta.textContent = state.selectedKey ? "Loading source…" : "";
      refs.sourceCode.textContent = state.selectedKey ? "Loading source…" : "Select a statement to load Lean source.";
      return;
    }
    const source = state.context?.source;
    if (!source?.available) {
      refs.sourceMeta.textContent = "Lean source is not available in the selected release cache.";
      refs.sourceCode.textContent = "No source snapshot available.";
      return;
    }
    refs.sourceMeta.textContent = `${source.path} / lines ${source.start}-${source.end} of ${source.totalLines}`;
    refs.sourceCode.replaceChildren();
    const code = document.createElement("code");
    source.lines.forEach((line) => {
      const row = document.createElement("span");
      row.className = `source-line${line.target ? " target" : ""}`;
      const number = document.createElement("span");
      number.className = "source-line-number";
      number.textContent = String(line.number);
      const text = document.createElement("span");
      text.className = "source-line-text";
      text.innerHTML = highlightLean(line.text || " ");
      row.append(number, text);
      code.append(row);
    });
    refs.sourceCode.append(code);
  }

  function renderFrames() {
    const resources = state.context?.resources || {};
    const item = selectedEvidenceItem();
    const stacksMode = isStacksBook();
    const docsUrl = resources.docs?.available ? resources.docs.url || "" : "";
    const versoUrl = !stacksMode && resources.verso?.available ? resources.verso.url || "" : "";
    const waiting = Boolean(state.selectedKey && !state.context);
    const failed = Boolean(state.context?.error);
    refs.docsEmpty.textContent = waiting ? "Checking documentation for this statement…" : failed ? "Unable to check documentation. Select the statement again to retry." : "Documentation is unavailable for this statement in the selected release.";
    refs.versoEmpty.textContent = waiting ? "Checking Verso for this declaration…" : failed ? "Unable to check Verso. Select the declaration again to retry." : "A generated Verso page is unavailable for this declaration in the selected release.";
    refs.versoTab.hidden = stacksMode;
    if (stacksMode && state.evidenceView === "verso") setEvidenceView("graph");
    refs.docsFrame.hidden = !docsUrl;
    refs.docsEmpty.hidden = Boolean(docsUrl);
    refs.versoFrame.hidden = !versoUrl;
    refs.versoEmpty.hidden = Boolean(versoUrl);
    if (docsUrl) {
      const docsTarget = new URL(appUrl(docsUrl), window.location.origin);
      if (item?.name) docsTarget.hash = encodeURIComponent(item.name);
      const absoluteDocsUrl = docsTarget.href;
      if (evidenceFrameLocation("docs") !== absoluteDocsUrl) {
        resetEvidenceFrameHistory("docs", absoluteDocsUrl);
        refs.docsFrame.src = absoluteDocsUrl;
        window.setTimeout(focusDocsDeclaration, 0);
      } else {
        focusDocsDeclaration();
      }
    } else {
      resetEvidenceFrameHistory("docs", "");
    }
    if (versoUrl) {
      const absoluteVersoUrl = new URL(appUrl(versoUrl), window.location.origin).href;
      if (evidenceFrameLocation("verso") !== absoluteVersoUrl) {
        resetEvidenceFrameHistory("verso", absoluteVersoUrl);
        refs.versoFrame.src = appUrl(versoUrl);
        window.setTimeout(focusVersoDeclaration, 0);
      } else {
        focusVersoDeclaration();
      }
    } else {
      resetEvidenceFrameHistory("verso", "");
    }
    updateEvidenceHistoryControls();
  }

  function renderReviewerCards() {
    const rows = reviewRows(state.selectedKey).filter((row) => row.status !== "unreviewed");
    refs.reviewerCards.innerHTML = rows.length ? rows.map((row) => `<article class="reviewer-card"><header><span>${escapeHtml(statusLabel(row.status))} / ${escapeHtml(row.reviewer || "Reviewer")}</span><span>${escapeHtml(row.updatedAt || "")}</span></header>${row.comment ? `<p>${escapeHtml(row.comment)}</p>` : ""}</article>`).join("") : `<div class="empty-state">No saved decisions yet.</div>`;
  }

  function renderHistory() {
    const history = state.history;
    if (!history) {
      refs.historyList.textContent = "Open this section to load history.";
      return;
    }
    if (history.loading) {
      refs.historyList.textContent = "Loading history…";
      return;
    }
    if (history.error) {
      refs.historyList.textContent = history.error;
      return;
    }
    refs.historyList.innerHTML = history.events.length
      ? history.events.map((event) => `<article class="history-item"><header><span>${escapeHtml(statusLabel(event.status))} / ${escapeHtml(event.reviewer || "Reviewer")}</span><span>${escapeHtml(event.createdAt || "")}</span></header>${event.comment ? `<p>${escapeHtml(event.comment)}</p>` : ""}</article>`).join("")
      : `<div class="empty-state">No review history yet.</div>`;
  }

  function renderLeanContract() {
    const lean = state.context?.lean;
    if (!lean?.available) {
      refs.leanContract.hidden = true;
      return;
    }
    refs.leanContract.hidden = false;
    const fallback = `${lean.signature || `${lean.kind || "declaration"} ${lean.name || ""}`}${lean.value ? ` := ${lean.value}` : ""}`;
    refs.leanCode.innerHTML = `<code>${highlightLean(lean.code || fallback)}</code>`;
  }

  function renderRelations() {
    const graph = state.context?.graph;
    if (!graph?.available) {
      refs.relationSection.hidden = true;
      return;
    }
    const upstream = Array.isArray(graph.upstream) ? graph.upstream : [];
    const downstream = Array.isArray(graph.downstream) ? graph.downstream : [];
    const sourceFallback = graph.generation?.mode === "source-fallback";
    const curated = graph.generation?.mode === "curated" || graph.generation?.mode === "curated-static";
    const sourceOnly = graph.selectedDependencyEvidence === "source-only";
    const evidenceUnavailable = sourceFallback || sourceOnly;
    const mode = state.relationDependencyMode === "statement" ? "statement" : "proof";
    const matchesMode = (node) => {
      if (curated) return true;
      const kinds = Array.isArray(node.kinds) ? node.kinds : [];
      return kinds.includes(mode) || (mode === "proof" && kinds.includes("unclassified"));
    };
    const visibleUpstream = upstream.filter(matchesMode);
    const visibleDownstream = downstream.filter(matchesMode);
    refs.relationSection.hidden = false;
    refs.relationStats.textContent = evidenceUnavailable
      ? sourceOnly ? "source inventory only" : "source only · no compiled edges"
      : `${visibleUpstream.length}/${upstream.length} upstream · ${visibleDownstream.length}/${downstream.length} downstream`;
    refs.relationSection.classList.toggle("source-fallback", evidenceUnavailable);
    refs.relationFilters.hidden = curated;
    refs.relationFilters.querySelectorAll("[data-relation-mode]").forEach((button) => {
      const active = button.dataset.relationMode === mode;
      button.classList.toggle("active", active);
      button.setAttribute("aria-pressed", String(active));
    });
    const kindLabel = (kind) => ({
      statement: "statement",
      proof: "proof/body",
      unclassified: curated ? "curated" : "legacy",
    }[kind] || kind);
    const renderList = (nodes, emptyText) => nodes.length
      ? nodes.map((node) => {
        const kinds = Array.isArray(node.kinds) ? node.kinds : [];
        const badges = kinds.map((kind) => `<span class="relation-kind ${escapeHtml(kind)}">${escapeHtml(kindLabel(kind))}</span>`).join("");
        return `<button type="button" class="relation-link" data-relation-name="${escapeHtml(node.declaration || "")}"><span class="relation-link-heading"><strong>${escapeHtml(node.label || node.declaration || "Untitled")}</strong>${badges}</span>${node.title ? `<span class="relation-copy">${escapeHtml(node.title)}</span>` : ""}</button>`;
      }).join("")
      : `<div class="relation-empty">${emptyText}</div>`;
    const emptyText = evidenceUnavailable
      ? sourceOnly
        ? "This declaration was not imported by the compiled project root; no dependency edges are inferred from source text."
        : "Compiled dependency evidence is unavailable for this release."
      : "No declarations recorded.";
    const filteredEmpty = evidenceUnavailable ? emptyText : `No ${mode === "statement" ? "statement" : "proof/body"} dependencies recorded.`;
    refs.upstreamRelations.innerHTML = renderList(visibleUpstream, filteredEmpty);
    refs.downstreamRelations.innerHTML = renderList(visibleDownstream, filteredEmpty);
    refs.relationSection.querySelectorAll("[data-relation-name]").forEach((button) => {
      button.addEventListener("click", () => {
        const name = button.dataset.relationName;
        const match = state.items.find((candidate) => candidate.name === name || candidate.graphId === name);
        if (match) selectItem(match.key, false);
      });
    });
  }

  function renderDetail() {
    const item = state.items.find((value) => value.key === state.selectedKey);
    if (!item) {
      refs.detailEmpty.hidden = false;
      refs.detailContent.hidden = true;
      refs.leanContract.hidden = true;
      refs.statementPanel.hidden = true;
      return;
    }
    refs.detailEmpty.hidden = true;
    refs.detailContent.hidden = false;
    const aggregate = aggregateReview(item.key);
    const statement = statementParts(item);
    refs.detailKind.hidden = true;
    refs.detailTitle.textContent = displayStatementHeading(statement.heading || item.label || itemKind(item));
    refs.detailStatus.textContent = statusLabel(aggregate.status);
    refs.detailStatus.className = `status-badge ${statusClass(aggregate.status)}`;
    refs.detailTags.innerHTML = item.hasSorry
      ? `<span class="meta-chip" style="color:var(--bad)">contains sorry</span>`
      : "";
    refs.detailTags.hidden = !item.hasSorry;
    refs.detailStatementLabel.textContent = "";
    refs.detailStatementLabel.hidden = true;
    refs.detailStatement.hidden = !statement.body;
    refs.detailStatement.innerHTML = statement.body ? statementMathHtml(statement.body) : "";
    if (statement.body) typesetMath(refs.detailStatement);
    renderStatementSource(item);
    renderRelations();
    renderLeanContract();
    renderReviewerCards();
    const draft = state.draft || mineReview(item.key);
    refs.reviewControls.hidden = false;
    const canSave = Boolean(state.session?.canSave);
    refs.reviewAccessNotice.hidden = canSave;
    if (!canSave) {
      refs.reviewAccessNotice.innerHTML = state.session?.canLogin
        ? `<span>Sign in to add a decision or comment.</span><a class="button button-primary" href="${escapeHtml(refs.loginLink.href)}">Sign in</a>`
        : `<span>Reviewing is read-only because authentication is not configured for this deployment.</span>`;
    }
    refs.reviewComment.value = draft.comment || "";
    refs.reviewComment.disabled = !canSave;
    document.querySelectorAll("[data-decision]").forEach((button) => {
      button.disabled = !canSave;
      button.classList.toggle("active", button.dataset.decision === (draft.status || "unreviewed"));
    });
    refs.saveReview.disabled = !canSave || !state.draft || !state.draft.dirty;
    refs.saveState.textContent = !canSave ? "Sign in required to save." : state.draft?.dirty ? "Unsaved changes." : state.draft?.savedAt ? `Saved ${state.draft.savedAt}` : "No unsaved changes.";
    refs.saveState.className = `save-state${state.draft?.error ? " error" : state.draft?.savedAt ? " saved" : ""}`;
    renderHistory();
  }

  async function loadContext(item) {
    const slug = state.selectedSlug;
    const key = item.key;
    const request = ++state.contextRequest;
    try {
      const context = await api(`/api/books/${encodeURIComponent(slug)}/context/${encodeURIComponent(key)}`);
      if (request !== state.contextRequest || state.selectedSlug !== slug || state.selectedKey !== key) return;
      state.context = context;
      renderBookOverview(); renderGraph(); renderSource(); renderFrames(); renderDetail();
    } catch (error) {
      if (request !== state.contextRequest || state.selectedSlug !== slug || state.selectedKey !== key) return;
      refs.graphMessage.textContent = error.message;
      state.context = { error: error.message };
      renderBookOverview(); renderGraph(); renderSource(); renderFrames(); renderDetail();
      refs.graphMessage.textContent = error.message;
    }
  }

  async function selectItem(key, moveToEvidence = false) {
    const item = state.items.find((value) => value.key === key);
    if (!item) return;
    state.contextRequest += 1;
    state.historyRequest += 1;
    state.selectedKey = key;
    state.evidenceReturn = null;
    state.context = null;
    state.draft = null;
    state.history = null;
    state.statementSourceOpen = false;
    if (state.statementCopyTimer) window.clearTimeout(state.statementCopyTimer);
    state.statementCopyTimer = null;
    refs.copyStatementSource.textContent = "Copy source";
    refs.historySection.open = false;
    refs.relationSection.open = false;
    renderBookOverview(); renderQueue(); renderGraph(); renderSource(); renderFrames(); renderDetail();
    if (moveToEvidence && isMobile()) setMobileView("evidence");
    history.replaceState({}, "", `${appUrl(`/books/${encodeURIComponent(state.selectedSlug)}/`)}?item=${encodeURIComponent(key)}`);
    await loadContext(item);
  }

  async function loadHistory() {
    if (!state.selectedKey || state.history?.loading) return;
    const slug = state.selectedSlug;
    const key = state.selectedKey;
    const request = ++state.historyRequest;
    state.history = { loading: true, events: [] };
    renderDetail();
    try {
      const payload = await api(`/api/books/${encodeURIComponent(slug)}/reviews/${encodeURIComponent(key)}/history`);
      if (request !== state.historyRequest || state.selectedSlug !== slug || state.selectedKey !== key) return;
      state.history = { loading: false, events: payload.events || [] };
      renderDetail();
    } catch (error) {
      if (request !== state.historyRequest || state.selectedSlug !== slug || state.selectedKey !== key) return;
      state.history = { loading: false, error: error.message, events: [] };
      renderDetail();
    }
  }

  function updateDraft(status, comment) {
    const saved = mineReview(state.selectedKey);
    const nextStatus = status ?? state.draft?.status ?? saved.status;
    const nextComment = comment ?? state.draft?.comment ?? saved.comment;
    state.draft = {
      status: nextStatus,
      comment: nextComment,
      dirty: nextStatus !== saved.status || nextComment !== saved.comment,
      baseRevision: saved.revision || 0,
      error: "",
      savedAt: "",
    };
    renderDetail();
  }

  async function csrfToken() {
    if (state.csrf) return state.csrf;
    const payload = await api("/api/auth/csrf");
    state.csrf = payload.csrf_token;
    return state.csrf;
  }

  function clientId() {
    const key = "reasbook-reviewer:client-id";
    let value = localStorage.getItem(key);
    if (!value) { value = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`; localStorage.setItem(key, value); }
    return value;
  }

  async function saveReview() {
    if (!state.book || !state.selectedKey || !state.draft?.dirty || !state.session?.canSave) return;
    refs.saveReview.disabled = true; refs.saveState.textContent = "Saving...";
    try {
      const token = await csrfToken();
      const payload = await api(`/api/books/${encodeURIComponent(state.selectedSlug)}/reviews/${encodeURIComponent(state.selectedKey)}`, {
        method: "POST", headers: { "Content-Type": "application/json", "X-CSRF-Token": token },
        body: JSON.stringify({ status: state.draft.status, comment: state.draft.comment, clientId: clientId(), baseRevision: state.draft.baseRevision }),
      });
      mergeReviews([payload.review]);
      state.draft = { ...state.draft, dirty: false, savedAt: payload.review.updatedAt || "now", baseRevision: payload.review.revision, error: "" };
      state.history = null; setSync("Synced", "ok"); renderQueue(); renderBookOverview(); renderDetail();
    } catch (error) {
      if (/CSRF|authentication|401/i.test(error.message)) state.csrf = null;
      state.draft = { ...state.draft, error: error.message };
      refs.saveState.textContent = error.message; refs.saveState.className = "save-state error"; refs.saveReview.disabled = false;
    }
  }

  async function selectBook(slug, push = true) {
    if (!state.catalog.some((book) => book.slug === slug)) return;
    if (state.selectedSlug && state.selectedSlug !== slug && state.draft?.dirty && !window.confirm("Discard unsaved review changes?")) return;
    const request = ++state.bookRequest;
    state.contextRequest += 1;
    state.historyRequest += 1;
    state.selectedSlug = slug; state.book = null; state.items = []; state.selectedKey = ""; state.context = null; state.draft = null; state.history = null; state.evidenceReturn = null; state.reviewLimit = 80; state.reviews.clear();
    if (push) history.pushState({}, "", appUrl(`/books/${encodeURIComponent(slug)}/`));
    renderCatalog(); renderToolbar(); renderBookOverview(); renderQueue(); renderGraph(); renderSource(); renderFrames(); renderDetail(); setSync("Loading", "warn");
    refs.bookOverview.setAttribute("aria-busy", "true");
    try {
      const [book, reviewPayload, resources] = await Promise.all([
        api(`/api/books/${encodeURIComponent(slug)}`),
        api(`/api/books/${encodeURIComponent(slug)}/reviews`),
        api(`/api/books/${encodeURIComponent(slug)}/resources`),
      ]);
      if (request !== state.bookRequest || state.selectedSlug !== slug) return;
      state.book = book; state.items = Array.isArray(book.items) ? book.items : []; state.reviewRevision = Number(reviewPayload.revision || 0); mergeReviews(reviewPayload.reviews || []); state.context = { resources: resources.resources };
      updateTypeFilter(); renderToolbar(); renderBookOverview(); renderQueue(); refs.bookOverview.setAttribute("aria-busy", "false");
      const query = new URLSearchParams(window.location.search); const initialKey = query.get("item");
      const item = state.items.find((value) => value.key === initialKey) || state.items[0];
      if (item) await selectItem(item.key, false);
      if (request !== state.bookRequest || state.selectedSlug !== slug) return;
      if (push && isMobile()) setMobileView("queue");
      setSync("Synced", "ok");
    } catch (error) {
      if (request !== state.bookRequest || state.selectedSlug !== slug) return;
      refs.bookOverview.setAttribute("aria-busy", "false");
      setSync("Load failed", "warn"); refs.graphMessage.textContent = error.message; renderBookOverview(); renderQueue();
    }
  }

  async function pollReviews() {
    if (!state.selectedSlug) return;
    const slug = state.selectedSlug;
    const bookRequest = state.bookRequest;
    try {
      const payload = await api(`/api/books/${encodeURIComponent(slug)}/reviews?since=${state.reviewRevision}`);
      if (state.selectedSlug !== slug || state.bookRequest !== bookRequest) return;
      if (Array.isArray(payload.reviews) && payload.reviews.length) { mergeReviews(payload.reviews); renderQueue(); renderBookOverview(); renderReviewerCards(); }
      state.reviewRevision = Number(payload.revision || state.reviewRevision); setSync("Synced", "ok");
    } catch (_) { setSync("Offline", "warn"); }
  }

  function alignReaderControls() {
    const catalog = document.querySelector(".catalog-controls");
    const queue = document.querySelector(".item-toolbar");
    const catalogContent = catalog.querySelector(".catalog-controls-content");
    const queueContent = queue.querySelector(".item-toolbar-content");
    let scheduled = false;
    const sync = () => {
      scheduled = false;
      if (isMobile() || state.catalogCollapsed || state.queueCollapsed) return;
      const naturalHeight = (outer, inner) => {
        const css = getComputedStyle(outer);
        return inner.getBoundingClientRect().height + ["paddingTop", "paddingBottom", "borderTopWidth", "borderBottomWidth"]
          .reduce((sum, key) => sum + (parseFloat(css[key]) || 0), 0);
      };
      const catalogTop = catalog.getBoundingClientRect().top;
      const queueTop = queue.getBoundingClientRect().top;
      const bottom = Math.max(catalogTop + naturalHeight(catalog, catalogContent), queueTop + naturalHeight(queue, queueContent));
      refs.appShell.style.setProperty("--catalog-controls-height", `${bottom - catalogTop}px`);
      refs.appShell.style.setProperty("--queue-controls-height", `${bottom - queueTop}px`);
    };
    const schedule = () => {
      if (!scheduled) { scheduled = true; requestAnimationFrame(sync); }
    };
    // Observe intrinsic content, not the synchronized outer heights, to avoid
    // a resize feedback loop. Covers wrapped titles, filters, and pane dragging.
    const observer = new ResizeObserver(schedule);
    [catalogContent, queueContent].forEach((element) => observer.observe(element));
    window.addEventListener("resize", schedule);
    schedule();
  }

  function bindEvents() {
    alignReaderControls();
    refs.subjectOptions.insertAdjacentHTML("beforeend", Object.entries(SUBJECT_LABELS).map(([subject, label]) =>
      `<label class="subject-option"><input type="checkbox" value="${subject}" /> <span>${escapeHtml(label)}</span></label>`).join(""));
    refs.subjectOptions.addEventListener("change", (event) => {
      const input = event.target;
      if (!(input instanceof HTMLInputElement) || !Object.hasOwn(SUBJECT_LABELS, input.value)) return;
      if (input.checked) state.subjectFilters.add(input.value); else state.subjectFilters.delete(input.value);
      renderCatalog();
    });
    refs.clearSubjectFilters.addEventListener("click", () => {
      state.subjectFilters.clear();
      refs.subjectOptions.querySelectorAll("input").forEach((input) => { input.checked = false; });
      renderCatalog();
    });
    refs.toggleCatalog.addEventListener("click", () => setPanelCollapsed("catalog", !state.catalogCollapsed));
    refs.toggleQueue.addEventListener("click", () => setPanelCollapsed("queue", !state.queueCollapsed));
    refs.queueRailToggle.addEventListener("click", () => setPanelCollapsed("queue", !state.queueCollapsed));
    refs.queuePanelToggle.addEventListener("click", () => setPanelCollapsed("queue", !state.queueCollapsed));
    refs.catalogPanelToggle.addEventListener("click", () => setPanelCollapsed("catalog", !state.catalogCollapsed));
    refs.toggleReview.addEventListener("click", () => setPanelCollapsed("review", !state.reviewCollapsed));
    refs.reviewPanelToggle.addEventListener("click", () => setPanelCollapsed("review", !state.reviewCollapsed));
    refs.reviewRailToggle.addEventListener("click", () => setPanelCollapsed("review", !state.reviewCollapsed));
    bindPaneResizer(refs.catalogResize, "catalog");
    bindPaneResizer(refs.queueResize, "queue");
    bindPaneResizer(refs.reviewResize, "review");
    refs.loginLink.addEventListener("click", (event) => {
      if (refs.loginLink.getAttribute("aria-disabled") === "true") event.preventDefault();
    });
    refs.graphFrame.addEventListener("load", bindOriginalGraphFrame);
    refs.docsFrame.addEventListener("load", () => { bindDocsFrame(); bindEvidenceFrameHistory("docs"); });
    refs.versoFrame.addEventListener("load", () => { bindVersoFrame(); bindEvidenceFrameHistory("verso"); });
    refs.evidenceBack.addEventListener("click", () => navigateEvidenceHistory(currentEvidenceHistoryKind(), -1));
    refs.evidenceForward.addEventListener("click", () => navigateEvidenceHistory(currentEvidenceHistoryKind(), 1));
    window.addEventListener("mathjax-ready", () => typesetMath(refs.detailStatement));
    window.addEventListener("message", handleEvidenceMessage);
    refs.skipLink.addEventListener("click", (event) => {
      if (!isMobile() || state.mobileView !== "queue") return;
      event.preventDefault(); setMobileView("review"); requestAnimationFrame(() => refs.workspaceMain?.focus());
    });
    refs.mobileButtons.forEach((button) => button.addEventListener("click", () => setMobileView(button.dataset.mobileView)));
    refs.bookSearch.addEventListener("input", () => { state.bookSearch = refs.bookSearch.value; renderCatalog(); });
    refs.kindFilter.addEventListener("change", () => { state.kindFilter = refs.kindFilter.value; renderCatalog(); });
    refs.availabilityFilter.addEventListener("change", () => { state.availabilityFilter = refs.availabilityFilter.value; renderCatalog(); });
    refs.itemSearch.addEventListener("input", () => { state.itemSearch = refs.itemSearch.value; renderQueue(); });
    refs.itemTypeFilter.addEventListener("change", () => { state.itemTypeFilter = refs.itemTypeFilter.value; renderQueue(); });
    refs.itemSectionFilter.addEventListener("change", () => { state.itemSectionFilter = refs.itemSectionFilter.value; renderQueue(); });
    refs.reviewFilter.addEventListener("change", () => { state.reviewFilter = refs.reviewFilter.value; renderQueue(); });
    refs.relationFilters.querySelectorAll("[data-relation-mode]").forEach((button) => {
      button.addEventListener("click", () => {
        state.relationDependencyMode = button.dataset.relationMode === "statement" ? "statement" : "proof";
        renderRelations();
      });
    });
    refs.statementSourceToggle.addEventListener("click", () => {
      state.statementSourceOpen = !state.statementSourceOpen;
      const item = state.items.find((value) => value.key === state.selectedKey);
      renderStatementSource(item);
    });
    refs.copyStatementSource.addEventListener("click", copyStatementSource);
    refs.clearItemFilters.addEventListener("click", () => {
      state.itemSearch = "";
      state.itemTypeFilter = "all";
      state.itemSectionFilter = "all";
      state.reviewFilter = "all";
      refs.itemSearch.value = "";
      refs.itemTypeFilter.value = "all";
      refs.itemSectionFilter.value = "all";
      refs.reviewFilter.value = "all";
      renderQueue();
      refs.itemSearch.focus();
    });
    document.querySelectorAll("[data-evidence-view]").forEach((button) => button.addEventListener("click", () => setEvidenceView(button.dataset.evidenceView)));
    document.querySelectorAll("[data-decision]").forEach((button) => button.addEventListener("click", () => updateDraft(button.dataset.decision)));
    refs.reviewComment.addEventListener("input", () => updateDraft(undefined, refs.reviewComment.value));
    refs.saveReview.addEventListener("click", saveReview);
    refs.historySection.addEventListener("toggle", () => { if (refs.historySection.open) loadHistory(); });
    refs.logoutButton.addEventListener("click", async () => { try { const token = await csrfToken(); await api("/api/auth/logout", { method: "POST", headers: { "X-CSRF-Token": token } }); state.csrf = null; await loadSession(); } catch (error) { refs.saveState.textContent = error.message; } });
    window.addEventListener("popstate", () => { const slug = (window.location.pathname.match(/\/books\/([^/]+)/) || [])[1]; if (slug) selectBook(decodeURIComponent(slug), false); });
    window.addEventListener("keydown", (event) => {
      const typing = ["INPUT", "TEXTAREA", "SELECT"].includes(event.target?.tagName);
      const interactive = event.target?.isContentEditable || event.target?.closest?.("button, a, select, textarea, input, [role='tab'], [role='option']");
      if (event.key === "/" && !typing) { event.preventDefault(); refs.itemSearch.focus(); refs.itemSearch.select(); }
      if (event.key === "Escape" && document.activeElement === refs.itemSearch && refs.itemSearch.value) {
        refs.itemSearch.value = ""; state.itemSearch = ""; renderQueue(); return;
      }
      if (typing || interactive || !state.items.length) return;
      if (event.key === "ArrowDown" || event.key === "ArrowUp") { event.preventDefault(); const list = visibleItems(); const index = Math.max(0, list.findIndex((item) => item.key === state.selectedKey)); const next = list[Math.max(0, Math.min(list.length - 1, index + (event.key === "ArrowDown" ? 1 : -1)))]; if (next) selectItem(next.key, false); }
    });
  }

  async function loadSession() {
    try { state.session = await api("/api/session"); } catch (_) { state.session = { canSave: false, canLogin: false, canLogout: false, authConfigured: false }; }
    renderAuth();
  }

  async function boot() {
    initializePaneWidths();
    initializePanelState();
    bindEvents();
    setMobileView(localStorage.getItem("reasbook-reviewer:mobile-view") || "queue", false);
    try {
      const payload = await api("/api/catalog");
      state.catalog = Array.isArray(payload.books) ? payload.books : [];
      renderCatalog();
      await loadSession();
      const match = window.location.pathname.match(/\/books\/([^/]+)/);
      const initial = match ? decodeURIComponent(match[1]) : state.catalog.find((book) => bookState(book) === "ready")?.slug || state.catalog[0]?.slug;
      if (initial) await selectBook(initial, !match);
      state.pollTimer = window.setInterval(pollReviews, 5000);
    } catch (error) {
      refs.catalogList.innerHTML = `<div class="empty-state">${escapeHtml(error.message)}</div>`;
      setSync("Catalog failed", "warn");
    }
  }

  boot();
}());
