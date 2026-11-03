/-
Authors: Zichen Wang, Wanli Ma
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoBlog
import ReasBookSite.Home
import ReasBookSite.LiterateModule
import ReasBookSite.Sections
import ReasBookSite.RouteTable
import Book

open Verso Genre Blog Site Syntax
open ReasBookSite.RouteTable
open scoped ReasBookSite.RouteTable

open Output Html Template Theme

def siteRoot : String := ReasBookSite.Sections.siteRoot
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""
def sidebarDataScript : String := s!"window.__reasbookSidebarData={ReasBookSite.Sections.sidebarDataJson};"
def sidebarItemStateScript : String := r##"
(function () {
  // One title rule for chapters, sections, directory links and both sidebars.
  // Keep canonical labels/routes intact and move rich title nodes, never flatten
  // mathematical markup or copy type information into replacement text.
  const numberedTitle = /^(\s*)((?:(?:Chapter|Part|Section|Appendix)\s+(?:\d+(?:\.\d+)*|[IVXLCDM]+|[A-Z])|§+\s*\d+(?:\.\d+)*|\d+(?:\.\d+)+|[A-Z]\.\d+(?:\.\d+)*|(?:Definition|Theorem|Lemma|Corollary|Proposition|Remark|Example|Problem|Exercise|Algorithm|Assumption|Notation|Construction)\s+\d+(?:\.\d+)*))(\s*(?:—|–|--|:)\s*|\s+-\s+|\.\s+)(\S[\s\S]*?)\s*$/i;
  window.__reasbookFormatReadingTitle = function (node) {
    if (!node || node.classList.contains("reader-numbered-title") || node.closest("pre, code, [aria-disabled]")) return;
    const raw = node.textContent;
    const parts = raw.match(numberedTitle);
    if (!parts) return;
    const start = parts[1].length + parts[2].length + parts[3].length;
    const walker = document.createTreeWalker(node, NodeFilter.SHOW_TEXT);
    const range = document.createRange();
    range.setStart(node, 0);
    let offset = 0, foundStart = false, text;
    while ((text = walker.nextNode())) {
      const next = offset + text.length;
      if (start <= next) {
        range.setEnd(text, start - offset);
        foundStart = true;
        break;
      }
      offset = next;
    }
    if (!foundStart || range.cloneContents().querySelector("code, .katex, [data-verso-hover]")) return;
    // Delete only the plain numbering prefix, then move the original name
    // subtree intact, including links, listeners and native inline math nodes.
    const originalIds = Array.from(node.querySelectorAll("[id]"), element => element.id);
    range.deleteContents();
    const remainingIds = new Set(Array.from(node.querySelectorAll("[id]"), element => element.id));
    const number = document.createElement("span");
    number.className = "reader-title-number";
    for (const id of originalIds) {
      if (remainingIds.has(id)) continue;
      const anchor = document.createElement("span");
      anchor.id = id;
      anchor.setAttribute("aria-hidden", "true");
      number.appendChild(anchor);
    }
    number.appendChild(document.createTextNode(parts[2]));
    const name = document.createElement("span");
    name.className = "reader-title-name";
    while (node.firstChild) name.appendChild(node.firstChild);
    if (node.tagName === "A" && !node.hasAttribute("aria-label")) node.setAttribute("aria-label", raw.trim());
    node.replaceChildren(number, document.createTextNode(" "), name);
    node.classList.add("reader-numbered-title");
  };
  window.__reasbookFormatReadingTitles = function () {
    for (const heading of document.querySelectorAll(".main h2, .main h3")) {
      if (heading.textContent.trim() !== "Statements") continue;
      const section = heading.closest("section");
      if (heading.id) {
        const anchor = document.createElement("div");
        anchor.id = heading.id;
        anchor.className = "reader-section-heading";
        heading.replaceWith(anchor);
      } else heading.remove();
      if (section && !section.querySelector("h2")) {
        for (const item of section.querySelectorAll('[role="heading"][aria-level="3"]')) item.setAttribute("aria-level", "2");
      }
    }
    const headings = ".main h1, .main h2, .main h3, .main h4, .main h5, .main h6, .main [role='heading']";
    const links = ".reader-chapter-grid a, .main li > p > a, #sidebar-nav-root a, #sidebar-nav-root .nav-section-title, #sidebar-nav-root .nav-chapter-title";
    for (const node of document.querySelectorAll(headings + ", " + links)) {
      if (node.matches("a")) {
        if (node.closest("[data-reasbook-statement], .reader-attribution, .reader-contributors")) continue;
        // A stand-alone directory entry may be formatted, an inline citation
        // surrounded by prose must retain the paragraph's reading flow.
        if (node.matches(".main li > p > a") && Array.from(node.parentNode.childNodes).some(
            sibling => sibling !== node && sibling.textContent.trim())) continue;
      }
      window.__reasbookFormatReadingTitle(node);
    }
  };
  // Article-level contents are shared by the primary and fallback sidebar.
  window.__reasbookBuildPaperNavigation = function (work) {
    if (!(work.items || []).length) return null;
    const root = window.__versoSiteRoot || "/";
    const href = (route, anchor) => root + String(route || "").replace(/^\/+|\/+$/g, "") + "/" + (anchor ? "#" + encodeURIComponent(anchor) : "");
    const list = document.createElement("ul");
    list.className = "nav-work-tree";
    function link(label, route, anchor) {
      const a = document.createElement("a");
      a.textContent = label;
      a.href = href(route, anchor);
      if (anchor) a.setAttribute("data-chapter-target", "true");
      else if (pathKey(a.pathname) === pathKey(window.location.pathname)) {
        a.classList.add("is-current");
        a.setAttribute("aria-current", "page");
      }
      return a;
    }
    for (const group of (work.item_sections || [])) {
      const section = document.createElement("li");
      section.className = "nav-reading-section";
      const chapter = document.createElement("div");
      chapter.className = "nav-chapter";
      const row = document.createElement("div");
      row.className = "nav-chapter-row";
      const title = link(group.label, work.reader_route, group.anchor);
      title.className = "nav-section-title nav-chapter-title";
      row.appendChild(title);
      const items = document.createElement("ul");
      items.className = "nav-section-list nav-item-list";
      items.id = "paper-contents-" + work.slug + "-" + group.anchor;
      const hash = fragment(window.location.hash.slice(1));
      const onReader = pathKey(new URL(href(work.reader_route), window.location.origin).pathname) === pathKey(window.location.pathname);
      const ownsHash = hash === group.anchor || work.items.some(item => String(item.section) === String(group.number)
        && item.anchor && (hash === item.anchor || hash.startsWith(item.anchor + "-clause-")));
      const open = onReader && (ownsHash || (!hash && group === work.item_sections[0]));
      items.hidden = !open;
      chapter.classList.toggle("is-open", open);
      const toggle = document.createElement("button");
      toggle.type = "button";
      toggle.className = "nav-chapter-toggle";
      toggle.setAttribute("aria-controls", items.id);
      toggle.setAttribute("aria-expanded", String(open));
      toggle.setAttribute("aria-label", "Toggle contents for " + group.label);
      const chevron = document.createElement("span");
      chevron.setAttribute("aria-hidden", "true");
      chevron.textContent = "›";
      toggle.appendChild(chevron);
      row.appendChild(toggle);
      chapter.appendChild(row);
      for (const item of work.items.filter(item => String(item.section) === String(group.number))) {
        const row = document.createElement("li");
        row.className = "nav-file-item";
        let label;
        if (item.anchor) label = link(item.title, work.reader_route, item.anchor);
        else {
          label = document.createElement("span");
          label.textContent = item.title + " — no statement yet";
          label.setAttribute("aria-disabled", "true");
        }
        label.title = item.source || item.module || "";
        row.appendChild(label);
        items.appendChild(row);
      }
      chapter.appendChild(items);
      section.appendChild(chapter);
      list.appendChild(section);
    }
    if ((work.files || []).length) {
      const row = document.createElement("li");
      const details = document.createElement("details");
      details.className = "nav-secondary nav-supporting-files";
      const title = document.createElement("summary");
      title.textContent = "Supporting Lean files";
      details.appendChild(title);
      const files = document.createElement("ul");
      for (const file of work.files) {
        if (!file.route) continue;
        const item = document.createElement("li");
        item.className = "nav-file-item";
        const a = link(file.title, file.route);
        a.title = file.module || "";
        if (pathKey(a.pathname) === pathKey(window.location.pathname)) details.open = true;
        item.appendChild(a);
        files.appendChild(item);
      }
      details.appendChild(files);
      row.appendChild(details);
      list.appendChild(row);
    }
    return list;
  };
  function appendWorkName(node, name) {
    for (const part of name.split(/(Q-Order)/g)) {
      if (part === "Q-Order") {
        const term = document.createElement("span");
        term.className = "reader-title-term";
        term.textContent = part;
        node.appendChild(term);
      } else node.appendChild(document.createTextNode(part));
    }
  }
  window.__reasbookFormatWorkHeader = function (node, work) {
    if (!node || !work || !work.navigation_title || node.dataset.workTitle) return;
    node.dataset.workTitle = work.title;
    node.setAttribute("aria-label", work.title);
    const name = document.createElement("span");
    name.className = "nav-work-name";
    appendWorkName(name, work.navigation_title);
    const citation = document.createElement("span");
    citation.className = "nav-work-citation";
    citation.textContent = work.citation || "";
    node.replaceChildren(name, document.createTextNode(" "), citation);
    node.classList.add("reader-bibliographic-title");
  };
  window.__reasbookFormatWorkHeading = function (current) {
    if (!current || !current.work || !current.work.display_title) return;
    const work = current.work;
    const heading = document.querySelector(".main h1");
    if (!heading || heading.dataset.readerTitle) return;
    const original = heading.textContent.trim();
    const home = original === work.title;
    const prefix = work.title + " -- ";
    const fullDetail = original.startsWith(prefix);
    const ownFile = (work.files || []).some(file => pathKey(file.route || "") === pathKey(current.route || "") && file.title === original);
    if (!home && !fullDetail && !ownFile) return;
    const name = home ? work.display_title : fullDetail ? original.slice(prefix.length) : original;
    heading.replaceChildren();
    appendWorkName(heading, name);
    heading.classList.add("reader-work-heading");
    heading.dataset.readerTitle = home ? work.title : name;
    const bibliography = document.createElement("p");
    bibliography.className = "reader-bibliography";
    if (!home) {
      const paper = document.createElement("a");
      paper.href = (window.__versoSiteRoot || "/") + work.home;
      paper.textContent = work.navigation_title || work.display_title;
      paper.setAttribute("aria-label", work.title);
      bibliography.append(paper, document.createTextNode(" · "));
    }
    bibliography.appendChild(document.createTextNode(work.citation));
    heading.after(bibliography);
  };
  let forwardedPaperURL = "";
  window.__reasbookForwardPaperFragment = function (current) {
    if (!current || current.kind !== "paper" || !current.work || !current.work.reader_route
        || pathKey(current.work.home || "") !== pathKey(current.route || "") || !window.location.hash) return false;
    const hash = fragment(window.location.hash.slice(1));
    if (!(current.work.items || []).some(item => item.anchor
        && (hash === item.anchor || hash.startsWith(item.anchor + "-clause-")))) return false;
    const root = window.__versoSiteRoot || "/";
    const target = root + current.work.reader_route.replace(/^\/+|\/+$/g, "") + "/" + window.location.hash;
    if (forwardedPaperURL !== target) {
      forwardedPaperURL = target;
      window.location.replace(target);
    }
    return true;
  };
  function pathKey(path) {
    return path.replace(/index\.html$/i, "").replace(/\/+$/, "");
  }
  function fragment(hash) {
    try { return decodeURIComponent(hash); } catch (_) { return hash; }
  }
  function setChapterOpen(chapter, open) {
    const button = chapter.querySelector(".nav-chapter-toggle");
    const contents = chapter.querySelector(".nav-section-list");
    if (!button || !contents) return;
    button.setAttribute("aria-expanded", String(open));
    contents.hidden = !open;
    chapter.classList.toggle("is-open", open);
  }
  // Shared by the full sidebar and its fallback. Update in place so a hash
  // change does not reset the reader's expanded chapters or scroll position.
  window.__reasbookSyncChapterItems = function () {
    const nav = document.getElementById("sidebar-nav-root");
    if (!nav) return;
    const hash = fragment(window.location.hash);
    for (const a of nav.querySelectorAll("a[data-chapter-target]")) {
      const targetHash = fragment(a.hash);
      const matchesHash = hash === targetHash || (targetHash && hash.startsWith(targetHash + "-clause-"));
      const active = pathKey(a.pathname) === pathKey(window.location.pathname) && !!matchesHash;
      a.classList.toggle("is-current", active);
      if (active) {
        a.setAttribute("aria-current", targetHash ? "location" : "page");
        for (let parent = a.parentElement; parent && parent !== nav; parent = parent.parentElement) {
          if (parent.tagName === "DETAILS") parent.open = true;
          if (parent.classList.contains("nav-chapter")) setChapterOpen(parent, true);
        }
      } else {
        a.removeAttribute("aria-current");
      }
    }
    const current = nav.querySelector("a.is-current");
    const work = nav.querySelector(".nav-work-title");
    const heading = document.querySelector(".main h1");
    if (work && heading && work.dataset.workTitle) {
      const title = work.dataset.workTitle;
      const page = heading.dataset.readerTitle || heading.textContent.trim();
      document.title = (page === title ? title : title + " — " + page) + " — ReasBook";
    } else if (work && heading && !heading.textContent.includes(work.textContent.trim())) {
      document.title = work.textContent.trim() + " — " + heading.textContent.trim() + " — ReasBook";
    }
    if (current && nav.clientHeight > 0 && nav.scrollHeight > nav.clientHeight) {
      const box = current.getBoundingClientRect();
      const bounds = nav.getBoundingClientRect();
      if (box.top < bounds.top || box.bottom > bounds.bottom) {
        // Scroll only the navigation panel, never move the statement out of
        // view (notably on mobile and when following a deep fragment link).
        nav.scrollTop += box.top - bounds.top - nav.clientHeight / 2 + box.height / 2;
      }
    }
  };
  window.addEventListener("hashchange", window.__reasbookSyncChapterItems);

  function setupContentsToggle() {
    const skip = document.querySelector(".reader-skip-link");
    // Keep this fragment on the current page despite the project-level base.
    if (skip) skip.href = window.location.pathname + window.location.search + "#main-content";
    for (const pre of document.querySelectorAll(".main pre, .main code.hl.lean.block")) {
      pre.tabIndex = 0;
      pre.setAttribute("role", "region");
      pre.setAttribute("aria-label", "Lean code");
      pre.setAttribute("translate", "no");
    }
    window.__reasbookFormatReadingTitles();
    const nav = document.getElementById("sidebar-nav-root");
    if (!nav) return;
    nav.addEventListener("click", (event) => {
      const toggle = event.target.closest(".nav-chapter-toggle");
      if (toggle) setChapterOpen(toggle.closest(".nav-chapter"), toggle.getAttribute("aria-expanded") !== "true");
    });
    const mobile = window.matchMedia("(max-width: 1000px)");
    const button = document.createElement("button");
    button.id = "reader-nav-toggle";
    button.type = "button";
    button.setAttribute("aria-controls", nav.id);
    nav.before(button);
    nav.classList.add("has-toggle");
    const header = nav.closest("header");
    if (header) header.classList.add("reader-navigation");
    function setOpen(open) {
      const expanded = mobile.matches && open;
      nav.classList.toggle("is-open", expanded);
      button.setAttribute("aria-expanded", String(expanded));
      button.textContent = expanded ? "Hide contents" : "Show contents";
      if (expanded || !mobile.matches) window.__reasbookSyncChapterItems();
    }
    function closeContents() {
      if (!mobile.matches) return;
      if (nav.contains(document.activeElement)) button.focus({ preventScroll: true });
      setOpen(false);
    }
    button.addEventListener("click", () => setOpen(button.getAttribute("aria-expanded") !== "true"));
    nav.addEventListener("click", (event) => {
      if (event.button === 0 && !event.metaKey && !event.ctrlKey && !event.shiftKey && !event.altKey
          && event.target.closest("a[href]")) closeContents();
    });
    document.addEventListener("keydown", (event) => {
      if (event.key === "Escape" && nav.classList.contains("is-open")) {
        closeContents();
        button.focus({ preventScroll: true });
      }
    });
    window.addEventListener("hashchange", closeContents);
    mobile.addEventListener("change", () => setOpen(false));
    setOpen(false);
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", setupContentsToggle);
  else setupContentsToggle();
})();
"##
def sidebarFallbackScript : String := r##"
(function () {
  const siteRoot = (typeof window !== "undefined" && typeof window.__versoSiteRoot === "string" && window.__versoSiteRoot)
    ? window.__versoSiteRoot
    : "/";
  const siteRootNoSlash = siteRoot.endsWith("/") ? siteRoot.slice(0, -1) : siteRoot;
  const introBookSlug = "introductiontorealanalysisvolumei_jirilebl_2025";

  function trimSlashes(s) {
    return (s || "").replace(/^\/+|\/+$/g, "");
  }

  function normalizeRoute(route) {
    route = (route || "").replace(/^\/+/, "");
    route = route.replace(/index\.html$/i, "");
    if (route.endsWith(".html")) route = route.slice(0, -5) + "/";
    if (route && !route.endsWith("/")) route += "/";
    return route;
  }

  function normalizeLegacyRoute(rel) {
    rel = normalizeRoute(rel || "");
    if (rel.startsWith("chapters/")) {
      return normalizeRoute("books/" + introBookSlug + "/" + rel);
    }
    return rel;
  }

  function canonicalRelPath(rel) {
    rel = normalizeRoute((rel || "").replace(/^\/+/, ""));
    const keys = ["books/", "papers/", "docs/"];
    for (const key of keys) {
      const i = rel.lastIndexOf(key);
      if (i > 0) return normalizeLegacyRoute(rel.slice(i));
    }
    return normalizeLegacyRoute(rel);
  }

  function currentRelPath() {
    let p = window.location.pathname || "";
    if (p.startsWith(siteRoot)) p = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) p = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) p = p.slice(1);
    return canonicalRelPath(p);
  }

  function docsRelToRoute(rel) {
    const parts = canonicalRelPath(rel).split("/").filter(Boolean);
    if (parts.length < 3 || parts[0] !== "docs") return "";
    const scope = String(parts[1] || "").toLowerCase();
    const slug = String(parts[2] || "").toLowerCase();
    if (!slug) return "";

    if (scope === "books") {
      if (parts.length >= 4 && String(parts[3] || "").toLowerCase() === "chapters") {
        const chap = String(parts[4] || "").toLowerCase().replace(/\.html$/i, "");
        if (!chap) return "";
        if (parts.length >= 6) {
          const leaf = String(parts[5] || "").toLowerCase().replace(/\.html$/i, "");
          if (!leaf) return normalizeRoute("books/" + slug + "/chapters/" + chap + "/");
          return normalizeRoute("books/" + slug + "/chapters/" + chap + "/" + leaf + "/");
        }
        return normalizeRoute("books/" + slug + "/chapters/" + chap + "/");
      }
      const leaf = String(parts[3] || "").toLowerCase();
      if (leaf === "book.html") return normalizeRoute("books/" + slug + "/book/");
      if (leaf.startsWith("chap") && leaf.endsWith(".html")) {
        return normalizeRoute("books/" + slug + "/chapters/" + leaf.replace(/\.html$/i, "") + "/");
      }
    }

    if (scope === "papers") {
      if (parts.length >= 4 && String(parts[3] || "").toLowerCase() === "sections") {
        const leaf = String(parts[4] || "").toLowerCase().replace(/\.html$/i, "");
        if (!leaf) return normalizeRoute("papers/" + slug + "/");
        return normalizeRoute("papers/" + slug + "/sections/" + leaf + "/");
      }
      const leaf = String(parts[3] || "").toLowerCase();
      if (leaf === "paper.html" || leaf === "main.html") return normalizeRoute("papers/" + slug + "/");
    }

    return "";
  }

  function routeForLocation() {
    const rel = currentRelPath();
    if (rel.startsWith("docs/")) return docsRelToRoute(rel);
    return normalizeRoute(rel);
  }

  function sameRoute(a, b) {
    const aa = normalizeRoute(a);
    const bb = normalizeRoute(b);
    return aa !== "" && aa === bb;
  }

  function findCurrentWork(navData) {
    const rel = currentRelPath();
    const route = routeForLocation();
    const parts = rel.split("/").filter(Boolean);
    if (parts.length >= 2 && parts[0] === "books") {
      const slug = parts[1];
      const work = (navData.books || []).find((w) => w.slug === slug) || null;
      return { kind: "book", work: work, route: route };
    }
    if (parts.length >= 2 && parts[0] === "papers") {
      const slug = parts[1];
      const work = (navData.papers || []).find((w) => w.slug === slug) || null;
      return { kind: "paper", work: work, route: route };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Books") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.books || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "book", work: work, route: route };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Papers") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.papers || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "paper", work: work, route: route };
    }
    // A project fragment renders its own home at / as well as the named route.
    // Do not turn that landing page back into an all-projects navigation tree.
    const owners = (navData.books || []).map(work => ({kind: "book", work}))
      .concat((navData.papers || []).map(work => ({kind: "paper", work})))
      .filter(({work}) => (work.routes || []).some(candidate => sameRoute(candidate, route)));
    if (owners.length === 1) return {...owners[0], route: route};
    if (!rel && document.querySelector(".reader-home-links")) {
      const works = (navData.books || []).map(work => ({kind: "book", work}))
        .concat((navData.papers || []).map(work => ({kind: "paper", work})));
      if (works.length === 1) return {...works[0], route: works[0].work.home};
    }
    return { kind: "", work: null, route: route };
  }

  function escapeHtml(s) {
    return String(s || "")
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function itemHtml(href, label) {
    return '<li><a href="' + href + '">' + escapeHtml(label) + '</a></li>';
  }

  function renderCurrentWork(current) {
    const work = current.work;
    const route = current.route;
    if (!work) return "";

    let html = '<li class="nav-current-work">';
    if (work.home) {
      const href = siteRoot + trimSlashes(work.home) + "/";
      html += '<a class="nav-work-title' + (sameRoute(work.home, route) ? ' is-current' : '')
        + '" title="' + (current.kind === "book" ? "Book home" : "Paper home") + '"'
        + (sameRoute(work.home, route) ? ' aria-current="page"' : '')
        + ' href="' + escapeHtml(href) + '">' + escapeHtml(work.title) + '</a>';
    } else {
      html += '<div class="nav-work-title">' + escapeHtml(work.title) + '</div>';
    }
    if (current.kind === "paper") {
      const contents = window.__reasbookBuildPaperNavigation(work);
      if (contents) return html + contents.outerHTML + "</li>";
    }
    html += '<ul class="nav-work-tree">';

    if (current.kind === "book" && Array.isArray(work.chapters) && work.chapters.length > 0) {
      for (const chapter of work.chapters) {
        const open = sameRoute(chapter.route, route) || (chapter.sections || []).some(section =>
          sameRoute(section.route, route) || (section.parts || []).some(part => sameRoute(part.route, route)));
        const id = "chapter-contents-" + String(chapter.route).replace(/[^a-zA-Z0-9_-]/g, "-");
        html += '<li class="nav-chapter-item"><div class="nav-chapter' + (open ? ' is-open' : '')
          + '"><div class="nav-chapter-row">';
        if (chapter.route) {
          const href = siteRoot + trimSlashes(chapter.route) + "/";
          html += '<a class="nav-chapter-title" data-chapter-target="true" href="' + escapeHtml(href)
            + '" aria-label="' + escapeHtml(chapter.title || "") + '">' + escapeHtml(chapter.title || "") + '</a>';
        } else {
          html += '<span class="nav-chapter-title">' + escapeHtml(chapter.title || "") + '</span>';
        }
        html += '<button type="button" class="nav-chapter-toggle" aria-controls="' + id
          + '" aria-expanded="' + open + '" aria-label="Toggle contents for '
          + escapeHtml(chapter.title || "") + '"><span aria-hidden="true">›</span></button></div>'
          + '<ul class="nav-section-list" id="' + id + '"' + (open ? '' : ' hidden') + '>';
        const itemGroups = (chapter.item_sections || []).length
          ? [{items: (chapter.items || []).filter(item => item.section === undefined)},
             ...chapter.item_sections.map(group => ({...group,
               items: (chapter.items || []).filter(item => item.section === group.number)}))]
          : [{items: chapter.items || []}];
        for (const group of itemGroups) {
          if (group.label) {
            html += '<li class="nav-reading-section">';
            if (group.anchor) {
              const href = siteRoot + trimSlashes(chapter.route) + '/#' + encodeURIComponent(group.anchor);
              html += '<a class="nav-section-title" data-chapter-target="true" href="' + escapeHtml(href)
                + '">' + escapeHtml(group.label) + '</a>';
            } else {
              html += '<span class="nav-section-title">' + escapeHtml(group.label) + '</span>';
            }
            html += '<ul class="nav-item-list">';
          }
          for (const item of group.items) {
            html += '<li class="nav-file-item">';
            if (item.anchor) {
              const href = siteRoot + trimSlashes(chapter.route) + "/#" + encodeURIComponent(item.anchor);
              html += '<a data-chapter-target="true" href="' + escapeHtml(href) + '" title="'
                + escapeHtml(item.source || item.module) + '">' + escapeHtml(item.title) + '</a>';
            } else {
              html += '<span aria-disabled="true" title="' + escapeHtml(item.source || item.module) + '">'
                + escapeHtml(item.title) + ' — no statement yet</span>';
            }
            html += '</li>';
          }
          if (group.label) html += '</ul></li>';
        }
        for (const section of (chapter.sections || [])) {
          if (section.route) {
            const href = siteRoot + trimSlashes(section.route) + "/";
            html += sameRoute(section.route, route)
              ? '<li><a class="is-current" href="' + href + '">' + escapeHtml(section.label || section.title || "") + "</a></li>"
              : itemHtml(href, section.label || section.title || "");
          }
          for (const part of (section.parts || [])) {
            const href = siteRoot + trimSlashes(part.route || "") + "/";
            html += sameRoute(part.route || "", route)
              ? '<li><a class="is-current" href="' + href + '">' + escapeHtml(part.title || "") + "</a></li>"
              : itemHtml(href, part.title || "");
          }
        }
        html += "</ul></div></li>";
      }
    } else {
      for (const section of (work.sections || [])) {
        if (!section.route) continue;
        const href = siteRoot + trimSlashes(section.route) + "/";
        html += sameRoute(section.route, route)
          ? '<li><a class="is-current" href="' + href + '">' + escapeHtml(section.title || "") + "</a></li>"
          : itemHtml(href, section.title || "");
      }
    }

    for (const file of (work.files || [])) {
      if (!file.route) continue;
      const href = siteRoot + trimSlashes(file.route) + "/";
      html += '<li class="nav-file-item"><a href="' + escapeHtml(href) + '"'
        + (sameRoute(file.route, route) ? ' class="is-current" aria-current="page"' : '')
        + ' title="' + escapeHtml(file.module || "") + '">' + escapeHtml(file.title) + '</a></li>';
    }
    html += "</ul></li>";
    return html;
  }

  function fallbackHtml() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const current = findCurrentWork(navData);
    let html = "<ol>";
    if (!current.work) {
      html += itemHtml(siteRoot, "Home");
      html += itemHtml(siteRoot + "docs/", "Documentation");
    }

    if (current.work) {
      html += renderCurrentWork(current);
      html += "</ol>";
      return html;
    }

    for (const w of (navData.books || [])) {
      if (w.home) html += itemHtml(siteRoot + trimSlashes(w.home) + "/", w.title || "Book");
    }
    for (const w of (navData.papers || [])) {
      if (w.home) html += itemHtml(siteRoot + trimSlashes(w.home) + "/", w.title || "Paper");
    }
    html += "</ol>";
    return html;
  }

  function ensureSidebarFallback() {
    var navRoot = document.getElementById("sidebar-nav-root");
    if (!navRoot) return;
    const current = findCurrentWork(window.__reasbookSidebarData || { books: [], papers: [] });
    if (window.__reasbookForwardPaperFragment(current)) return;
    window.__reasbookFormatWorkHeading(current);
    if (navRoot.children && navRoot.children.length > 0) return;
    navRoot.innerHTML = fallbackHtml();
    window.__reasbookFormatWorkHeader(navRoot.querySelector(".nav-work-title"), current && current.work);
    window.__reasbookFormatReadingTitles();
    window.__reasbookSyncChapterItems();
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", ensureSidebarFallback);
  else ensureSidebarFallback();
})();
"##
def docsRoot : String := ReasBookSite.Sections.docsRoot
def staticRoot : String := ReasBookSite.Sections.staticRoot
def navLinkRewriteScript : String := r##"
(function () {
  const siteRoot = (typeof window !== "undefined" && typeof window.__versoSiteRoot === "string" && window.__versoSiteRoot)
    ? window.__versoSiteRoot
    : "/";
  const siteRootNoSlash = siteRoot.endsWith("/") ? siteRoot.slice(0, -1) : siteRoot;
  const introBookSlug = "introductiontorealanalysisvolumei_jirilebl_2025";
  const specials = ["#", "mailto:", "tel:"];

  function trimSlashes(s) {
    return (s || "").replace(/^\/+|\/+$/g, "");
  }

  function normalizeRoute(route) {
    route = (route || "").replace(/^\/+/, "");
    route = route.replace(/index\.html$/i, "");
    if (route.endsWith(".html")) route = route.slice(0, -5) + "/";
    if (route && !route.endsWith("/")) route += "/";
    return route;
  }

  function normalizeLegacyRoute(rel) {
    rel = normalizeRoute(rel || "");
    if (rel.startsWith("chapters/")) {
      return normalizeRoute("books/" + introBookSlug + "/" + rel);
    }
    return rel;
  }

  function isSpecial(href) {
    return specials.some((p) => href.startsWith(p));
  }

  function trimToLastSegment(rel, key) {
    const i = rel.lastIndexOf(key);
    if (i > 0) return rel.slice(i);
    return rel;
  }

  function canonicalRelPath(rel) {
    rel = normalizeRoute(rel.replace(/^\/+/, ""));
    rel = trimToLastSegment(rel, "books/");
    rel = trimToLastSegment(rel, "papers/");
    rel = trimToLastSegment(rel, "docs/");
    return normalizeLegacyRoute(rel);
  }

  function currentRelPath() {
    let p = window.location.pathname || "";
    if (p.startsWith(siteRoot)) p = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) p = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) p = p.slice(1);
    return canonicalRelPath(p);
  }

  function docsRelToRoute(rel) {
    const parts = canonicalRelPath(rel).split("/").filter(Boolean);
    if (parts.length < 3 || parts[0] !== "docs") return "";
    const scope = String(parts[1] || "").toLowerCase();
    const slug = String(parts[2] || "").toLowerCase();
    if (!slug) return "";

    if (scope === "books") {
      if (parts.length >= 4 && String(parts[3] || "").toLowerCase() === "chapters") {
        const chap = String(parts[4] || "").toLowerCase().replace(/\.html$/i, "");
        if (!chap) return "";
        if (parts.length >= 6) {
          const leaf = String(parts[5] || "").toLowerCase().replace(/\.html$/i, "");
          if (!leaf) return normalizeRoute("books/" + slug + "/chapters/" + chap + "/");
          return normalizeRoute("books/" + slug + "/chapters/" + chap + "/" + leaf + "/");
        }
        return normalizeRoute("books/" + slug + "/chapters/" + chap + "/");
      }
      const leaf = String(parts[3] || "").toLowerCase();
      if (leaf === "book.html") return normalizeRoute("books/" + slug + "/book/");
      if (leaf.startsWith("chap") && leaf.endsWith(".html")) {
        return normalizeRoute("books/" + slug + "/chapters/" + leaf.replace(/\.html$/i, "") + "/");
      }
    }

    if (scope === "papers") {
      if (parts.length >= 4 && String(parts[3] || "").toLowerCase() === "sections") {
        const leaf = String(parts[4] || "").toLowerCase().replace(/\.html$/i, "");
        if (!leaf) return normalizeRoute("papers/" + slug + "/");
        return normalizeRoute("papers/" + slug + "/sections/" + leaf + "/");
      }
      const leaf = String(parts[3] || "").toLowerCase();
      if (leaf === "paper.html" || leaf === "main.html") return normalizeRoute("papers/" + slug + "/");
    }

    return "";
  }

  function routeForLocation() {
    const rel = currentRelPath();
    if (rel.startsWith("docs/")) return docsRelToRoute(rel);
    return normalizeRoute(rel);
  }

  function findWork(collection, slug) {
    return (collection || []).find((w) => String(w.slug || "").toLowerCase() === String(slug || "").toLowerCase()) || null;
  }

  function findCurrentWork(navData) {
    const rel = currentRelPath();
    const currentRoute = routeForLocation();
    const parts = rel.split("/").filter(Boolean);
    const p0 = String(parts[0] || "").toLowerCase();
    const p1 = String(parts[1] || "").toLowerCase();

    if (parts.length >= 2 && p0 === "books") {
      return { kind: "book", work: findWork(navData.books, parts[1]), route: currentRoute };
    }
    if (parts.length >= 2 && p0 === "papers") {
      return { kind: "paper", work: findWork(navData.papers, parts[1]), route: currentRoute };
    }
    if (parts.length >= 3 && p0 === "docs" && p1 === "books") {
      return { kind: "book", work: findWork(navData.books, parts[2]), route: currentRoute };
    }
    if (parts.length >= 3 && p0 === "docs" && p1 === "papers") {
      return { kind: "paper", work: findWork(navData.papers, parts[2]), route: currentRoute };
    }
    const owners = (navData.books || []).map(work => ({kind: "book", work}))
      .concat((navData.papers || []).map(work => ({kind: "paper", work})))
      .filter(({work}) => (work.routes || []).some(route => sameRoute(route, currentRoute)));
    if (owners.length === 1) return {...owners[0], route: currentRoute};
    if (!rel && document.querySelector(".reader-home-links")) {
      const works = (navData.books || []).map(work => ({kind: "book", work}))
        .concat((navData.papers || []).map(work => ({kind: "paper", work})));
      if (works.length === 1) return {...works[0], route: works[0].work.home};
    }
    return { kind: "", work: null, route: currentRoute };
  }

  function sameRoute(a, b) {
    const aa = normalizeRoute(a);
    const bb = normalizeRoute(b);
    return aa !== "" && aa === bb;
  }

  function isRoutePrefix(prefix, current) {
    const p = normalizeRoute(prefix);
    const c = normalizeRoute(current);
    return p !== "" && c.startsWith(p);
  }

  function routeHref(route) {
    const rel = normalizeRoute(route);
    if (!rel) return siteRoot;
    return siteRoot + rel;
  }

  function mkAnchor(href, label, isCurrent) {
    const a = document.createElement("a");
    a.href = href;
    a.textContent = label;
    if (isCurrent) {
      a.classList.add("is-current");
      a.setAttribute("aria-current", "page");
    }
    return a;
  }

  function mkItem(href, label, isCurrent) {
    const li = document.createElement("li");
    li.appendChild(mkAnchor(href, label, isCurrent));
    return li;
  }

  function fmtNumber(n) {
    const k = Number(n);
    return Number.isFinite(k) && k > 0 ? String(Math.trunc(k)) : "";
  }

  function sectionLabel(chapterNumber, section) {
    if (section && section.label) return String(section.label);
    const c = fmtNumber(chapterNumber);
    const s = fmtNumber(section && section.number);
    const title = (section && section.title) ? String(section.title) : "";
    if (c && s) return c + "." + s + ". " + title;
    return title;
  }

  function partLabel(chapterNumber, section, part) {
    const c = fmtNumber(chapterNumber);
    const s = fmtNumber(section && section.number);
    const p = fmtNumber(part && part.number);
    const title = (part && part.title) ? String(part.title) : ("Part " + p);
    if (section && section.label) return String(section.label) + " — " + title;
    if (c && s && p) return c + "." + s + "." + p + ". " + title;
    return title;
  }

  function sectionHasCurrent(section, currentRoute) {
    if (sameRoute(section.route || "", currentRoute)) return true;
    if (isRoutePrefix(section.route || "", currentRoute)) return true;
    for (const part of (section.parts || [])) {
      if (sameRoute(part.route || "", currentRoute)) return true;
    }
    return false;
  }

  function chapterHasCurrent(chapter, currentRoute) {
    if (sameRoute(chapter.route || "", currentRoute)) return true;
    if (isRoutePrefix(chapter.route || "", currentRoute)) return true;
    for (const section of (chapter.sections || [])) {
      if (sectionHasCurrent(section, currentRoute)) return true;
    }
    return false;
  }

  function mkSectionNode(section, currentRoute, chapterNumber) {
    const li = document.createElement("li");
    li.classList.add("nav-section-item");

    const title = sectionLabel(chapterNumber, section);
    if (section.route) {
      li.appendChild(mkAnchor(routeHref(section.route), title, sameRoute(section.route, currentRoute)));
    } else {
      const span = document.createElement("span");
      span.textContent = title;
      li.appendChild(span);
    }

    const parts = Array.isArray(section.parts) ? section.parts : [];
    if (parts.length > 0) {
      const details = document.createElement("details");
      details.classList.add("nav-section-parts");
      details.open = sectionHasCurrent(section, currentRoute);

      const summary = document.createElement("summary");
      summary.textContent = "Parts (" + parts.length + ")";
      details.appendChild(summary);

      const partList = document.createElement("ul");
      partList.classList.add("nav-part-list");
      for (const part of parts) {
        if (!part.route) continue;
        partList.appendChild(
          mkItem(
            routeHref(part.route),
            partLabel(chapterNumber, section, part),
            sameRoute(part.route, currentRoute)
          )
        );
      }
      if (partList.children.length > 0) {
        details.appendChild(partList);
        li.appendChild(details);
      }
    }

    return li;
  }

  function mkChapterNode(chapter, currentRoute) {
    const li = document.createElement("li");
    li.classList.add("nav-chapter-item");

    const details = document.createElement("div");
    details.classList.add("nav-chapter");
    const open = chapterHasCurrent(chapter, currentRoute);
    details.classList.toggle("is-open", open);
    const row = document.createElement("div");
    row.classList.add("nav-chapter-row");
    const title = chapter.route
      ? mkAnchor(routeHref(chapter.route), chapter.title || "", false)
      : document.createElement("span");
    if (!chapter.route) title.textContent = chapter.title || "";
    title.classList.add("nav-chapter-title");
    if (chapter.route) title.setAttribute("data-chapter-target", "true");
    row.appendChild(title);
    const toggle = document.createElement("button");
    toggle.type = "button";
    toggle.classList.add("nav-chapter-toggle");
    const contentsId = "chapter-contents-" + String(chapter.route).replace(/[^a-zA-Z0-9_-]/g, "-");
    toggle.setAttribute("aria-controls", contentsId);
    toggle.setAttribute("aria-expanded", String(open));
    toggle.setAttribute("aria-label", "Toggle contents for " + (chapter.title || ""));
    const chevron = document.createElement("span");
    chevron.setAttribute("aria-hidden", "true");
    chevron.textContent = "›";
    toggle.appendChild(chevron);
    row.appendChild(toggle);
    details.appendChild(row);
    const sectionList = document.createElement("ul");
    sectionList.classList.add("nav-section-list");
    sectionList.id = contentsId;
    sectionList.hidden = !open;
    const itemGroups = (chapter.item_sections || []).length
      ? [{items: (chapter.items || []).filter(item => item.section === undefined)},
         ...chapter.item_sections.map(group => ({...group,
           items: (chapter.items || []).filter(item => item.section === group.number)}))]
      : [{items: chapter.items || []}];
    for (const group of itemGroups) {
      let itemList = sectionList;
      if (group.label) {
        const section = document.createElement("li");
        section.classList.add("nav-reading-section");
        const heading = group.anchor
          ? mkAnchor(routeHref(chapter.route) + "#" + encodeURIComponent(group.anchor), group.label, false)
          : document.createElement("span");
        if (!group.anchor) heading.textContent = group.label;
        heading.classList.add("nav-section-title");
        if (group.anchor) heading.setAttribute("data-chapter-target", "true");
        section.appendChild(heading);
        itemList = document.createElement("ul");
        itemList.classList.add("nav-item-list");
        section.appendChild(itemList);
        sectionList.appendChild(section);
      }
      for (const item of group.items) {
        const node = document.createElement("li");
        node.classList.add("nav-file-item");
        let label;
        if (item.anchor) {
          label = mkAnchor(routeHref(chapter.route) + "#" + encodeURIComponent(item.anchor), item.title, false);
          label.setAttribute("data-chapter-target", "true");
        } else {
          label = document.createElement("span");
          label.textContent = item.title + " — no statement yet";
          label.setAttribute("aria-disabled", "true");
        }
        label.title = item.source || item.module || "";
        node.appendChild(label);
        itemList.appendChild(node);
      }
    }
    for (const section of (chapter.sections || [])) {
      sectionList.appendChild(mkSectionNode(section, currentRoute, chapter.number));
    }

    details.appendChild(sectionList);
    li.appendChild(details);
    return li;
  }

  function mkWorkHeader(work, currentRoute, label) {
    const li = document.createElement("li");
    li.classList.add("nav-current-work");
    const title = work.home
      ? mkAnchor(routeHref(work.home), work.title || label, sameRoute(work.home, currentRoute))
      : document.createElement("div");
    if (!work.home) title.textContent = work.title || label;
    title.classList.add("nav-work-title");
    title.title = label;
    window.__reasbookFormatWorkHeader(title, work);
    li.appendChild(title);
    return li;
  }

  function mkBookTree(work, currentRoute) {
    const li = mkWorkHeader(work, currentRoute, "Book home");
    const tree = document.createElement("ul");
    tree.classList.add("nav-work-tree");

    const chapters = Array.isArray(work.chapters) ? work.chapters : [];
    if (chapters.length > 0) {
      for (const chapter of chapters) {
        tree.appendChild(mkChapterNode(chapter, currentRoute));
      }
    } else {
      for (const section of (work.sections || [])) {
        if (!section.route) continue;
        tree.appendChild(mkSectionNode(section, currentRoute, 0));
      }
    }

    li.appendChild(tree);
    return li;
  }

  function mkPaperTree(work, currentRoute) {
    const li = mkWorkHeader(work, currentRoute, "Paper home");
    const contents = window.__reasbookBuildPaperNavigation(work);
    if (contents) {
      li.appendChild(contents);
      return li;
    }
    const sectionList = document.createElement("ul");
    sectionList.classList.add("nav-work-tree");
    for (const section of (work.sections || [])) {
      if (!section.route) continue;
      sectionList.appendChild(mkSectionNode(section, currentRoute, 0));
    }
    for (const file of (work.files || [])) {
      if (!file.route) continue;
      const item = mkItem(routeHref(file.route), file.title, sameRoute(file.route, currentRoute));
      item.classList.add("nav-file-item");
      item.firstChild.title = file.module || "";
      sectionList.appendChild(item);
    }

    li.appendChild(sectionList);
    return li;
  }

  function mkSectionGroup(title, works, defaultOpen) {
    const li = document.createElement("li");
    li.classList.add("nav-secondary-group");
    const details = document.createElement("details");
    details.classList.add("nav-secondary");
    details.open = !!defaultOpen;
    const summary = document.createElement("summary");
    summary.textContent = title;
    details.appendChild(summary);

    const workList = document.createElement("ul");
    for (const w of works || []) {
      if (!w.home) continue;
      workList.appendChild(mkItem(routeHref(w.home), w.title || "", false));
    }

    details.appendChild(workList);
    li.appendChild(details);
    return li;
  }

  function normalizeInternalHref(href) {
    if (!href) return href;
    href = href.trim();
    if (!href || isSpecial(href)) return href;

    let u;
    try {
      u = new URL(href, window.location.origin);
    } catch (_) {
      return href;
    }

    if (u.origin !== window.location.origin) return href;

    // Preserve query/hash while normalizing the path component.
    const qh = u.search + u.hash;
    let p = u.pathname;

    if (p === "/" || p === "/index.html") return siteRoot + qh;
    if (p === "/docs" || p === "/docs/") return siteRoot + "docs/" + qh;

    let relRaw;
    if (p.startsWith(siteRoot)) relRaw = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) relRaw = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) relRaw = p.slice(1);
    else relRaw = p;

    relRaw = (relRaw || "").replace(/^\/+/, "");
    const docsIdx = relRaw.toLowerCase().lastIndexOf("docs/");
    if (docsIdx >= 0) {
      const docsRel = relRaw.slice(docsIdx);
      const docsLower = docsRel.toLowerCase();
      if (docsLower === "docs" || docsLower === "docs/") return siteRoot + "docs/" + qh;
      if (docsLower.endsWith(".html")) return siteRoot + docsRel + qh;
    }

    let rel = normalizeRoute(canonicalRelPath(relRaw));
    if (!rel) return siteRoot + qh;
    return siteRoot + rel + qh;
  }

  function rewriteAllAnchors() {
    for (const a of document.querySelectorAll("a[href]")) {
      // A collection link may intentionally leave a project-mounted reader.
      if (a.hasAttribute("data-reader-collection")) continue;
      const oldHref = (a.getAttribute("href") || "").trim();
      const newHref = normalizeInternalHref(oldHref);
      if (newHref && newHref !== oldHref) a.setAttribute("href", newHref);
    }
  }

  function onClick(ev) {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    const a = ev.target && ev.target.closest ? ev.target.closest("a[href]") : null;
    if (!a) return;
    if (a.hasAttribute("data-reader-collection")) return;
    if ((a.getAttribute("target") || "").toLowerCase() === "_blank") return;

    const oldHref = (a.getAttribute("href") || "").trim();
    const newHref = normalizeInternalHref(oldHref);
    if (!newHref || newHref === oldHref) return;

    a.setAttribute("href", newHref);
    ev.preventDefault();
    window.location.assign(newHref);
  }

  function boot() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const current = findCurrentWork(navData);
    const navRoot = document.getElementById("sidebar-nav-root");
    window.__reasbookFormatWorkHeading(current);

    function renderSidebarNav() {
      if (!navRoot) return;
      const list = document.createElement("ol");
      list.classList.add("nav-tree-root");
      try {
        if (current.work) {
          if (current.kind === "book") {
            list.appendChild(mkBookTree(current.work, current.route));
          } else if (current.kind === "paper") {
            list.appendChild(mkPaperTree(current.work, current.route));
          }
        } else {
          list.appendChild(mkItem(siteRoot, "Home", sameRoute("", current.route)));
          list.appendChild(mkItem(siteRoot + "docs/", "Documentation", false));
          list.appendChild(mkSectionGroup("Books", navData.books || [], true));
          list.appendChild(mkSectionGroup("Papers", navData.papers || [], true));
        }
      } catch (err) {
        console.error("Failed to build sidebar navigation", err);
        return;
      }
      navRoot.innerHTML = "";
      navRoot.appendChild(list);
      window.__reasbookSyncChapterItems();
    }

    renderSidebarNav();
    if (window.__reasbookForwardPaperFragment(current)) return;
    window.__reasbookFormatReadingTitles();
    rewriteAllAnchors();
    document.addEventListener("click", onClick, true);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();
"##

def theme : Theme := { Theme.default with
  primaryTemplate := do
    let pagePath := String.intercalate "/" (← currentPath).toList
    let skipTarget := siteRoot ++ pagePath ++ (if pagePath.isEmpty || pagePath.endsWith "/" then "" else "/") ++ "#main-content"
    return {{
      <html lang="en">
        <head>
          <meta charset="UTF-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="theme-color" content="#ffffff"/>
          <base href={{siteRoot}}/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href={{staticRoot}}/>
          <script>{{Html.text false siteRootScript}}</script>
          <script>{{Html.text false sidebarDataScript}}</script>
          <script>{{Html.text false sidebarItemStateScript}}</script>
          <script>{{Html.text false navLinkRewriteScript}}</script>
          <script>{{Html.text false sidebarFallbackScript}}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <a class="reader-skip-link" href={{skipTarget}}>"Skip to content"</a>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation" aria-label="Reading contents" id="sidebar-nav-root"></nav>
            </div>
          </header>
          <div class="main" role="main" id="main-content" tabindex="-1">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
}
|>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

/-- Generated section routes are injected by `reasbook_site_dir` from `ReasBookSite.RouteTable`. -/
def demoSite : Site := reasbook_site

def baseUrl := ReasBookSite.Sections.docsRoot

def linkTargets : Code.LinkTargets α where
  const name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
  definition name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
where
  mkLink href := { shortDescription := "doc", description := "Documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
