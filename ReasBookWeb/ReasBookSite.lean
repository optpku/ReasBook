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
  function pathKey(path) {
    return path.replace(/index\.html$/i, "").replace(/\/+$/, "");
  }
  function fragment(hash) {
    try { return decodeURIComponent(hash); } catch (_) { return hash; }
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
        }
      } else {
        a.removeAttribute("aria-current");
      }
    }
    const current = nav.querySelector("a.is-current");
    const work = nav.querySelector(".nav-work-title");
    const heading = document.querySelector(".main h1");
    if (work && heading && !heading.textContent.includes(work.textContent.trim())) {
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
    const nav = document.getElementById("sidebar-nav-root");
    if (!nav) return;
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
    html += '<ul class="nav-work-tree">';

    if (current.kind === "book" && Array.isArray(work.chapters) && work.chapters.length > 0) {
      for (const chapter of work.chapters) {
        html += '<li><details class="nav-chapter"' + (sameRoute(chapter.route, route) ? " open" : "")
          + "><summary>" + escapeHtml(chapter.title || "")
          + '</summary><ul class="nav-section-list">';
        if (chapter.route) {
          const href = siteRoot + trimSlashes(chapter.route) + "/";
          html += '<li><a data-chapter-target="true" href="' + escapeHtml(href) + '">Overview</a></li>';
        }
        for (const item of (chapter.items || [])) {
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
        for (const section of (chapter.sections || [])) {
          if (section.route) {
            const href = siteRoot + trimSlashes(section.route) + "/";
            html += sameRoute(section.route, route)
              ? '<li><a class="is-current" href="' + href + '">' + escapeHtml(section.title || "") + "</a></li>"
              : itemHtml(href, section.title || "");
          }
          for (const part of (section.parts || [])) {
            const href = siteRoot + trimSlashes(part.route || "") + "/";
            html += sameRoute(part.route || "", route)
              ? '<li><a class="is-current" href="' + href + '">' + escapeHtml(part.title || "") + "</a></li>"
              : itemHtml(href, part.title || "");
          }
        }
        html += "</ul></details></li>";
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
    if (navRoot.children && navRoot.children.length > 0) return;
    navRoot.innerHTML = fallbackHtml();
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

    const details = document.createElement("details");
    details.classList.add("nav-chapter");
    details.open = chapterHasCurrent(chapter, currentRoute);

    const summary = document.createElement("summary");
    summary.textContent = chapter.title || "";
    details.appendChild(summary);

    const sectionList = document.createElement("ul");
    sectionList.classList.add("nav-section-list");
    if (chapter.route) {
      const overview = mkItem(routeHref(chapter.route), "Overview", false);
      overview.firstChild.setAttribute("data-chapter-target", "true");
      sectionList.appendChild(overview);
    }
    for (const item of (chapter.items || [])) {
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
      sectionList.appendChild(node);
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
