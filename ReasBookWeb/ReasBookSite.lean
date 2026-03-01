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
    return { kind: "", work: null, route: route };
  }

  function escapeHtml(s) {
    return String(s || "")
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }

  function itemHtml(href, label) {
    return '<li><a href="' + href + '">' + escapeHtml(label) + '</a></li>';
  }

  function renderCurrentWork(current) {
    const work = current.work;
    const route = current.route;
    if (!work) return "";

    let html = "<li><details open><summary>" + escapeHtml(work.title || "") + "</summary><ul>";
    if (work.home) {
      const href = siteRoot + trimSlashes(work.home) + "/";
      html += sameRoute(work.home, route)
        ? '<li><a class="is-current" href="' + href + '">Home</a></li>'
        : itemHtml(href, "Home");
    }

    if (current.kind === "book" && Array.isArray(work.chapters) && work.chapters.length > 0) {
      for (const chapter of work.chapters) {
        html += "<li><details open><summary>" + escapeHtml(chapter.title || "") + "</summary><ul>";
        if (chapter.route) {
          const href = siteRoot + trimSlashes(chapter.route) + "/";
          html += sameRoute(chapter.route, route)
            ? '<li><a class="is-current" href="' + href + '">Overview</a></li>'
            : itemHtml(href, "Overview");
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

    html += "</ul></details></li>";
    return html;
  }

  function fallbackHtml() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const current = findCurrentWork(navData);
    let html = "<ol>";
    html += itemHtml(siteRoot, "Home");
    html += itemHtml(siteRoot + "docs/", "Documentation");

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
    if (isCurrent) a.classList.add("is-current");
    return a;
  }

  function mkItem(href, label, isCurrent) {
    const li = document.createElement("li");
    li.appendChild(mkAnchor(href, label, isCurrent));
    return li;
  }

  function mkLabel(text) {
    const li = document.createElement("li");
    li.classList.add("nav-group-label");
    li.textContent = text;
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
      sectionList.appendChild(mkItem(routeHref(chapter.route), "Overview", sameRoute(chapter.route, currentRoute)));
    }
    for (const section of (chapter.sections || [])) {
      sectionList.appendChild(mkSectionNode(section, currentRoute, chapter.number));
    }

    details.appendChild(sectionList);
    li.appendChild(details);
    return li;
  }

  function mkBookTree(work, currentRoute) {
    const li = document.createElement("li");
    li.classList.add("nav-current-work");
    const details = document.createElement("details");
    details.classList.add("nav-work");
    details.open = true;

    const summary = document.createElement("summary");
    summary.textContent = work.title || "";
    details.appendChild(summary);

    const tree = document.createElement("ul");
    tree.classList.add("nav-work-tree");
    if (work.home) {
      tree.appendChild(mkItem(routeHref(work.home), "Home", sameRoute(work.home, currentRoute)));
    }

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

    details.appendChild(tree);
    li.appendChild(details);
    return li;
  }

  function mkPaperTree(work, currentRoute) {
    const li = document.createElement("li");
    li.classList.add("nav-current-work");
    const details = document.createElement("details");
    details.classList.add("nav-work");
    details.open = true;

    const summary = document.createElement("summary");
    summary.textContent = work.title || "";
    details.appendChild(summary);

    const sectionList = document.createElement("ul");
    sectionList.classList.add("nav-work-tree");
    if (work.home) {
      sectionList.appendChild(mkItem(routeHref(work.home), "Home", sameRoute(work.home, currentRoute)));
    }
    for (const section of (work.sections || [])) {
      if (!section.route) continue;
      sectionList.appendChild(mkSectionNode(section, currentRoute, 0));
    }

    details.appendChild(sectionList);
    li.appendChild(details);
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

    let rel;
    if (p.startsWith(siteRoot)) rel = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) rel = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) rel = p.slice(1);
    else rel = p;

    rel = normalizeRoute(canonicalRelPath(rel));
    if (!rel) return siteRoot + qh;
    return siteRoot + rel + qh;
  }

  function rewriteAllAnchors() {
    for (const a of document.querySelectorAll("a[href]")) {
      const oldHref = (a.getAttribute("href") || "").trim();
      const newHref = normalizeInternalHref(oldHref);
      if (newHref && newHref !== oldHref) a.setAttribute("href", newHref);
    }
  }

  function onClick(ev) {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    const a = ev.target && ev.target.closest ? ev.target.closest("a[href]") : null;
    if (!a) return;
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
        list.appendChild(mkItem(siteRoot, "Home", sameRoute("", current.route)));
        list.appendChild(mkItem(siteRoot + "docs/", "Documentation", false));
        if (current.work) {
          list.appendChild(mkLabel(current.kind === "book" ? "Current Book" : "Current Paper"));
          if (current.kind === "book") {
            list.appendChild(mkBookTree(current.work, current.route));
          } else if (current.kind === "paper") {
            list.appendChild(mkPaperTree(current.work, current.route));
          }
        } else {
          list.appendChild(mkSectionGroup("Books", navData.books || [], true));
          list.appendChild(mkSectionGroup("Papers", navData.papers || [], true));
        }
      } catch (err) {
        console.error("Failed to build sidebar navigation", err);
        return;
      }
      navRoot.innerHTML = "";
      navRoot.appendChild(list);
      const currentNode = navRoot.querySelector("a.is-current");
      if (currentNode && currentNode.scrollIntoView) {
        currentNode.scrollIntoView({ block: "center", inline: "nearest" });
      }
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
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <base href={{siteRoot}}/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href={{staticRoot}}/>
          <script>{{Html.text false siteRootScript}}</script>
          <script>{{Html.text false sidebarDataScript}}</script>
          <script>{{Html.text false navLinkRewriteScript}}</script>
          <script>{{Html.text false sidebarFallbackScript}}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation" id="sidebar-nav-root"></nav>
            </div>
          </header>
          <div class="main" role="main">
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
  mkLink href := { shortDescription := "doc", description := "API documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
