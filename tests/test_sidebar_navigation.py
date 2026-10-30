"""File-level reader navigation: generated targets, scripts and optional browser checks.

Set REASBOOK_SIDEBAR_BROWSER_TEST=1 with Playwright installed to run the
browser cases as well. The browser serves an in-memory fixture, never a live site.
"""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "ReasBookWeb/scripts"))
import gen_sections as generator  # noqa: E402


def sidebar_payload(text):
    value = re.search(r"^def sidebarDataJson : String := (.+)$", text, re.M).group(1)
    return json.loads(json.loads(value))


def sidebar_scripts():
    source = (ROOT / "ReasBookWeb/ReasBookSite.lean").read_text()
    return dict(re.findall(r'def (\w+Script) : String := r##"\n(.*?)\n"##', source, re.S))


class SidebarInventoryTests(unittest.TestCase):
    def test_flat_paper_files_have_explicit_ownership_and_numeric_navigation(self):
        entries = [generator.Entry('papers', f'Book.{stem}', stem, f'book/{stem.lower()}/',
                                   'FlatPaper', 0, 0, 0, stem.lower())
                   for stem in ('Definition_2_1', 'Theorem_1_10', 'Lemma_1_2', 'Paper')]
        payload = sidebar_payload(generator.emit_sections(entries, source_root=self.source))
        paper = payload['papers'][0]
        self.assertEqual([file['title'] for file in paper['files']],
                         ['Lemma 1.2', 'Theorem 1.10', 'Definition 2.1'])
        self.assertIn('book/lemma_1_2/', paper['routes'])
        self.assertEqual(paper['home'], 'papers/flatpaper/')

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.source = self.repo / "ReasBook"
        self.chapter = self.source / "Books/SidebarDemo/Chap01"
        self.chapter.mkdir(parents=True)
        (self.source / "Papers").mkdir()
        (self.source / "lean-toolchain").write_text('leanprover/lean4:v4.30.0\n')
        (self.source / "lakefile.lean").write_text('lean_lib SidebarDemo where\n  srcDir := "Books"\n')
        (self.chapter.parent / "Book.lean").write_text("import SidebarDemo.Chap01\n")

    def generate(self):
        self.chapter.with_suffix('.lean').write_text(''.join(
            f'import SidebarDemo.Chap01.{path.stem}\n' for path in sorted(self.chapter.glob('*.lean'))))
        inventories = generator.collect_chapter_inventories(self.source)
        entries = generator.collect_entries(self.source, inventories)
        readers = generator.collect_reader_chapters(entries, inventories)
        payload = sidebar_payload(generator.emit_sections(entries, readers, source_root=self.source))
        generator.write_work_pages(self.repo, self.source, entries, readers)
        page = (self.repo / "ReasBookWeb/ReasBookSite/WorkPages/Books/SidebarDemo/Chap01.lean").read_text()
        chapter = payload["books"][0]["chapters"][0]
        self.assertEqual(chapter["sections"], [])
        for item in chapter["items"]:
            if item["anchor"]:
                self.assertEqual(page.count(f'id := "{item["anchor"]}"'), 1, item)
        return chapter["items"], page

    def test_one_entry_per_item_file_in_numeric_order(self):
        for name in ("Lemma_1_10", "Definition_1_2", "Theorem_1_3"):
            (self.chapter / f"{name}.lean").write_text("import Mathlib\n#check Nat\n#check Int\n")
        helper = self.chapter / "Definition_1_2/section13325.lean"
        helper.parent.mkdir()
        helper.write_text("def helper := 0\n")
        items, _ = self.generate()
        self.assertEqual([i["title"] for i in items], ["Definition 1.2", "Theorem 1.3", "Lemma 1.10"])
        self.assertEqual([Path(i["source"]).stem for i in items],
                         ["Definition_1_2", "Theorem_1_3", "Lemma_1_10"])
        self.assertNotIn("section13325", json.dumps(items))

    def test_empty_items_are_disabled_but_imported_statements_have_anchors(self):
        (self.chapter / "Lemma_1_1.lean").write_text("import Mathlib\n")
        (self.chapter / "Definition_1_2.lean").write_text("import SidebarDemo.Chap01.Definition_1_2.Body\n")
        helper = self.chapter / "Definition_1_2/Body.lean"
        helper.parent.mkdir()
        helper.write_text("structure Body where\n  field : Nat\n")
        items, page = self.generate()
        self.assertEqual(items[0]["anchor"], "")
        self.assertEqual(items[1]["anchor"], "definition-1-2")
        self.assertIn("no statement yet", page)

    def test_section_facades_share_one_inventory_with_rendered_reading_parts(self):
        sources = {
            "Section01": "import SidebarDemo.Chap01.Section01_part2\nimport SidebarDemo.Chap01.Section01_part10\n",
            "Section01_part2": "recall foo : True\n",
            "Section01_part10": "recall bar : True\n",
            "Section02": "import SidebarDemo.Chap01.Section01_part2\n",
            "Section03": "import Mathlib\n",
            "Section10": "recall baz : True\n",
        }
        for name, source in sources.items():
            (self.chapter / f"{name}.lean").write_text(source)
        items, page = self.generate()
        self.assertEqual([i["module"].rsplit(".", 1)[1] for i in items],
                         ["Section01_part2", "Section01_part10", "Section03", "Section10"])
        self.assertEqual(items[2]["anchor"], "")
        self.assertEqual(page.count("recall foo : True"), 1)
        self.assertNotIn("Section 02 — no statement yet", page)

    def test_section_importing_numbered_items_does_not_duplicate_file_entries(self):
        for number in range(1, 6):
            (self.chapter / f"Lemma_1_{number}.lean").write_text("recall foo : True\n")
        (self.chapter / "Section01.lean").write_text("import SidebarDemo.Chap01.Lemma_1_1\n")
        items, page = self.generate()
        self.assertEqual(len(items), 5)
        self.assertEqual(page.count("recall foo : True"), 5)
        home = (self.repo / "ReasBookWeb/ReasBookSite/WorkPages/Books/SidebarDemo.lean").read_text()
        self.assertIn("/chap01/)\n", home)
        self.assertNotIn("5 items", home)
        self.assertNotIn("#lemma-1-1", home)
        self.assertNotIn("Section index:", home)

    def test_home_and_excerpts_have_no_navigation_boilerplate(self):
        (self.chapter / "Definition_1_1.lean").write_text("#check Nat\n#check Int\n")
        _, page = self.generate()
        home = (self.repo / "ReasBookWeb/ReasBookSite/WorkPages/Books/SidebarDemo.lean").read_text()
        self.assertIn('class := "reader-home-links"', home)
        self.assertIn('class := "reader-chapter-grid"', home)
        self.assertIn('[Documentation](/ReasBook/docs/ReasBook/SidebarDemo/Book.html)', home)
        self.assertNotIn('Choose a chapter', home)
        self.assertNotIn('Additional statements', page)
        self.assertNotIn('This chapter indexes', page)
        self.assertIn('#doc (Page) "Chapter 01"', page)
        self.assertIn('class := "reader-statement-title"', page)
        self.assertIn('(role := "heading") («aria-level» := "3")', page)
        self.assertIn('class := "reader-statement-links"', page)
        self.assertIn('Proofs omitted.', page)

    def test_named_chapter_agrees_across_home_sidebar_and_item_reader(self):
        book = "FirstOrderMethodsOptimization_Beck_2017"
        chapter = self.source / "Books" / book / "Chap01"
        chapter.mkdir(parents=True)
        (chapter.parent / "Book.lean").write_text(f"import {book}.Chap01\n")
        # Old aggregators repeat the book name instead of identifying the chapter.
        (chapter.with_suffix('.lean')).write_text(
            f"import {book}.Chap01.Definition_1_1\n"
            "/-!\n# Chapter 01 — First-Order Methods in Optimization (Beck, 2017)\n-/\n")
        (chapter / "Definition_1_1.lean").write_text("import Mathlib\n#check Nat\n")
        lakefile = self.source / "lakefile.lean"
        lakefile.write_text(lakefile.read_text() + f'lean_lib {book} where\n  srcDir := "Books"\n')
        inventories = generator.collect_chapter_inventories(self.source)
        entries = generator.collect_entries(self.source, inventories)
        readers = generator.collect_reader_chapters(entries, inventories)
        payload = sidebar_payload(generator.emit_sections(entries, readers, source_root=self.source))
        generator.write_work_pages(self.repo, self.source, entries, readers)
        named = next(item for item in payload['books'] if item['slug'] == book.lower())
        title = "Chapter 01 — Vector Spaces"
        route = named['chapters'][0]['route']
        self.assertEqual(named['chapters'][0]['title'], title)
        pages = self.repo / "ReasBookWeb/ReasBookSite/WorkPages/Books"
        home = (pages / f"{book}.lean").read_text()
        page = (pages / book / "Chap01.lean").read_text()
        self.assertIn(f"- [{title}]({generator.portable_site_link(route)})", home)
        self.assertIn(f'#doc (Page) "{title}"', page)
        self.assertNotIn('1 items', home)
        self.assertEqual(generator.chapter_title_for_book('UnknownBook', 1), 'Chapter 01')

    def test_introduction_chapter_zero_keeps_its_title_and_sections(self):
        book = "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025"
        chapter = self.source / "Books" / book / "Chap00"
        chapter.mkdir(parents=True)
        (chapter.parent / "Book.lean").write_text(f"import {book}.Chap00\n")
        chapter.with_suffix('.lean').write_text(f"import {book}.Chap00.section01\n")
        (chapter / "section01.lean").write_text("import Mathlib\n/-!\n# Section 0.1\n-/\n")
        lakefile = self.source / "lakefile.lean"
        lakefile.write_text(lakefile.read_text() + f'lean_lib {book} where\n  srcDir := "Books"\n')
        entries = generator.collect_entries(self.source)
        payload = sidebar_payload(generator.emit_sections(entries, source_root=self.source))
        generator.write_work_pages(self.repo, self.source, entries)
        named = next(item for item in payload['books'] if item['slug'] == book.lower())
        self.assertEqual(named['chapters'][0]['title'], "Chapter 00 — Introduction")
        self.assertEqual(len(named['chapters'][0]['sections']), 1)
        home = (self.repo / f"ReasBookWeb/ReasBookSite/WorkPages/Books/{book}.lean").read_text()
        self.assertIn("[Chapter 00 — Introduction]", home)
        aggregation = next(entry for entry in entries if generator.is_chapter_entry(entry))
        self.assertEqual(aggregation.title, "Chapter 00 — Introduction")

    def test_theme_has_bypass_and_reading_semantics(self):
        source = (ROOT / 'ReasBookWeb/ReasBookSite.lean').read_text()
        self.assertIn('<html lang="en">', source)
        self.assertIn('class="reader-skip-link"', source)
        self.assertIn('id="main-content" tabindex="-1"', source)
        self.assertIn('let pagePath := String.intercalate', source)
        self.assertIn('pre.setAttribute("translate", "no")', source)

    def test_statement_header_directives_have_strictly_nested_fences(self):
        lines = generator.statement_blocks('#check Nat\n', 'Definition 1.1',
                                           '[Lean source](source.lean)', 'definition-1-1')
        fences = []
        for line in lines:
            if opening := re.match(r'^(:{3,})html\b', line):
                width = len(opening[1])
                if fences:
                    self.assertLess(width, fences[-1])
                fences.append(width)
            elif re.fullmatch(r':{3,}', line):
                self.assertEqual(len(line), fences.pop())
        self.assertEqual(fences, [])

    @unittest.skipUnless(shutil.which("node"), "Node is not installed")
    def test_embedded_javascript_parses(self):
        for name, script in sidebar_scripts().items():
            with self.subTest(script=name):
                result = subprocess.run(["node", "--check"], input=script, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)


@unittest.skipUnless(os.environ.get("REASBOOK_SIDEBAR_BROWSER_TEST") == "1",
                     "Set REASBOOK_SIDEBAR_BROWSER_TEST=1 to run browser checks")
class SidebarBrowserTests(unittest.TestCase):
    def test_flat_paper_pages_keep_file_navigation_in_main_and_fallback(self):
        from playwright.sync_api import sync_playwright

        scripts = sidebar_scripts()
        data = {'books': [], 'papers': [{'slug': 'demo', 'title': 'Demo paper',
            'home': 'papers/demo/', 'sections': [], 'routes': ['book/theorem_1_1/'],
            'files': [{'title': 'Theorem 1.1', 'route': 'book/theorem_1_1/', 'module': 'Book.Theorem_1_1'}]}]}
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                selected = [scripts['sidebarItemStateScript']]
                if not fallback:
                    selected.append(scripts['navLinkRewriteScript'])
                selected.append(scripts['sidebarFallbackScript'])
                init = 'window.__versoSiteRoot="/ReasBook/native/";window.__reasbookSidebarData=' + json.dumps(data) + ';'
                html = ('<html><head><base href="/ReasBook/native/">' +
                        ''.join('<script>' + script + '</script>' for script in [init, *selected]) +
                        '</head><body><nav id="sidebar-nav-root"></nav><div class="main"><h1>Theorem 1.1</h1></div></body></html>')
                page = browser.new_page()
                errors = []
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.route('**/*', lambda route: route.fulfill(status=200, content_type='text/html', body=html))
                page.goto('https://preview.test/ReasBook/native/book/theorem_1_1/')
                self.assertEqual(page.locator('.nav-work-title').inner_text(), 'Demo paper')
                self.assertEqual(page.locator('.nav-file-item [aria-current="page"]').inner_text(), 'Theorem 1.1')
                self.assertEqual(page.locator('#sidebar-nav-root').get_by_role('link', name='Home', exact=True).count(), 0)
                self.assertEqual(errors, [])
                page.close()
            browser.close()

    def test_home_typography_and_contents_are_responsive_without_javascript(self):
        from playwright.sync_api import expect, sync_playwright

        css = (ROOT / "ReasBookWeb/static_files/style.css").read_text()
        title = "Convex Analysis and Monotone Operator Theory in Hilbert Spaces"
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            page = browser.new_page(java_script_enabled=False)
            for tag in ('article', 'div class="frontpage"'):
                for count in (1, 3, 20):
                    closing_tag = tag.split()[0]
                    labels = [generator.chapter_title_for_book(
                        "ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017", i)
                        for i in range(1, count + 1)]
                    chapters = ''.join(f'<li><p><a href="chapter{i}/">{label}</a></p></li>'
                                       for i, label in enumerate(labels, 1))
                    page.set_content(f'''<html><head><style>{css}</style></head><body>
                        <div class="main"><div class="wrap"><{tag}><h1>{title}</h1>
                        <div class="reader-home-links"><ul>
                        <li><p><a href="docs/Book.html">Documentation</a></p></li>
                        <li><p><a href="source/">Lean source</a></p></li></ul></div>
                        <section><h2>Chapters</h2><div class="reader-chapter-grid">
                        <ul>{chapters}</ul></div></section></{closing_tag}></div></div>
                        </body></html>''')
                    for width in (320, 390, 768, 1000, 1001, 1440):
                        with self.subTest(tag=tag, count=count, width=width):
                            page.set_viewport_size({"width": width, "height": 1000})
                            self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
                            heading = page.locator('h1')
                            self.assertIn('Georgia', heading.evaluate('n => getComputedStyle(n).fontFamily'))
                            grid = page.locator('.reader-chapter-grid ul')
                            columns = grid.evaluate('n => getComputedStyle(n).gridTemplateColumns.split(" ").length')
                            self.assertEqual(columns, 1 if width <= 640 or count <= 4 else 2)
                            links = grid.get_by_role('link')
                            expect(links).to_have_count(count)
                            for index, link in enumerate(links.all(), 1):
                                expect(link).to_have_text(labels[index - 1])
                                self.assertGreaterEqual(link.bounding_box()['height'], 44)
                            docs = page.get_by_role('link', name='Documentation', exact=True)
                            self.assertEqual(docs.evaluate('n => getComputedStyle(n).color'), 'rgb(81, 64, 119)')
                            self.assertEqual(docs.evaluate('n => getComputedStyle(n).backgroundColor'), 'rgba(0, 0, 0, 0)')
                            docs.focus()
                            page.keyboard.press('Tab')
                            expect(page.get_by_role('link', name='Lean source', exact=True)).to_be_focused()
                            page.keyboard.press('Tab')
                            expect(links.first).to_be_focused()
                            self.assertNotEqual(links.first.evaluate('n => getComputedStyle(n).outlineStyle'), 'none')
            # Home and chapter retain the same reading typography.
            page.set_content(f'<html><head><style>{css}</style></head><body>'
                             '<div class="main"><h1>Chapter 01</h1></div></body></html>')
            self.assertIn('Georgia', page.locator('h1').evaluate('n => getComputedStyle(n).fontFamily'))
            browser.close()

    def test_navigation_and_fallback_preserve_fragments_history_and_mobile_scroll(self):
        from playwright.sync_api import expect, sync_playwright

        scripts = sidebar_scripts()
        css = (ROOT / "ReasBookWeb/static_files/style.css").read_text()
        chapter_route = "books/demo/chapters/chap01/"
        items = [{"title": f"Lemma 1.{i}", "anchor": f"lemma-1-{i}",
                  "source": f"ReasBook/Books/Demo/Chap01/Lemma_1_{i}.lean"}
                 for i in range(1, 81)]
        items.append({"title": 'Empty <item> "quoted"', "anchor": "", "source": "Empty.lean"})
        chapter_title = "Chapter 01 — The Fundamental Group and Some of Its Applications"
        data = {"books": [{"slug": "demo", "title": "Demo", "home": "books/demo/", "chapters": [
            {"title": chapter_title, "route": chapter_route, "items": items, "sections": []},
            {"title": "Chapter 02", "route": "books/demo/chapters/chap02/", "items": [], "sections": []},
        ]}], "papers": []}
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                for prefix in ("/ReasBook/", "/proxy/3000/ReasBook/versions/v4.30.0/sites/demo/"):
                    with self.subTest(fallback=fallback, prefix=prefix):
                        page = browser.new_page(viewport={"width": 1440, "height": 1000})
                        errors = []
                        page.on("pageerror", lambda error: errors.append(str(error)))
                        selected = [scripts["sidebarItemStateScript"]]
                        if not fallback:
                            selected.append(scripts["navLinkRewriteScript"])
                        selected.append(scripts["sidebarFallbackScript"])
                        script = (f"window.__versoSiteRoot={json.dumps(prefix)};"
                                  f"window.__reasbookSidebarData={json.dumps(data)};")
                        html = (f'<html><head><base href="{prefix}"><style>{css}</style>'
                                + "".join(f"<script>{s}</script>" for s in [script, *selected])
                                + '</head><body><header><nav id="sidebar-nav-root"></nav></header><div class="main">'
                                + '<div class="reader-home-links"></div>'
                                + '<a href="/all-books/" data-reader-collection>All books and papers</a>'
                                + '<code class="hl lean block">theorem example : True</code>'
                                + "".join(f'<div data-reasbook-statement="true" id="lemma-1-{i}" style="height:250px">Statement {i}</div>'
                                          for i in range(1, 81)) + "</div></body></html>")
                        page.route("**/*", lambda route: route.fulfill(status=200, content_type="text/html", body=html))
                        base = "https://preview.test" + prefix + chapter_route
                        page.goto(base + "#lemma-1-70")
                        expect(page.locator('[data-reader-collection]')).to_have_attribute('href', '/all-books/')
                        expect(page.locator('code.hl.lean.block')).to_have_attribute('tabindex', '0')
                        expect(page.locator('code.hl.lean.block')).to_have_attribute('aria-label', 'Lean code')
                        nav = page.locator("#sidebar-nav-root")
                        self.assertEqual(nav.locator(".nav-file-item").count(), 81)
                        self.assertEqual(nav.get_by_role("link", name="Home", exact=True).count(), 0)
                        expect(nav.locator("a.nav-work-title")).to_have_text("Demo")
                        expect(nav.locator("a.nav-work-title")).to_have_attribute("href", prefix + "books/demo/")
                        self.assertEqual(nav.locator(".nav-count, .nav-work, .nav-group-label").count(), 0)
                        self.assertEqual(nav.get_by_role("link", name="Documentation", exact=True).count(), 0)
                        expect(nav.locator(".nav-chapter > summary").first).to_have_text(chapter_title)
                        # Every navigation level must keep the same sans family.
                        for selector in (".nav-work-title", ".nav-chapter > summary",
                                         ".nav-chapter a[data-chapter-target]", ".nav-file-item > a"):
                            family = nav.locator(selector).first.evaluate("n => getComputedStyle(n).fontFamily")
                            self.assertIn("sans-serif", family)
                            self.assertNotIn("Georgia", family)
                        self.assertEqual(nav.locator("a.is-current").inner_text(), "Lemma 1.70")
                        self.assertEqual(nav.locator("a[aria-current=location]").count(), 1)
                        self.assertIn('Empty <item> "quoted"', nav.locator("[aria-disabled]").inner_text())
                        self.assertEqual(nav.locator(".nav-chapter[open]").count(), 1)
                        self.assertGreater(nav.evaluate("n => n.scrollTop"), 0)
                        nav.get_by_role("link", name="Lemma 1.71", exact=True).click()
                        page.wait_for_url("**/#lemma-1-71")
                        expect(nav.locator("a.is-current")).to_have_text("Lemma 1.71")
                        page.go_back()
                        page.wait_for_url("**/#lemma-1-70")
                        expect(nav.locator("a.is-current")).to_have_text("Lemma 1.70")
                        page.go_forward()
                        page.wait_for_url("**/#lemma-1-71")
                        expect(nav.locator("a.is-current")).to_have_text("Lemma 1.71")
                        page.set_viewport_size({"width": 390, "height": 844})
                        page.goto(base + "index.html#lemma-1-70")
                        self.assertEqual(nav.locator("a.is-current").inner_text(), "Lemma 1.70")
                        expect(nav).not_to_be_visible()
                        toggle = page.locator("#reader-nav-toggle")
                        expect(toggle).to_have_attribute("aria-expanded", "false")
                        page.set_viewport_size({"width": 1440, "height": 1000})
                        expect(nav).to_be_visible()
                        expect(toggle).not_to_be_visible()
                        expect(nav.locator("a.is-current")).to_be_in_viewport()
                        page.set_viewport_size({"width": 390, "height": 844})
                        expect(nav).not_to_be_visible()
                        toggle.click()
                        expect(nav).to_be_visible()
                        expect(toggle).to_have_attribute("aria-expanded", "true")
                        self.assertLessEqual(nav.evaluate("n => n.clientHeight"), 422)
                        self.assertTrue(page.evaluate("document.documentElement.scrollWidth <= innerWidth"))
                        self.assertGreater(page.evaluate("window.scrollY"), 0)
                        page.keyboard.press("Escape")
                        expect(nav).not_to_be_visible()
                        expect(toggle).to_be_focused()
                        toggle.press("Enter")
                        nav.get_by_role("link", name="Lemma 1.71", exact=True).click()
                        page.wait_for_url("**/#lemma-1-71")
                        expect(nav).not_to_be_visible()
                        expect(nav.locator("a.is-current")).to_have_text("Lemma 1.71")
                        self.assertGreaterEqual(page.locator("#lemma-1-71").bounding_box()["y"], 44)
                        toggle.click()
                        nav.get_by_role("link", name="Overview", exact=True).first.click()
                        page.wait_for_url(base)
                        expect(nav.locator("a.is-current")).to_have_text("Overview")
                        expect(nav).not_to_be_visible()
                        toggle.click()
                        nav.locator("a.nav-work-title").click()
                        page.wait_for_url("https://preview.test" + prefix + "books/demo/")
                        expect(nav.locator("a.nav-work-title")).to_have_attribute("aria-current", "page")
                        expect(nav).not_to_be_visible()
                        page.goto("https://preview.test" + prefix)
                        expect(nav.locator("a.nav-work-title")).to_have_text("Demo")
                        expect(nav.locator("a.nav-work-title")).to_have_attribute("aria-current", "page")
                        self.assertEqual(nav.get_by_role("link", name="Documentation", exact=True).count(), 0)
                        self.assertEqual(errors, [])
                        page.close()
            browser.close()


if __name__ == "__main__":
    unittest.main()
