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
    def test_registered_book_titles_keep_their_bibliographic_identity(self):
        for book, title in generator.BOOK_TITLES.items():
            with self.subTest(book=book):
                layout = generator.book_title_layout(book)
                self.assertEqual(f'{layout["display_title"]} ({layout["citation"]})', title)
                self.assertEqual(layout['navigation_title'], layout['display_title'])
        self.assertEqual(generator.book_title_layout('UnknownBook'), {})

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

    def test_mixed_reading_files_cannot_replace_the_chapter_destination(self):
        for stem in ('Section01', 'Section02', 'Definition_1_1'):
            (self.chapter / f'{stem}.lean').write_text('import Mathlib\n#check Nat\n')
        self.chapter.with_suffix('.lean').write_text('import SidebarDemo.Chap01.Section01\n')
        inventories = generator.collect_chapter_inventories(self.source)
        entries = generator.collect_entries(self.source, inventories)
        payload = sidebar_payload(generator.emit_sections(entries, source_root=self.source))
        chapter = payload['books'][0]['chapters'][0]
        canonical = next(entry for entry in entries if generator.is_chapter_entry(entry))
        self.assertEqual(chapter['route'], canonical.route)

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
        self.assertIn('(role := "heading") («aria-level» := "2")', page)
        self.assertNotIn("# Statements", page)
        self.assertIn('id := "statements-1"', page)
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
        self.assertEqual(named['title'], generator.BOOK_TITLES[book])
        self.assertEqual(named['display_title'], 'First-Order Methods in Optimization')
        self.assertEqual(named['citation'], 'Beck, 2017')
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

    def test_book_contents_use_the_numbering_and_topics_of_the_source(self):
        self.assertEqual(generator.book_section_heading('AlgebraicTopology_May_1999', 1, 2),
                         '1.2 — The Fundamental Group')
        self.assertEqual(generator.book_section_heading('AlgebraicTopology_May_1999', 1, 8), 'Problems')
        self.assertEqual(generator.book_section_heading('ConvexAnalysis_Rockafellar_1970', 5, 23),
                         '§23 — Directional Derivatives and Subgradients')
        self.assertEqual(generator.chapter_title_for_book('ConvexAnalysis_Rockafellar_1970', 5),
                         'Part V — Differential Theory')
        self.assertEqual(generator.book_section_heading('IntroductiontoRealAnalysisVolumeI_JiriLebl_2025', 0, 3),
                         '0.3 — Basic Set Theory')
        self.assertEqual(generator.chapter_title_for_book('CombinatorialGroupTheory_Magnus_2004', 5),
                         'Chapter 05 — Small Cancellation Theory')

    def test_authored_section_heading_is_not_replaced_by_a_directory_number(self):
        path = self.chapter / 'Section01.lean'
        path.write_text('import Mathlib\n/-!\n# Section 1.1 — Limits: a first example\n-/\n#check Nat\n')
        entries = generator.collect_entries(self.source)
        entry = next(entry for entry in entries if entry.stem == 'section01')
        self.assertEqual(generator.readme_label(entry), '1.1 — Limits: a first example')

    def test_full_reading_pages_receive_the_named_section_title(self):
        book = 'Analysis2_Tao_2022'
        path = self.source / 'Books' / book / 'Chap01/section01.lean'
        path.parent.mkdir(parents=True)
        path.write_text('import Mathlib\n/-!\n# Section 1.1\n-/\n#check Nat\n')
        entries = generator.collect_entries(self.source)
        entry = next(entry for entry in entries if entry.book_or_paper == book)
        self.assertEqual(entry.title, '1.1 — Definitions and Examples')

    def test_helper_docstrings_do_not_create_fake_reading_sections(self):
        path = self.chapter / 'helper_bridge.lean'
        path.write_text('import Mathlib\n/-- Section 1.1: helper for the imported theorem. -/\n'
                        'theorem bridge : True := by trivial\n')
        self.assertIsNone(generator.module_doc_title(path))

    def test_clause_suffixes_do_not_invent_book_sections(self):
        for book, stem in (
            ('FirstOrderMethodsOptimization_Beck_2017', 'Theorem_10_51_1'),
            ('ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017', 'Theorem_3_27_1'),
            ('IntroductoryLecturesOnConvexOptimization_Nesterov_2004', 'Lemma_2_21_1'),
        ):
            chapter = int(stem.split('_')[1])
            path = self.source / 'Books' / book / f'Chap{chapter:02d}' / f'{stem}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('#check Nat\n')
            with self.subTest(book=book):
                self.assertEqual(generator.parse_book_item(path, self.source).section_num, 0)

    def test_named_sections_link_to_the_heading_that_owns_the_items(self):
        book = 'AlgebraicTopology_May_1999'
        chapter = self.source / 'Books' / book / 'Chap01'
        chapter.mkdir(parents=True)
        (chapter.parent / 'Book.lean').write_text(f'import {book}.Chap01\n')
        chapter.with_suffix('.lean').write_text(f'import {book}.Chap01.Definition_1_2_1\n')
        (chapter / 'Definition_1_2_1.lean').write_text('#check Nat\n')
        (chapter / 'Problem_1_8_1.lean').write_text('#check Int\n')
        lakefile = self.source / 'lakefile.lean'
        lakefile.write_text(lakefile.read_text() + f'lean_lib {book} where\n  srcDir := "Books"\n')
        inventories = generator.collect_chapter_inventories(self.source)
        entries = generator.collect_entries(self.source, inventories)
        readers = generator.collect_reader_chapters(entries, inventories)
        payload = sidebar_payload(generator.emit_sections(entries, readers, source_root=self.source))
        generator.write_work_pages(self.repo, self.source, entries, readers)
        named = next(work for work in payload['books'] if work['slug'] == book.lower())
        groups = named['chapters'][0]['item_sections']
        self.assertEqual([group['label'] for group in groups], ['1.2 — The Fundamental Group', 'Problems'])
        page = (self.repo / f'ReasBookWeb/ReasBookSite/WorkPages/Books/{book}/Chap01.lean').read_text()
        for group in groups:
            self.assertEqual(page.count(f'id := "{group["anchor"]}"'), 1)
            self.assertIn(f'# {group["label"]}', page)

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

    def test_nesterov_legacy_identifier_does_not_override_2018_bibliography(self):
        book = "IntroductoryLecturesOnConvexOptimization_Nesterov_2004"
        self.assertEqual(generator.BOOK_TITLES[book],
                         "Lectures on Convex Optimization (Nesterov, 2018)")
        self.assertEqual(sorted(generator.BOOK_CHAPTER_TITLES[book]), list(range(1, 8)))
        self.assertEqual(generator.chapter_title_for_book(book, 4),
                         "Chapter 04 — Second-Order Methods")
        self.assertEqual(generator.chapter_title_for_book(book, 7),
                         "Chapter 07 — Optimization in Relative Scale")
        self.assertIn("2004", generator.PAPER_TITLES["SmoothMinimization_Nesterov_2004"])

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
    def test_book_bibliography_is_separate_and_repeated_enhancement_is_safe(self):
        from playwright.sync_api import expect, sync_playwright

        book = 'ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017'
        title = generator.BOOK_TITLES[book]
        layout = generator.book_title_layout(book)
        work = {'slug': 'bauschke', 'title': title, **layout,
                'home': 'books/bauschke/', 'chapters': []}
        scripts = sidebar_scripts()
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                page = browser.new_page()
                errors = []
                page.on('pageerror', lambda error: errors.append(str(error)))
                selected = [scripts['sidebarItemStateScript']]
                if not fallback:
                    selected.append(scripts['navLinkRewriteScript'])
                selected.append(scripts['sidebarFallbackScript'])
                init = 'window.__versoSiteRoot="/ReasBook/";window.__reasbookSidebarData=' + json.dumps({'books': [work], 'papers': []}) + ';'
                html = ('<html><head>' + ''.join('<script>' + script + '</script>' for script in [init, *selected])
                        + '</head><body><nav id="sidebar-nav-root"></nav><div class="main"><h1>' + title
                        + '</h1><section id="credits">Formalization contributors: Yifan Bai, Zichen Wang, Zaiwen Wen</section></div></body></html>')
                page.route('**/*', lambda route: route.fulfill(status=200, content_type='text/html', body=html))
                page.goto('https://preview.test/ReasBook/' + work['home'])
                expect(page.locator('.main h1')).to_have_text(layout['display_title'])
                expect(page.locator('.reader-bibliography')).to_have_text(layout['citation'])
                expect(page.locator('.nav-work-title')).to_have_attribute('aria-label', title)
                expect(page.locator('.nav-work-citation')).to_have_text(layout['citation'])
                self.assertEqual(page.title().count(title), 1)
                page.evaluate(scripts['sidebarFallbackScript'])
                expect(page.locator('.reader-bibliography')).to_have_count(1)
                expect(page.locator('#credits')).to_have_text('Formalization contributors: Yifan Bai, Zichen Wang, Zaiwen Wen')
                self.assertEqual(errors, [])
                page.close()
            browser.close()

    def test_long_paper_title_keeps_canonical_identity_in_both_renderers(self):
        from playwright.sync_api import expect, sync_playwright

        scripts = sidebar_scripts()
        title = generator.paper_title('BFGSMinimumQOrder_Liu_2026')
        layout = generator.paper_title_layout('BFGSMinimumQOrder_Liu_2026')
        paper = {'slug': 'bfgs', 'title': title, **layout, 'home': 'papers/bfgs/',
                 'sections': [], 'routes': ['book/notation_1_1/'],
                 'files': [{'title': 'Notation 1.1', 'route': 'book/notation_1_1/'}]}
        data = {'books': [], 'papers': [paper]}
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                for route, heading in (('papers/bfgs/', title),
                                       ('book/notation_1_1/', 'Notation 1.1')):
                    page = browser.new_page()
                    errors = []
                    page.on('pageerror', lambda error: errors.append(str(error)))
                    selected = [scripts['sidebarItemStateScript']]
                    if not fallback:
                        selected.append(scripts['navLinkRewriteScript'])
                    selected.append(scripts['sidebarFallbackScript'])
                    init = 'window.__versoSiteRoot="/ReasBook/";window.__reasbookSidebarData=' + json.dumps(data) + ';'
                    html = ('<html><head>' + ''.join('<script>' + script + '</script>' for script in [init, *selected])
                            + '</head><body><nav id="sidebar-nav-root"></nav><div class="main"><h1>' + heading
                            + '</h1><pre id="native"><code data-verso-hover="original">Nat</code></pre>'
                            + '<p class="reader-attribution">Lean contributor: Chenyi Li</p></div></body></html>')
                    page.route('**/*', lambda request: request.fulfill(status=200, content_type='text/html', body=html))
                    page.goto('https://preview.test/ReasBook/' + route)
                    expect(page.locator('.main h1')).to_have_text(layout['display_title'] if route == paper['home'] else heading)
                    expect(page.locator('.nav-work-name')).to_have_text(layout['navigation_title'])
                    expect(page.locator('.nav-work-title')).to_have_attribute('aria-label', title)
                    expect(page.locator('.reader-bibliography')).to_contain_text(layout['citation'])
                    self.assertEqual(page.title().count(title), 1)
                    if route != paper['home']:
                        expect(page.locator('.reader-bibliography a')).to_have_attribute('href', '/ReasBook/' + paper['home'])
                    page.evaluate(scripts['sidebarFallbackScript'])
                    expect(page.locator('.reader-bibliography')).to_have_count(1)
                    expect(page.locator('#native code')).to_have_attribute('data-verso-hover', 'original')
                    expect(page.locator('.reader-attribution')).to_have_text('Lean contributor: Chenyi Li')
                    self.assertEqual(errors, [])
                    page.close()
            browser.close()

    def test_actual_theme_metadata_uses_device_viewport_and_allows_text_zoom(self):
        from playwright.sync_api import expect, sync_playwright

        source = (ROOT / 'ReasBookWeb/ReasBookSite.lean').read_text()
        metadata = ''.join(re.findall(r'<meta\b[^>]+/>', source))
        css = (ROOT / 'ReasBookWeb/static_files/style.css').read_text()
        scripts = sidebar_scripts()
        init = 'window.__versoSiteRoot="/ReasBook/";window.__reasbookSidebarData={books:[],papers:[]};'
        html = ('<html><head>' + metadata + '<style>' + css + '</style>'
            + ''.join('<script>' + script + '</script>' for script in [init, *scripts.values()])
            + '</head><body><nav id="sidebar-nav-root"></nav><div class="main"><h1>Convex Analysis and Monotone Operator Theory</h1>'
            + '<div class="reader-chapter-grid"><ul><li><p><a href="#chapter">Chapter 01 — Background</a></p></li></ul></div></div></body></html>')
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            page = browser.new_page(viewport={'width': 390, 'height': 844}, is_mobile=True, has_touch=True)
            page.route('**/*', lambda route: route.fulfill(status=200, content_type='text/html', body=html))
            page.goto('https://preview.test/ReasBook/', wait_until='networkidle')
            self.assertEqual(page.evaluate('innerWidth'), 390)
            expect(page.locator('#reader-nav-toggle')).to_be_visible()
            page.locator('#reader-nav-toggle').tap()
            expect(page.locator('#sidebar-nav-root')).to_be_visible()
            page.keyboard.press('Escape')
            page.evaluate("document.documentElement.style.fontSize = '200%'")
            self.assertEqual(page.evaluate('innerWidth'), 390)
            self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
            browser.close()

    def test_title_formatting_preserves_aliases_rich_nodes_and_inline_prose(self):
        from playwright.sync_api import expect, sync_playwright

        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            page = browser.new_page()
            page.set_content('''<div class="main">
                <h2 id="section"><a id="old-alias"></a>1.1 — <em>Topology</em>
                  of <a href="#reference">spaces</a> <code data-test="math">ℝ</code></h2>
                <ul><li><p>See <a href="#reference">1.1 — A reference</a> for details.</p></li></ul>
                <div class="reader-chapter-grid"><ul><li><p><a href="#section">1.1 — Topology</a></p></li></ul></div>
                </div>''')
            page.evaluate('''() => {
                window.originalTitleCode = document.querySelector('h2 code');
                window.originalTitleLink = document.querySelector('h2 a[href]');
                window.originalTitleLink.addEventListener('click', event => {
                    event.preventDefault(); window.titleLinkClicked = true;
                });
            }''')
            page.evaluate(sidebar_scripts()['sidebarItemStateScript'])
            expect(page.locator('#old-alias')).to_have_count(1)
            expect(page.locator('h2 > .reader-title-number')).to_have_text('1.1')
            self.assertTrue(page.evaluate('document.querySelector("h2 code") === window.originalTitleCode'))
            self.assertTrue(page.evaluate('document.querySelector("h2 a[href]") === window.originalTitleLink'))
            page.locator('h2 a[href]').click()
            self.assertTrue(page.evaluate('window.titleLinkClicked'))
            expect(page.locator('.main > ul a')).not_to_have_class(re.compile('reader-numbered-title'))
            expect(page.locator('.reader-chapter-grid a')).to_have_class(re.compile('reader-numbered-title'))
            before = page.locator('h2').inner_html()
            page.evaluate('window.__reasbookFormatReadingTitles()')
            self.assertEqual(page.locator('h2').inner_html(), before)
            browser.close()

    def test_item_paper_bookmarks_and_support_fragments_in_both_renderers(self):
        from playwright.sync_api import expect, sync_playwright

        scripts = sidebar_scripts()
        paper = {'slug': 'demo', 'title': 'Demo paper', 'home': 'papers/demo/',
            'reader_route': 'papers/demo/items/', 'sections': [], 'routes': ['demo/support/'],
            'items': [{'title': 'Theorem 2.1', 'anchor': 'theorem-2-1', 'section': '2'}],
            'item_sections': [{'number': '2', 'label': 'Section 2 — Results', 'anchor': 'paper-section-2'}],
            'files': [{'title': 'Support', 'route': 'demo/support/', 'module': 'Demo.Support'}]}
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                for prefix in ('/ReasBook/', '/proxy/3009/ReasBook/versions/v4.32.2/sites/demo/'):
                    page = browser.new_page()
                    errors = []
                    page.on('pageerror', lambda error: errors.append(str(error)))
                    selected = [scripts['sidebarItemStateScript']]
                    if not fallback:
                        selected.append(scripts['navLinkRewriteScript'])
                    selected.append(scripts['sidebarFallbackScript'])
                    init = f'window.__versoSiteRoot={json.dumps(prefix)};window.__reasbookSidebarData=' + json.dumps({'books': [], 'papers': [paper]}) + ';'
                    html = ('<html><head>' + ''.join('<script>' + script + '</script>' for script in [init, *selected])
                        + '</head><body><nav id="sidebar-nav-root"></nav><div class="main"><h1>Demo paper</h1>'
                        + '<div id="theorem-2-1"></div><div id="theorem-2-1-clause-2"></div></div></body></html>')
                    page.route('**/*', lambda route: route.fulfill(status=200, content_type='text/html', body=html))
                    base = 'https://preview.test' + prefix
                    for path in ('demo/support/#declaration', 'demo/support/index.html#declaration'):
                        page.goto(base + path, wait_until='networkidle')
                        support = page.get_by_role('link', name='Support', exact=True)
                        expect(support).to_have_attribute('aria-current', 'page')
                        expect(page.locator('.nav-supporting-files')).to_have_attribute('open', '')
                        page.evaluate('window.location.hash = "second-declaration"')
                        expect(support).to_have_attribute('aria-current', 'page')
                    page.goto(base + 'previous/', wait_until='networkidle')
                    page.goto(base + 'papers/demo/#theorem-2-1-clause-2', wait_until='networkidle')
                    page.wait_for_url(base + 'papers/demo/items/#theorem-2-1-clause-2')
                    expect(page.get_by_role('link', name='Theorem 2.1', exact=True)).to_have_attribute('aria-current', 'location')
                    page.go_back(wait_until='networkidle')
                    self.assertEqual(page.url, base + 'previous/')
                    for fragment in ('unknown-item', '%zz'):
                        page.goto(base + 'papers/demo/#' + fragment, wait_until='networkidle')
                        self.assertEqual(page.url, base + 'papers/demo/#' + fragment)
                    self.assertEqual(errors, [])
                    page.close()
            browser.close()

    def test_named_chapter_links_and_contents_buttons_have_separate_actions(self):
        from playwright.sync_api import expect, sync_playwright

        scripts = sidebar_scripts()
        css = (ROOT / 'ReasBookWeb/static_files/style.css').read_text()
        title = 'Chapter 01 — The Fundamental Group and Some of Its Applications'
        route = 'books/demo/chapters/chap01/'
        data = {'books': [{'slug': 'demo', 'title': 'Demo', 'home': 'books/demo/',
            'chapters': [{'title': title, 'route': route, 'sections': [],
                'items': [{'title': 'Definition 1.2.1', 'module': 'Demo.Definition_1_2_1',
                           'section': 2, 'anchor': 'definition-1-2-1'}],
                'item_sections': [{'number': 2, 'label': '1.2 — The Fundamental Group', 'anchor': 'section-1-2'}]}]}],
            'papers': []}
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            for fallback in (False, True):
                for prefix in ('/ReasBook/', '/proxy/3008/ReasBook/versions/v4.30.0/sites/demo/'):
                    page = browser.new_page(viewport={'width': 1440, 'height': 1000})
                    selected = [scripts['sidebarItemStateScript']]
                    if not fallback:
                        selected.append(scripts['navLinkRewriteScript'])
                    selected.append(scripts['sidebarFallbackScript'])
                    init = f'window.__versoSiteRoot={json.dumps(prefix)};window.__reasbookSidebarData={json.dumps(data)};'
                    html = (f'<html><head><base href="{prefix}"><style>{css}</style>'
                        + ''.join(f'<script>{script}</script>' for script in [init, *selected])
                        + '</head><body><header><nav id="sidebar-nav-root"></nav></header>'
                        + '<div class="main"><h1>Demo</h1><div class="reader-home-links"></div>'
                        + '<h2 id="section-1-2">The Fundamental Group</h2>'
                        + '<div data-reasbook-statement id="definition-1-2-1">Definition</div></div></body></html>')
                    page.route('**/*', lambda request: request.fulfill(status=200, content_type='text/html', body=html))
                    home = 'https://preview.test' + prefix + 'books/demo/'
                    chapter = 'https://preview.test' + prefix + route
                    page.goto(home)
                    nav = page.locator('#sidebar-nav-root')
                    link = nav.get_by_role('link', name=title, exact=True)
                    toggle = nav.get_by_role('button', name='Toggle contents for ' + title, exact=True)
                    expect(toggle).to_have_attribute('aria-expanded', 'false')
                    expect(link).to_have_attribute('href', prefix + route)
                    self.assertEqual(nav.get_by_role('link', name='Overview', exact=True).count(), 0)
                    link.focus()
                    page.keyboard.press('Tab')
                    expect(toggle).to_be_focused()
                    page.keyboard.press('Space')
                    expect(toggle).to_have_attribute('aria-expanded', 'true')
                    self.assertEqual(page.url, home)
                    page.keyboard.press('Space')
                    expect(toggle).to_have_attribute('aria-expanded', 'false')
                    link.click()
                    page.wait_for_url(chapter)
                    expect(link).to_have_attribute('aria-current', 'page')
                    section = nav.get_by_role('link', name='1.2 — The Fundamental Group', exact=True)
                    section.click()
                    page.wait_for_url(chapter + '#section-1-2')
                    expect(section).to_have_attribute('aria-current', 'location')
                    self.assertEqual(nav.locator('.nav-file-item').count(), 1)
                    for width in (320, 768, 1024, 1440):
                        page.set_viewport_size({'width': width, 'height': 1000})
                        if width <= 1000:
                            page.locator('#reader-nav-toggle').click()
                        expect(link).to_be_visible()
                        self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
                        if width <= 1000:
                            self.assertGreaterEqual(toggle.bounding_box()['height'], 44)
                            self.assertGreaterEqual(toggle.bounding_box()['width'], 44)
                            page.keyboard.press('Escape')
                    page.close()
            browser.close()

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
                        expect(nav.locator(".nav-chapter-title").first).to_have_text(chapter_title)
                        # Every navigation level must keep the same sans family.
                        for selector in (".nav-work-title", ".nav-chapter-title",
                                         ".nav-chapter a[data-chapter-target]", ".nav-file-item > a"):
                            family = nav.locator(selector).first.evaluate("n => getComputedStyle(n).fontFamily")
                            self.assertIn("sans-serif", family)
                            self.assertNotIn("Georgia", family)
                        self.assertEqual(nav.locator("a.is-current").inner_text(), "Lemma 1.70")
                        self.assertEqual(nav.locator("a[aria-current=location]").count(), 1)
                        self.assertIn('Empty <item> "quoted"', nav.locator("[aria-disabled]").inner_text())
                        self.assertEqual(nav.locator(".nav-chapter.is-open").count(), 1)
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
                        nav.get_by_role("link", name=chapter_title, exact=True).click()
                        page.wait_for_url(base)
                        expect(nav.locator("a.is-current")).to_have_text(chapter_title)
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
