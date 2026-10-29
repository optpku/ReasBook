"""Opt-in real Lean → SubVerso → reader → Chromium hover acceptance.

Set REASBOOK_HOVER_LEAN to a Lean executable and REASBOOK_HOVER_WEB_CACHE to
the matching built Web cache (containing packages/verso, subverso, MD4Lean,
illuminate, plausible). No dependency downloads or shared-cache writes occur.
REASBOOK_HOVER_EXTRACTOR selects the matching version branch's LiterateExtract.lean.
REASBOOK_HOVER_OUTPUT optionally preserves the canary in a new private directory.
REASBOOK_HOVER_REAL_SOURCE optionally checks archived BFGS source/JSON with the
matching v4.32.2 toolchain, without altering or rebuilding that source tree.
"""

from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from threading import Thread
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'ReasBookWeb/scripts'))
import gen_sections as generator  # noqa: E402
import reader_attributions  # noqa: E402
from reasbook_sdk_common.attribution import project_credit  # noqa: E402
from reasbook_sdk_common.catalog import catalog_page  # noqa: E402

NATIVE = os.environ.get('REASBOOK_HOVER_LEAN') and os.environ.get('REASBOOK_HOVER_WEB_CACHE')
SOURCE = '''/- Authors: Zichen Wang, Wanli Ma -/
import Lean
open Lean Elab Command
open Lean.Parser.Command
-- Reproduce old Mathlib's missing recall-head info without depending on Mathlib.
syntax (name := Mathlib.Tactic.Recall.recall) (docComment)? "recall " ident ppIndent(optDeclSig) (declVal)? : command
elab_rules : command
  | `($[$_doc?:docComment]? recall $id:ident $sig:optDeclSig $[$_val?]?) => withoutModifyingEnv do
    let (_, some type) := expandOptDeclSig sig
      | throwError "The recall fixture requires an explicit type"
    let name ← resolveGlobalConstNoOverload id
    liftTermElabM do
      let expected ← Term.elabType type
      unless ← Meta.isDefEq expected (← getConstInfo name).type do
        throwError "Incorrect recall signature"
namespace HoverSmoke
local notation "ℕₕ" => Nat
#check (ℕₕ → ℕₕ)
variable (α : Type)
/-- Definition 1.0: retain the source spelling of an escaped identifier. -/
def «plain» : Nat := 1
#check «plain»
/-- Theorem 1.1: reflexivity. -/
theorem same (n : Nat) : n = n := by rfl
/-- Definition 1.2: a point with its law. -/
structure Point where
  x : Nat
  law : x = x
section
variable (p : Point)
-- A dotted parser identifier elaborates to a projection application, not a
-- bare global constant. Preserve the native receiver/projection metadata.
#check p.x
end
/-- Definition 1.3: a constructor. -/
inductive Choice where
  | left : Choice
  | right : Choice
#check Nat.add_comm
section
variable (ε : Nat)
#check ε
/-- Theorem 1.4: Unicode local variables. -/
theorem unicode : ε = ε := by rfl
end
namespace RecallScope
def witness : Nat := 1
section
variable (witness : Type)
#check witness
end
recall witness : Nat
end RecallScope
end HoverSmoke
#check HoverSmoke.RecallScope.witness
recall HoverSmoke.RecallScope.witness : Nat
'''


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *_):
        pass


@unittest.skipUnless(NATIVE, 'Set REASBOOK_HOVER_LEAN and REASBOOK_HOVER_WEB_CACHE for native hover acceptance')
class NativeStatementHoverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if output := os.environ.get('REASBOOK_HOVER_OUTPUT'):
            cls.root = Path(output)
            cls.root.mkdir(parents=True, exist_ok=False)
        else:
            temporary = tempfile.TemporaryDirectory(prefix='reasbook-hover-')
            cls.addClassCleanup(temporary.cleanup)
            cls.root = Path(temporary.name)
        cls.web = cls.root / 'ReasBookWeb'
        cls.source = cls.root / 'ReasBook'
        (cls.web / 'ReasBookSite').mkdir(parents=True)
        (cls.source / 'Books').mkdir(parents=True)
        cls.source_file = cls.source / 'Books/HoverSmoke.lean'
        cls.source_file.write_text(SOURCE)
        cls.json_file = cls.source / '.lake/build/literate/HoverSmoke.json'
        cls.json_file.parent.mkdir(parents=True)
        cache = Path(os.environ['REASBOOK_HOVER_WEB_CACHE'])
        shutil.copy2(cache / 'packages/verso/lean-toolchain', cls.web / 'lean-toolchain')
        dependencies = [cache / 'packages' / package / '.lake/build/lib/lean'
                        for package in ('verso', 'subverso', 'MD4Lean', 'illuminate', 'plausible')]
        cls.dynlibs = sorted((cache / 'packages/MD4Lean/.lake/build/lib').glob('*.so'))
        cls.lean = os.environ['REASBOOK_HOVER_LEAN']
        cls.env = {**os.environ, 'LEAN_NUM_THREADS': '2',
                   'PATH': str(Path(cls.lean).parent) + os.pathsep + os.environ.get('PATH', ''),
                   'LEAN_PATH': os.pathsep.join(map(str, [cls.web, cls.source / 'Books', *dependencies])),
                   'LEAN_SRC_PATH': str(cls.source / 'Books')}
        original_extractor = os.environ.get('REASBOOK_HOVER_EXTRACTOR', str(ROOT / 'ReasBook/LiterateExtract.lean'))
        extractor = cls.source / 'LiterateExtract.lean'
        shutil.copy2(original_extractor, extractor)
        generator.write_recall_support(cls.source)
        cls.command([str(extractor), 'HoverSmoke', str(cls.json_file)],
                    run=True, label='extract')
        (cls.web / '.literate-sources.json').write_text(json.dumps({'HoverSmoke': 'Books/HoverSmoke.lean'}))
        shutil.copy2(ROOT / 'ReasBookWeb/scripts/statement_code.lean',
                     cls.web / 'ReasBookSite/StatementCode.lean')
        cls.command(['-o', 'ReasBookSite/StatementCode.olean', 'ReasBookSite/StatementCode.lean'], label='runtime')
        lines = ['import ReasBookSite.StatementCode', 'open Verso Genre Blog',
                 generator.STATEMENT_PAGE_OPTIONS,
                 '#doc (Page) "Hover acceptance" =>', '']
        # Use the production selector/rendering path, including exact source ranges.
        lines += generator.statement_blocks(SOURCE, 'Statements', '[Documentation](#)', 'checked',
                                             limit=None, module='HoverSmoke', source_path='Books/HoverSmoke.lean')
        if archived := os.environ.get('REASBOOK_HOVER_REAL_SOURCE'):
            mapping = {'HoverSmoke': 'Books/HoverSmoke.lean'}
            for name in ('Notation_3_1', 'Theorem_1_1'):
                module = f'Book.{name}'
                source_path = f'Papers/BFGSMinimumQOrder_Liu_2026/Book/{name}.lean'
                destination = cls.source / source_path
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(Path(archived) / source_path, destination)
                json_path = f'.lake/build/literate/Book/{name}.json'
                (cls.source / json_path).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(Path(archived) / json_path, cls.source / json_path)
                mapping[module] = source_path
                lines += generator.statement_blocks(destination.read_text(), name, '[Documentation](#)',
                                                     name.lower(), module=module, source_path=source_path)
            (cls.web / '.literate-sources.json').write_text(json.dumps(mapping))
        # Production includes the environment identity in page syntax so Lake
        # recompiles when imported sources change; exercise that JSON shape too.
        for index, line in enumerate(lines):
            if ' reasbookStatement ' in line:
                fence, value = line.split(' reasbookStatement ', 1)
                record = json.loads(json.loads(value))
                record['environment_sha256'] = generator.statement_environment_digest(cls.source)
                lines[index] = fence + ' reasbookStatement ' + generator.lean_string(json.dumps(record))
        cls.page_text = '\n'.join(lines)
        (cls.web / 'Page.lean').write_text(cls.page_text)
        cls.command(['-o', 'Page.olean', 'Page.lean'], label='page')
        # Full literate pages omit ordinary author headers in their AST. Test
        # the post-render path separately from generated statement-card credit.
        full = ['import ReasBookSite.StatementCode', 'open Verso Genre Blog',
                '#doc (Page) "Full-page attribution acceptance" =>', '']
        full += generator.statement_blocks(SOURCE, 'Statement', '[Documentation](#)', 'full-checked',
                                           module='HoverSmoke', source_path='Books/HoverSmoke.lean')
        full_text = '\n'.join(full).replace('\n'.join(generator.source_attribution_blocks(SOURCE, 'Books/HoverSmoke.lean')), '')
        (cls.web / 'Full.lean').write_text(full_text)
        cls.command(['-o', 'Full.olean', 'Full.lean'], label='full')
        home = ['import VersoBlog', 'open Verso Genre Blog',
                '#doc (Page) "Integer Programming (Conforti et al., 2014)" =>', '',
                '# Chapters', '', ':::html div (class := "reader-chapter-grid")',
                '- [Chapter 01](/ReasBook/)', '- [Chapter 02](/ReasBook/)', ':::', '']
        home += generator.book_contributor_blocks('IntegerProgramming_Conforti_2014')
        (cls.web / 'Home.lean').write_text(generator.GENERATED_LEAN_HEADER + '\n'.join(home))
        cls.command(['-o', 'Home.olean', 'Home.lean'], label='home')
        sections = ('namespace ReasBookSite.Sections\ndef siteRoot := "/ReasBook/"\n'
                    'def docsRoot := "/ReasBook/docs/"\ndef staticRoot := "/ReasBook/static/style.css"\n'
                    'def sidebarDataJson := "{}"\nend ReasBookSite.Sections\n')
        (cls.web / 'ReasBookSite/Sections.lean').write_text(generator.GENERATED_LEAN_HEADER + sections)
        cls.command(['-o', 'ReasBookSite/Sections.olean', 'ReasBookSite/Sections.lean'], label='sections')
        shell = (ROOT / 'ReasBookWeb/ReasBookSite.lean').read_text()
        theme = 'open Output Html Template Theme\n' + shell.split('open Output Html Template Theme\n', 1)[1].split('/-- Generated section routes', 1)[0]
        main = '\n'.join(['import Page', 'import Home', 'import Full', 'import ReasBookSite.Sections',
                          'open Verso Genre Blog Site Syntax', theme,
                          'def hoverSite : Site := site Page /',
                          '  static "static" ← "./static_files"',
                          '  "book" Home',
                          '  "books/integerprogramming_conforti_2014/" Home',
                          '  "full" Full',
                          'def main := blogMain theme hoverSite', ''])
        (cls.web / 'Main.lean').write_text(generator.GENERATED_LEAN_HEADER + main)
        shutil.copytree(ROOT / 'ReasBookWeb/static_files', cls.web / 'static_files')
        generator.write_statement_styles(cls.web)
        cls.command(['Main.lean', '--output', str(cls.web / 'rendered/ReasBook')], run=True, label='render')
        manifest = cls.web / '.reader-attributions.json'
        manifest.write_text(json.dumps(dict(schema_version=1, pages={
            'full/': generator.source_attribution(SOURCE, 'ReasBook/Books/HoverSmoke.lean')})))
        reader_attributions.apply_attributions(cls.web / 'rendered/ReasBook', manifest)
        catalog = cls.web / 'rendered/ReasBook/catalog/index.html'
        catalog.parent.mkdir()
        catalog.write_text(catalog_page('ReasBook — Contributor layout samples', [
            ('Integer Programming — home layout sample', '../books/integerprogramming_conforti_2014/'),
        ]))

    @classmethod
    def command(cls, args, *, run=False, label='probe', success=True):
        libraries = [flag for path in cls.dynlibs for flag in ('--load-dynlib', str(path))]
        command = [cls.lean, '-j', '2', *libraries, *(['--run'] if run else []), *args]
        result = subprocess.run(command, cwd=cls.web, env=cls.env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        (cls.root / f'{label}.log').write_text(result.stdout)
        if success and result.returncode:
            raise AssertionError(f'{label} failed:\n{result.stdout}')
        return result

    def test_native_hover_is_visible_with_real_types(self):
        from playwright.sync_api import sync_playwright

        server = ThreadingHTTPServer(('127.0.0.1', 0),
                                     partial(QuietHandler, directory=str(self.web / 'rendered')))
        thread = Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        origin = f'http://127.0.0.1:{server.server_port}'
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(headless=True, args=['--disable-gpu'])
            try:
                page = browser.new_page(viewport={'width': 1440, 'height': 1000})
                errors, failed = [], []
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.on('response', lambda response: failed.append(response.url) if response.status >= 400 else None)
                page.route('**/*', lambda route: route.continue_() if route.request.url.startswith(origin) else route.abort())
                page.goto(origin + '/ReasBook/', wait_until='networkidle')
                code = page.locator('#checked')
                native_block = code.locator('code.hl.lean.block').first
                self.assertEqual(native_block.get_attribute('tabindex'), '0')
                self.assertEqual(native_block.get_attribute('aria-label'), 'Lean code')
                native_block.focus()
                self.assertTrue(native_block.evaluate('node => node === document.activeElement'))
                self.assertIn('Lean authors: Zichen Wang, Wanli Ma', code.locator('.reader-attribution').inner_text())
                self.assertNotIn('by rfl', code.inner_text())
                self.assertIn('law : x = x', code.inner_text())
                self.assertIn('| right : Choice', code.inner_text())
                # Actual semantic classes must have distinguishable colors, not
                # just a stylesheet with unused syntax-highlighter selectors.
                colors = [code.locator('.hl.lean ' + selector).first.evaluate(
                    'node => getComputedStyle(node).color')
                    for selector in ('.keyword', '.const', '.var')]
                self.assertEqual(len(set(colors)), 3, colors)
                for name, expected in [('n', 'Nat'), ('ε', 'Nat'), ('Nat.add_comm', 'Nat'),
                                       ('«plain»', 'Nat'), ('p', 'Point'), ('ℕₕ', 'Type')]:
                    token = code.locator('[data-verso-hover]').filter(has_text=re.compile('^' + re.escape(name) + '$')).last
                    self.assertGreater(token.count(), 0, name)
                    self.assertEqual(token.evaluate('node => getComputedStyle(node).cursor'), 'help')
                    token.hover()
                    popup = page.locator('.tippy-box[data-state="visible"]').last
                    popup.wait_for(state='visible')
                    self.assertIn(expected, popup.inner_text())
                    page.mouse.move(1400, 20)
                    # Older Verso/Tippy releases unmount on the hide animation's
                    # completion. Do not resize while that desktop popup remains.
                    page.wait_for_function("!document.querySelector('[data-tippy-root]')")
                page.screenshot(path=str(self.root / 'hover-desktop.png'))
                scoped = code.locator('code.hl.lean.block').filter(has_text='#check witness')
                self.assertEqual(scoped.locator('.var[data-verso-hover]').filter(
                    has_text=re.compile('^witness$')).count(), 1)
                # Lean's bare #check intentionally prefers a global constant:
                # the binder above remains a variable, the checked name does not.
                self.assertEqual(scoped.locator('.const').filter(has_text=re.compile('^witness$')).count(), 1)
                local_check = code.locator('code.hl.lean.block').filter(has_text='#check ε')
                self.assertGreater(local_check.locator('.var[data-verso-hover]').filter(
                    has_text=re.compile('^ε$')).count(), 0)
                self.assertEqual(local_check.locator('.const').filter(has_text=re.compile('^ε$')).count(), 0)
                # Both an open scope and a final command at EOF must use the
                # original parser range, before SubVerso extends trailing info.
                for spelling in ('witness', 'HoverSmoke.RecallScope.witness'):
                    recalled = code.locator('code.hl.lean.block').filter(has_text='recall ' + spelling)
                    token = recalled.locator('[data-verso-hover]').filter(
                        has_text=re.compile('^' + re.escape(spelling) + '$'))
                    self.assertEqual(token.count(), 1, 'The recalled name itself needs real type metadata')
                    token.hover()
                    popup = page.locator('.tippy-box[data-state="visible"]').last
                    popup.wait_for(state='visible')
                    self.assertIn('HoverSmoke.RecallScope.witness', popup.inner_text())
                    self.assertIn('Nat', popup.inner_text())
                    page.mouse.move(1400, 20)
                    page.wait_for_function("!document.querySelector('[data-tippy-root]')")
                page.set_viewport_size({'width': 390, 'height': 844})
                self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
                page.screenshot(path=str(self.root / 'hover-mobile.png'))
                self.assertEqual(errors, [])
                self.assertEqual(failed, [])
                if os.environ.get('REASBOOK_HOVER_REAL_SOURCE'):
                    page.set_viewport_size({'width': 1440, 'height': 1000})
                    for anchor, name, expected in [
                        ('notation_3_1', 'g', 'EuclideanSpace'),
                        ('theorem_1_1', 'BFGS.exists_orderOneExample', 'IsOrderOneExample'),
                    ]:
                        credit = page.locator(f'#{anchor} .reader-attribution').inner_text()
                        self.assertIn('Chenyi Li', credit)
                        self.assertIn('project-level attribution', credit)
                        self.assertNotIn('Zichen Wang', credit)
                        token = page.locator(f'#{anchor} [data-verso-hover]').filter(
                            has_text=re.compile('^' + re.escape(name) + '$')).last
                        token.hover()
                        popup = page.locator('.tippy-box[data-state="visible"]').last
                        popup.wait_for(state='visible')
                        self.assertIn(expected, popup.inner_text())
                        page.mouse.move(1400, 20)
                        page.wait_for_function("!document.querySelector('[data-tippy-root]')")
                    page.screenshot(path=str(self.root / 'hover-real-bfgs.png'))
                page.goto(origin + '/ReasBook/book/', wait_until='networkidle')
                credits = page.locator('.reader-contributors')
                expected_names = project_credit('books/IntegerProgramming_Conforti_2014').names
                self.assertIn(', '.join(expected_names), credits.inner_text())
                self.assertNotIn('Conforti', credits.inner_text(), 'textbook authors are not code contributors')
                for width, height, name in [(1440, 1000, 'desktop'), (390, 844, 'mobile')]:
                    page.set_viewport_size({'width': width, 'height': height})
                    self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
                    self.assertTrue(credits.is_visible())
                    page.screenshot(path=str(self.root / f'contributors-{name}.png'), full_page=True)
                self.assertEqual(errors, [])
                self.assertEqual(failed, [])
                page.goto(origin + '/ReasBook/full/', wait_until='networkidle')
                self.assertEqual(page.locator('.reader-attribution').count(), 1)
                self.assertIn('Lean authors: Zichen Wang, Wanli Ma', page.locator('.reader-attribution').inner_text())
                token = page.locator('#full-checked [data-verso-hover]').filter(has_text=re.compile('^n$')).last
                token.hover()
                popup = page.locator('.tippy-box[data-state="visible"]').last
                popup.wait_for(state='visible')
                self.assertIn('Nat', popup.inner_text())
                page.screenshot(path=str(self.root / 'full-page-credit.png'))
                page.goto(origin + '/ReasBook/catalog/', wait_until='networkidle')
                self.assertIn(', '.join(expected_names), page.locator('.catalog-credit').inner_text())
                self.assertTrue(page.evaluate('document.documentElement.scrollWidth <= innerWidth'))
                page.screenshot(path=str(self.root / 'catalog-credit.png'), full_page=True)
                self.assertEqual(errors, [])
                self.assertEqual(failed, [])
            finally:
                browser.close()

    def test_stale_data_and_wrong_ranges_are_rejected(self):
        try:
            self.source_file.write_text(SOURCE + '\n-- modified since extraction\n')
            result = self.command(['Page.lean'], label='stale', success=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Stale statement semantic data', result.stdout)
        finally:
            self.source_file.write_text(SOURCE)
        try:
            (self.web / 'Page.lean').write_text(self.page_text.replace('theorem same', 'theorem wrong', 1))
            result = self.command(['Page.lean'], label='mismatch', success=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('does not match its checked source ranges', result.stdout)
        finally:
            (self.web / 'Page.lean').write_text(self.page_text)

    def test_large_chapter_can_compile_without_per_item_reader_pages(self):
        lines = [generator.GENERATED_LEAN_HEADER, 'import ReasBookSite.StatementCode',
                 'open Verso Genre Blog', generator.STATEMENT_PAGE_OPTIONS,
                 '#doc (Page) "Large chapter acceptance" =>', '']
        for index in range(410):
            lines += generator.statement_blocks(SOURCE, 'Theorem 1.1', '[Documentation](#)',
                                                 f'item-{index}', module='HoverSmoke',
                                                 source_path='Books/HoverSmoke.lean')
        (self.web / 'Large.lean').write_text('\n'.join(lines))
        self.command(['-o', 'Large.olean', 'Large.lean'], label='large-chapter')


if __name__ == '__main__':
    unittest.main()
