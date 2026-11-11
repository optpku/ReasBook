from pathlib import Path
import json
import shutil
import tempfile
from types import SimpleNamespace
import unittest

from reasbook_deploy_sdk.release.artifacts import PagesSiteProjector
from reasbook_deploy_sdk.release.static_assets import (
    deduplicate_theorem_map_runtime,
    relativize_native_documentation_links,
    resolve_native_documentation_links,
)


class GraphAliasTests(unittest.TestCase):
    def test_only_identical_graphs_redirect_and_keep_nested_entries(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            full, site = root / 'full', root / 'site'
            project = SimpleNamespace(kind='papers', slug='demo', branch='v4.32.0',
                                      key='papers/Demo', project_id='Demo')
            spec = SimpleNamespace(base_path='/ReasBook/', canonical_projects=lambda: [project])
            source = full / 'theorem-maps/papers/demo'
            target = site / 'versions/v4.32.0/theorem-maps/papers/demo'
            (source / 'v21').mkdir(parents=True)
            for relative, text in [('index.html', '<title>ReasBook Theorem Map</title>'),
                                   ('data.json', '{"items":["original"]}'),
                                   ('v21/index.html', '<title>Second graph</title>'),
                                   ('v21/data.json', '{"items":["second"]}'),
                                   ('metadata.json', json.dumps({'project': {
                                       'id': 'Demo', 'kind': 'papers', 'branch': 'v4.32.0',
                                       'title': 'A mathematical title', 'commit': 'verified'}}))]:
                (source / relative).write_text(text)
            shutil.copytree(source, target)
            report = PagesSiteProjector()._write_theorem_map_aliases(spec, full, site)
            self.assertEqual(report['redirects'], 2)
            alias = site / 'theorem-maps/papers/demo'
            self.assertFalse((alias / 'data.json').exists())
            self.assertIn('location.search+location.hash', (alias / 'v21/index.html').read_text())
            self.assertIn('/versions/v4.32.0/theorem-maps/papers/demo/v21/index.html',
                          (alias / 'v21/index.html').read_text())
            self.assertEqual((source / 'data.json').read_bytes(), (target / 'data.json').read_bytes())
            self.assertIn('/versions/v4.32.0/theorem-maps/papers/demo/index.html',
                          (site / 'theorem-maps/index.html').read_text())
            self.assertIn('A mathematical title', (site / 'theorem-maps/index.html').read_text())
            shutil.rmtree(alias)
            (source / 'data.json').write_text('{"items":["different"]}')
            report = PagesSiteProjector()._write_theorem_map_aliases(spec, full, site)
            self.assertEqual(report['redirects'], 0)
            self.assertEqual((alias / 'data.json').read_bytes(), (source / 'data.json').read_bytes())


class NativeDocumentationLinkTests(unittest.TestCase):
    def test_native_constants_use_actual_local_declarations_or_upstream_finder(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            prefix = '/ReasBook/versions/v4.30.0/'
            docs = root / 'versions/v4.30.0/docs/ReasBook'
            (docs / 'declarations').mkdir(parents=True)
            (docs / 'declarations/declaration-data.bmp').write_text(json.dumps({'declarations': {
                'Demo.main': {'docLink': './Demo.html#Demo.main'},
                "Demo.main'": {'docLink': './Demo.html#Demo.main%27'},
            }}))
            (docs / 'Demo.html').write_text('<div id="Demo.main">Actual declaration</div><div id="Demo.main\x27">A primed declaration</div>')
            page = root / 'versions/v4.30.0/books/demo/index.html'
            page.parent.mkdir(parents=True)
            links = ''.join('<a title="Documentation" href="' + prefix +
                            'docs/ReasBook/find?pattern=' + name + '#doc">' + text + '</a>'
                            for name, text in [('Demo.main', 'main'), ('Demo.main%27', 'main prime'), ('Fin', 'Fin'), ('Nat', 'ℕ')])
            raw = '<script>const keep = ' + json.dumps(links) + ';</script>'
            page.write_text('<head><base href="' + prefix + '"><script>window.__versoSiteRoot="/ReasBook/";</script></head>' + links + raw)
            report = resolve_native_documentation_links(root, '/ReasBook/')
            self.assertEqual(report, {'pages': 1, 'local': 2, 'upstream': 2})
            rendered = page.read_text()
            self.assertIn('href="' + prefix + 'docs/ReasBook/Demo.html#Demo.main"', rendered)
            self.assertIn('href="' + prefix + 'docs/ReasBook/Demo.html#Demo.main%27"', rendered)
            for name in ['Fin', 'Nat']:
                self.assertIn('href="https://leanprover-community.github.io/mathlib4_docs/find/?pattern=' + name + '#doc"', rendered)
            self.assertIn('Upstream documentation (current version): Nat', rendered)
            self.assertIn('>ℕ</a>', rendered)
            self.assertIn(raw, rendered)
            self.assertEqual(resolve_native_documentation_links(root, '/ReasBook/')['pages'], 0)

    def test_complete_urls_stay_equal_and_only_native_declaration_links_change(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            page = root / 'versions/v4.30.0/books/demo/index.html'
            page.parent.mkdir(parents=True)
            prefix = '/ReasBook/versions/v4.30.0/'
            link = '<a href="' + prefix + 'docs/ReasBook/find?pattern=Nat&amp;x=y#doc" title="Documentation">Nat</a>'
            source = ('<head><base href="' + prefix + '"><base href="https://ignored.invalid/">'
                      '<script>window.__versoSiteRoot="/ReasBook/";</script></head>'
                      + link + '<code class="hl lean block">' + link + '</code>'
                      + '<script>const fake=\'' + link + '\';</script>')
            page.write_text(source)
            docs = root / 'docs/Item.html'
            docs.parent.mkdir()
            docs.write_text(source)
            report = relativize_native_documentation_links(root, '/ReasBook/')
            self.assertEqual(report['links'], 1)
            self.assertIn('href="docs/ReasBook/find?pattern=Nat&amp;x=y#doc"', page.read_text())
            self.assertEqual(page.read_text().count(link), 2)
            self.assertEqual(docs.read_text(), source)
            self.assertEqual(relativize_native_documentation_links(root, '/ReasBook/')['links'], 0)

    def test_forged_attributes_external_base_and_inert_code_remain_unchanged(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            link = '<a href="/ReasBook/versions/v4.30.0/docs/X.html" title="Documentation">X</a>'
            cases = [
                '<code data-class="hl lean block">' + link + '</code>',
                '<template><code class="hl lean block">' + link + '</code></template>',
                '<code class="hl lean block"><a data-note=\'title="Documentation"\' '
                'href="/ReasBook/versions/v4.30.0/docs/X.html" title="Source">X</a></code>',
                '<code class="hl lean block"><a data-note=\'href="/ReasBook/versions/v4.30.0/docs/X.html"\' '
                'title="Documentation">X</a></code>',
            ]
            for i, body in enumerate(cases):
                page = root / f'{i}.html'
                source = ('<head><base href="/ReasBook/versions/v4.30.0/">'
                          '<script>window.__versoSiteRoot="/ReasBook/";</script></head>' + body)
                page.write_text(source)
            outside = root / 'external.html'
            outside.write_text('<head><base href="https://outside.invalid/">'
                               '<script>window.__versoSiteRoot="/ReasBook/";</script></head>'
                               '<code class="hl lean block">' + link + '</code>')
            before = {p: p.read_bytes() for p in root.glob('*.html')}
            self.assertEqual(relativize_native_documentation_links(root, '/ReasBook/')['links'], 0)
            self.assertEqual(before, {p: p.read_bytes() for p in root.glob('*.html')})


class GraphRuntimeTests(unittest.TestCase):
    def test_verified_runtime_shared_with_original_notices_and_unknown_apps_retained(self):
        assets = (Path(__file__).resolve().parents[2] / 'theorem_graph/src/theorem_graph_sdk/resources/assets')
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            folders = []
            for name in ('one', 'two', 'custom', 'crlf'):
                folder = root / 'versions/v4.30.0/theorem-maps/books' / name
                (folder / 'vendor').mkdir(parents=True)
                shutil.copyfile(assets / 'vendor/viz-global.js', folder / 'vendor/viz-global.js')
                shutil.copyfile(assets / 'app.js', folder / 'app.js')
                folders.append(folder)
            custom = folders[-2] / 'app.js'
            custom.write_text(custom.read_text() + '\n// Unknown customized loader\n')
            (folders[-1] / 'app.js').write_bytes((assets / 'app.js').read_bytes().replace(b'\n', b'\r\n'))
            original = (assets / 'vendor/viz-global.js').read_bytes()
            report = deduplicate_theorem_map_runtime(root, '/ReasBook/')
            self.assertEqual(report['runtimes'], 2)
            shared = list((root / 'static/shared-theorem-maps').glob('*.js'))
            self.assertEqual(len(shared), 1)
            self.assertEqual(shared[0].read_bytes(), original)
            for folder in folders[:2]:
                self.assertFalse((folder / 'vendor/viz-global.js').exists())
                self.assertIn('/ReasBook/static/shared-theorem-maps/', (folder / 'app.js').read_text())
            for folder in folders[2:]:
                self.assertEqual((folder / 'vendor/viz-global.js').read_bytes(), original)
            self.assertEqual(deduplicate_theorem_map_runtime(root, '/ReasBook/')['runtimes'], 0)
