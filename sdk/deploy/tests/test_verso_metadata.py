from html.parser import HTMLParser
from pathlib import Path
import tempfile
import unittest

from reasbook_deploy_sdk.release.static_assets import compact_verso_metadata


class Probe(HTMLParser):
    def __init__(self):
        super().__init__()
        self.text = []
        self.bindings = []
        self.links = []

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        if tag == 'span' and ('data-binding' in attributes or 'data-b' in attributes):
            self.bindings.append(attributes.get('data-b', attributes.get('data-binding')))
        for key in ['href', 'src']:
            if key in attributes:
                self.links.append(attributes[key])

    def handle_data(self, data):
        self.text.append(data)


class VersoMetadataTests(unittest.TestCase):
    def test_compaction_preserves_source_and_binding_equivalence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            page = root/'index.html'
            source = '''<script>window.__versoSiteRoot="/ReasBook/";</script>
<code class="hl lean block" data-lean-context="name"><span class="const token" data-binding="const-Matrix.VeryLongTheorem" data-verso-hover="123">∀ x, f x = x</span>
<span class="const token" data-binding="const-Matrix.VeryLongTheorem">f</span>
<span class="var token" data-binding="var-AnotherVeryLongBinding">x</span>
<span class="token" data-binding="b0">y</span><span class="token" data-binding="">(</span></code>
<a href="/ReasBook/source/#L12">source</a>'''
            page.write_text(source)
            before = Probe()
            before.feed(source)
            report = compact_verso_metadata(root, '/ReasBook/')
            result = page.read_text()
            after = Probe()
            after.feed(result)
            self.assertEqual(before.text, after.text)
            self.assertEqual(before.links, after.links)
            for i in range(len(before.bindings)):
                for j in range(len(before.bindings)):
                    self.assertEqual(before.bindings[i] == before.bindings[j],
                                     after.bindings[i] == after.bindings[j])
            self.assertEqual(after.bindings[-1], '')
            self.assertGreater(report['saved_bytes'], 0)
            compact_verso_metadata(root, '/ReasBook/')
            self.assertEqual(page.read_text(), result)

    def test_compaction_keeps_api_pages_and_original_assets(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            assets = root/'static/shared-verso'
            assets.mkdir(parents=True)
            script = assets/'original.js'
            script.write_text('document.querySelectorAll("[data-binding]"); c.dataset.binding;')
            page = root/'index.html'
            page.write_text('<script>window.__versoSiteRoot="/ReasBook/";</script>'
                            '<script src="/ReasBook/static/shared-verso/original.js"></script>'
                            '<span data-binding="const-AnActualLongConstant">x</span>')
            docs = root/'versions/v4.32.0/docs/ReasBook'
            docs.mkdir(parents=True)
            api = docs/'Theorem.html'
            api.write_text(page.read_text())
            original_api = api.read_bytes()
            original_script = script.read_bytes()
            compact_verso_metadata(root, '/ReasBook/')
            self.assertEqual(api.read_bytes(), original_api)
            self.assertEqual(script.read_bytes(), original_script)
            self.assertNotIn('src="/ReasBook/static/shared-verso/original.js"', page.read_text())
            copies = [p for p in assets.glob('*.js') if p != script]
            self.assertEqual(len(copies), 1)
            self.assertIn('dataset.b', copies[0].read_text())
            self.assertNotIn('dataset.binding', copies[0].read_text())


class NativeWhitespaceTests(unittest.TestCase):
    def test_compaction_preserves_text_hovers_and_api_bytes(self):
        from reasbook_deploy_sdk.release.static_assets import compact_verso_intertext
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            code = ('<code class="hl lean block"><span class="var token" data-binding="v" data-verso-hover="2">x</span>'
                    '<span class="inter-text"> &lt;\n </span><span class=inter-text> </span>'
                    '<span class="inter-text" data-verso-hover="3">keep</span></code>')
            source = '<script>window.__versoSiteRoot="/ReasBook/";</script><p>Prose</p>'+code
            (root/'a.html').write_text(source)
            (root/'docs').mkdir()
            (root/'docs/Item.html').write_text(source)
            before=Probe()
            before.feed(source)
            result=compact_verso_intertext(root)
            after=Probe()
            after.feed((root/'a.html').read_text())
            self.assertEqual(''.join(before.text), ''.join(after.text))
            self.assertEqual(before.bindings, after.bindings)
            self.assertIn('data-verso-hover="2"', (root/'a.html').read_text())
            self.assertIn('data-verso-hover="3"', (root/'a.html').read_text())
            self.assertEqual((root/'docs/Item.html').read_text(), source)
            self.assertEqual(result['wrappers'], 2)
            self.assertEqual(compact_verso_intertext(root)['wrappers'], 0)

    def test_inert_text_non_native_code_and_diagnostics_are_retained(self):
        from reasbook_deploy_sdk.release.static_assets import compact_verso_intertext
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            inner='<span class="inter-text"> </span>'
            examples=[
                '<div class="has-info"><code class="hl lean block">'+inner+'</code></div>',
                '<code class="hl lean block"><span class="has-info">'+inner+'</span></code>',
                '<code>'+inner+'</code>',
                '<code data-note=\'class="hl lean block"\'>'+inner+'</code>',
                '<template><code class="hl lean block">'+inner+'</code></template>',
                '<template><script>noop()</script><code class="hl lean block">'+inner+'</code></template>',
                '<template><template></template><code class="hl lean block">'+inner+'</code></template>',
                '<div class = "has-info"><code class="hl lean block">'+inner+'</code></div>',
                """<script>let x='</style><code class="hl lean block">"""+inner+"""</code>';</script>""",
                '<code data-class="hl lean block">'+inner+'</code>',
                '<!-- <code class="hl lean block">'+inner+'</code> -->',
                '<script>const text=\'<code class="hl lean block">'+inner+'</code>\';</script>',
            ]
            for i,text in enumerate(examples):
                (root/f'{i}.html').write_text('<script>window.__versoSiteRoot="/ReasBook/";</script>'+text)
            originals={p:p.read_bytes() for p in root.glob('*.html')}
            self.assertEqual(compact_verso_intertext(root)['pages'],0)
            for p,data in originals.items():
                self.assertEqual(p.read_bytes(),data)


if __name__ == '__main__':
    unittest.main()
