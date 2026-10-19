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
