from pathlib import Path
import tempfile
import unittest

from reasbook_deploy_sdk.release.static_assets import deduplicate_verso_assets


class StaticAssetTests(unittest.TestCase):
    def test_shared_head_preserves_order_body_and_docs(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            script = 'window.shared = "' + 'x' * 500 + '";'
            css = 'p {color: red;}\n' * 40
            body = '<body><pre>theorem x : True := by trivial</pre><script>body()</script></body>'
            source = ('<html><head><script>window.__versoSiteRoot="/ReasBook/";</script>'
                      f'<style>{css}</style><script>{script}</script></head>' + body + '</html>')
            for name in ('a.html', 'b.html', 'docs/index.html'):
                p = root / name
                p.parent.mkdir(exist_ok=True)
                p.write_text(source)
            report = deduplicate_verso_assets(root, '/ReasBook/')
            self.assertEqual(report['assets'], 2)
            self.assertEqual(report['replaced_blocks'], 4)
            self.assertGreater(report['saved_bytes'], 0)
            changed = (root / 'a.html').read_text()
            self.assertIn(body, changed)
            self.assertLess(changed.index('<link '), changed.index('<script src='))
            self.assertNotIn('async', changed)
            self.assertEqual((root / 'docs/index.html').read_text(), source)
            self.assertEqual(deduplicate_verso_assets(root, '/ReasBook/')['replaced_blocks'], 0)

    def test_context_sensitive_and_inert_blocks_unchanged(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            filler = ' ' * 300
            head = ('<script>window.__versoSiteRoot="/ReasBook/";</script>'
                    f'<script>{filler}document.currentScript.src</script>'
                    f'<style>{filler}a {{background:url(../image.png)}}</style>'
                    f'<script type="module">{filler}import("./module.js")</script>'
                    f'<!--<script>{filler}evil()</script>-->'
                    f'<template><script>{filler}inert()</script></template>'
                    f'<noscript><style>{filler}p {{color:red}}</style></noscript>')
            source = '<html><head>' + head + '</head><body>Content</body></html>'
            for name in ('a.html','b.html'):
                (root/name).write_text(source)
            report = deduplicate_verso_assets(root, '/ReasBook/')
            self.assertEqual(report['replaced_blocks'], 0)
            self.assertEqual((root/'a.html').read_text(), source)

    def test_csp_documents_are_not_rewritten(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = ('<html><head><meta http-equiv="Content-Security-Policy" content="script-src none">'
                      '<script>window.__versoSiteRoot="/ReasBook/";' + ' ' * 300 + '</script></head></html>')
            for name in ('a.html', 'b.html'):
                (root/name).write_text(source)
            self.assertEqual(deduplicate_verso_assets(root, '/ReasBook/')['assets'], 0)
            self.assertEqual((root/'a.html').read_text(), source)

    def test_non_verso_html_not_rewritten(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = '<html><head><style>' + 'p {color:red}\n' * 100 + '</style></head></html>'
            for name in ('a.html','b.html'):
                (root/name).write_text(source)
            self.assertEqual(deduplicate_verso_assets(root, '/ReasBook/')['assets'], 0)




class LargeStaticAssetTests(unittest.TestCase):
    def test_large_native_navigation_is_shared_without_touching_body(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            script = 'window.largeNavigation="' + 'n' * (1400 * 1024) + '";'
            body = '<body><code class="hl lean block"><span data-verso-hover="7">∀ x, x = x</span></code></body>'
            source = ('<html><head><script>window.__versoSiteRoot="/ReasBook/";</script>'
                      + '<script>' + script + '</script></head>' + body + '</html>')
            for name in ('a.html', 'b.html'):
                (root/name).write_text(source)
            report = deduplicate_verso_assets(root, '/ReasBook/')
            self.assertEqual(report['assets'], 1)
            self.assertEqual(report['replaced_blocks'], 2)
            self.assertGreater(report['saved_bytes'], 1300 * 1024)
            self.assertTrue((root/'a.html').read_text().endswith(body + '</html>'))

    def test_javascript_url_constructor_is_safe_but_relative_css_is_retained(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            script = ' ' * 300 + 'window.testURL = new URL("./thing", location.href);'
            css = ' ' * 300 + '.image {background: url(./image.png)}'
            source = ('<head><script>window.__versoSiteRoot="/ReasBook/";</script>'
                      f'<script>{script}</script><style>{css}</style></head><body>Math</body>')
            for name in ('a.html', 'b.html'):
                (root/name).write_text(source)
            result = deduplicate_verso_assets(root, '/ReasBook/')
            self.assertEqual(result['assets'], 1)
            self.assertIn(f'<style>{css}</style>', (root/'a.html').read_text())


if __name__ == '__main__':
    unittest.main()
