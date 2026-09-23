"""Checks for the project-owned reading routes and presentation adapter."""
import json
from pathlib import Path
import tempfile
import unittest

from build_verso import prepare_presentation


class ReadingResourceTests(unittest.TestCase):
    def test_all_reading_modules_exist_after_refactor(self):
        root = Path(__file__).resolve().parents[1]
        plan = json.loads((root / 'tools/verso_modules.json').read_text())
        self.assertEqual(len(plan['modules']), 8)
        self.assertEqual(len({row['slug'] for row in plan['modules']}), 8)
        self.assertEqual(plan['modules'][0]['module'], 'DFPWolfe.Main')
        for row in plan['modules']:
            self.assertTrue((root / Path(*row['module'].split('.')).with_suffix('.lean')).is_file())

    def test_landing_route_and_mobile_adapter_are_idempotent(self):
        with tempfile.TemporaryDirectory() as temporary:
            web = Path(temporary)
            (web / 'ReasBookSite').mkdir()
            (web / 'static_files').mkdir()
            (web / 'ReasBookSite/RouteTable.lean').write_text(
                'import Book\nmacro_rules\n      static "static" ← "./static_files"\n'
                'def reasbook_site :=\n  static "static" ← "./static_files"\n')
            (web / '.project-fragment.json').write_text(json.dumps({'routes': ['chapter/']}))
            (web / 'ReasBookSite.lean').write_text(
                '<meta charset="UTF-8"/>\n    if (u.origin !== window.location.origin) return href;')
            (web / 'static_files/style.css').write_text('body { color: black; }\n')
            prepare_presentation(web)
            first = {p.relative_to(web): p.read_text() for p in web.rglob('*') if p.is_file()}
            prepare_presentation(web)
            second = {p.relative_to(web): p.read_text() for p in web.rglob('*') if p.is_file()}
            self.assertEqual(first, second)
            routes = (web / 'ReasBookSite/RouteTable.lean').read_text()
            self.assertEqual(routes.count('"papers/dfp_wolfe_local/"'), 2)
            self.assertIn('chapter/', (web / '.project-fragment.json').read_text())


if __name__ == '__main__':
    unittest.main()
