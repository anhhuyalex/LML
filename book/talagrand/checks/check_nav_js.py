"""Runs the Node checks of the Contents pane script (``check_nav.cjs``) inside the unittest run."""
import re
import shutil
import subprocess
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("check_nav.cjs")


@unittest.skipUnless(shutil.which("node"), "node is not installed (GitHub's runners have it)")
class NavScriptChecks(unittest.TestCase):
    def test_pure_functions_of_book_nav_js(self):
        done = subprocess.run(["node", str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)


class TemplateChecks(unittest.TestCase):
    """book.html must offer every element that book-nav.js looks up by id."""

    def test_template_has_the_elements_the_script_uses(self):
        template_dir = SCRIPT.parents[2] / "typstverso" / "templates" / "html"
        template = (template_dir / "book.html").read_text(encoding="utf-8")
        script = (template_dir / "book-nav.js").read_text(encoding="utf-8")
        wanted = set(re.findall(r'getElementById\("([^"]+)"\)', script))
        self.assertTrue(wanted, "no getElementById calls found; has the script changed shape?")
        # reader.js and tooltips.js are inlined into the page at build time, so ids that only they
        # create are not in the template text.
        missing = {name for name in wanted if f'id="{name}"' not in template}
        self.assertEqual(missing, set())
        self.assertIn('href="book-nav.css"', template)
        self.assertIn('src="book-nav.js"', template)


if __name__ == "__main__":
    unittest.main()
