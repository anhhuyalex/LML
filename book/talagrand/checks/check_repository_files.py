"""The checks' own inputs must not be hidden by `.gitignore` (it would pass locally, fail in CI)."""
import unittest

from sample_files import SAMPLES_DIR, git_ignore_rule


class SampleFilesAreTrackable(unittest.TestCase):
    def test_no_sample_file_is_git_ignored(self):
        samples = sorted(SAMPLES_DIR.rglob("*"))
        self.assertTrue(samples, f"no sample files found in {SAMPLES_DIR}")
        hidden = {str(path): git_ignore_rule(path) for path in samples + [SAMPLES_DIR]
                  if git_ignore_rule(path)}
        self.assertEqual(hidden, {}, "these test inputs would not be committed (path: rule)")


if __name__ == "__main__":
    unittest.main()
