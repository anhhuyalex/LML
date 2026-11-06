#!/usr/bin/env python3
"""Exercise release tagging against a local remote, including an upstream-history merge."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("create_lean_release_tag.sh").resolve()


class ReleaseTagChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.repo, self.remote = root / "repo", root / "remote.git"
        self.repo.mkdir()
        self.git("init", "--initial-branch=main")
        self.git("config", "user.name", "Release tests")
        self.git("config", "user.email", "release-tests@example.invalid")
        subprocess.run(["git", "init", "--bare", "--initial-branch=main", str(self.remote)],
                       check=True, capture_output=True)
        self.git("remote", "add", "origin", str(self.remote))

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, text=True,
                                       stderr=subprocess.STDOUT).strip()

    def commit(self, version):
        (self.repo / "lean-toolchain").write_text(f"leanprover/lean4:{version}\n")
        self.git("add", "lean-toolchain")
        self.git("commit", "-m", version)
        return self.git("rev-parse", "HEAD")

    def run_script(self, **environment):
        return subprocess.run(["bash", str(SCRIPT)], cwd=self.repo, text=True,
                              env={**os.environ, "DO_RELEASE": "false", **environment},
                              capture_output=True)

    def remote_tags(self):
        return self.git("ls-remote", "--tags", "--refs", "origin")

    def test_upstream_merge_tags_only_current_fork_revision_and_is_repeatable(self):
        before = self.commit("v4.34.0-rc2")
        self.git("checkout", "-b", "upstream")
        self.commit("v4.34.0")
        self.commit("v4.36.0-rc2")
        self.git("checkout", "main")
        (self.repo / "fork.txt").write_text("fork-specific work\n")
        self.git("add", "fork.txt")
        self.git("commit", "-m", "Fork changes")
        self.git("merge", "--no-ff", "upstream", "-m", "Merge upstream")
        after = self.git("rev-parse", "HEAD")
        self.git("push", "origin", "main")
        self.assertIn("v4.34.0", self.git("log", f"{before}..{after}", "--format=%s"))
        for _ in range(2):
            result = self.run_script(AFTER=after)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(self.remote_tags().endswith("refs/tags/v4.36.0-rc2"))
            self.assertEqual(len(self.remote_tags().splitlines()), 1)
            self.assertEqual(self.git("rev-parse", "v4.36.0-rc2^{commit}"), after)

    def test_existing_release_tag_is_never_moved(self):
        original = self.commit("v4.36.0-rc2")
        self.assertEqual(self.run_script().returncode, 0)
        self.git("commit", "--allow-empty", "-m", "Later work")
        self.assertEqual(self.run_script().returncode, 0)
        self.assertEqual(self.git("rev-parse", "v4.36.0-rc2^{commit}"), original)

    def test_remote_failure_does_not_create_a_local_tag(self):
        self.commit("v4.36.0-rc2")
        self.git("remote", "set-url", "origin", str(self.remote / "missing"))
        self.assertNotEqual(self.run_script().returncode, 0)
        self.assertEqual(self.git("tag", "--list"), "")


if __name__ == "__main__":
    unittest.main()
