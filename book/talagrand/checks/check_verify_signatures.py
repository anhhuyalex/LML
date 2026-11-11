"""Checks for ``verify_signatures``."""
import unittest

import verify_signatures as v


def command(name, severities):
    return {"source": f"set_option format.width 72 in\nopen A in\n#check {name}",
            "messages": [{"severity": s, "lines": []} for s in severities]}


class VerifySignatureChecks(unittest.TestCase):
    def test_reports_missing_empty_and_failing_names(self):
        data = {"inlineCommands": [command("A.ok", ["info"]), command("A.bad", ["error"]),
                                   command("A.silent", [])]}
        found = v.problems(["A.ok", "A.bad", "A.silent", "A.absent"], data)
        self.assertEqual(sorted(found), ["A.absent", "A.bad", "A.silent"])

    def test_all_good_is_empty(self):
        self.assertEqual(v.problems(["A.ok"], {"inlineCommands": [command("A.ok", ["info"])]}), {})

    def test_the_real_cache_format_is_understood_after_expansion(self):
        # `#check` sources written by lean-signature-source end in the bare name.
        self.assertEqual(list(v.checked_results({"inlineCommands": [command("X.y_z'", ["info"])]})), ["X.y_z'"])


if __name__ == "__main__":
    unittest.main()
