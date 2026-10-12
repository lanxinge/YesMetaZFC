"""句子闭合性策略的兼容性正反例；测试公理仅存在于临时模块中。

默认使用当前项目的 Lake 环境。隔离构建可同时指定
YESMETAZFC_TEST_LEAN 与 YESMETAZFC_TEST_LEAN_PATH。
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
MODULE = "SentenceClosednessGuardTest"


class SentenceClosednessTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lean = os.environ.get("YESMETAZFC_TEST_LEAN")
        lean_path = os.environ.get("YESMETAZFC_TEST_LEAN_PATH")
        if lean is not None or lean_path is not None:
            if lean is None or lean_path is None:
                raise RuntimeError("Specify both isolated-test environment variables")
            cls.lean, cls.lean_path = lean, lean_path
            return
        prefix = subprocess.run(
            ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, check=True,
            capture_output=True, encoding="utf-8").stdout.strip()
        cls.lean = str(Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean"))
        cls.lean_path = json.loads(subprocess.run(
            ["lake", "env", sys.executable, "-c",
             "import json, os; print(json.dumps(os.environ.get('LEAN_PATH', '')))"],
            cwd=ROOT, check=True, capture_output=True, encoding="utf-8").stdout)

    def check_module(self, source, expected_oracles, accepted=True,
                     expected_kernel_axioms=()):
        with tempfile.TemporaryDirectory(prefix="sentence-closedness-") as directory:
            path = Path(directory) / f"{MODULE}.lean"
            path.write_text(
                "import Lean\nimport YesMetaZFC.SetTheory.Notation.Surface\n"
                "open YesMetaZFC.SetTheory\n"
                f"namespace {MODULE}\n{source}\nend {MODULE}\n", encoding="utf-8")
            env = {**os.environ, "LEAN_NUM_THREADS": "1",
                   "LEAN_PATH": os.pathsep.join([directory, self.lean_path])}
            build = subprocess.run(
                [self.lean, "-R", directory, str(path), "-o", str(path.with_suffix(".olean"))],
                cwd=ROOT, env=env, capture_output=True, encoding="utf-8", errors="replace")
            log = build.stdout + build.stderr
            if not accepted:
                self.assertNotEqual(build.returncode, 0, log)
                self.assertIn("is false", log)
                self.assertFalse(path.with_suffix(".olean").exists(), log)
                return
            self.assertEqual(build.returncode, 0, log)
            expected = "#[" + ", ".join("`" + name for name in expected_oracles) + "]"
            sentence_expected = "#[" + ", ".join("`" + name for name in expected_kernel_axioms) + "]"
            audit_source = f'''import {MODULE}
run_cmd do
  let env ← Lean.getEnv
  let expected : Array Lean.Name := {expected}
  let permitted : Array Lean.Name := #[`propext, `Quot.sound] ++ expected
  let sentenceExpected : Array Lean.Name := {sentence_expected} ++ expected
  let mut actual : Array Lean.Name := #[]
  let mut seen := false
  for i in [0 : env.header.moduleNames.size] do
    unless env.header.moduleNames[i]! == `{MODULE} do continue
    seen := true
    for c in env.header.moduleData[i]!.constants do
      match c with
      | .axiomInfo _ => actual := actual.push c.name
      | _ => pure ()
      if c.isUnsafe then throwError "Unsafe test declaration: {{c.name}}"
      for ax in ← Lean.collectAxioms c.name do
        unless permitted.contains ax do
          throwError "Unexpected test dependency: {{c.name}} → {{ax}}"
  unless seen do throwError "Test module missing"
  unless actual.size == expected.size && actual.all expected.contains do
    throwError "Oracle inventory mismatch: expected {{expected}}, got {{actual}}"
  let sentenceAxioms ← Lean.collectAxioms `{MODULE}.sentence
  unless sentenceAxioms.size == sentenceExpected.size && sentenceAxioms.all sentenceExpected.contains do
    throwError "Sentence axiom set mismatch: expected {{sentenceExpected}}, got {{sentenceAxioms}}"
  Lean.logInfo m!"SENTENCE_CLOSEDNESS_PASS: test-only oracles {{actual}}"
'''
            audit = subprocess.run(
                [self.lean, "--stdin"], input=audit_source, cwd=ROOT, env=env,
                capture_output=True, encoding="utf-8", errors="replace")
            log = audit.stdout + audit.stderr
            self.assertEqual(audit.returncode, 0, log)
            self.assertIn("SENTENCE_CLOSEDNESS_PASS:", log)

    def test_transparent_formula_uses_kernel(self):
        self.check_module("""
def sentence : Definitional.Project.Sentence := sentence! ⟪∀ x, x = x⟫
""", [])

    def test_opaque_injection_retains_native_fallback(self):
        self.check_module("""
opaque formula : Definitional.Project.OpenFormula := .falsum
def sentence : Definitional.Project.Sentence := sentence! ⟪⌜formula⌝ₚ⟫
""", [f"{MODULE}.sentence._native.native_decide.ax_1"], expected_kernel_axioms=[])

    def test_open_formula_is_rejected(self):
        self.check_module("""
def sentence : Definitional.Project.Sentence := sentence! ⟪#ᶠ[0] ∈ #ᶠ[0]⟫
""", [], accepted=False)


if __name__ == "__main__":
    unittest.main()
