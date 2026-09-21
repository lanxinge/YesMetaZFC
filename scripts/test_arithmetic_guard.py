"""数据边界审计的正反例；临时模块不进入正式算术库或共享构建目录。"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_arithmetic import DATA_GUARD, ROOT


class DataGuardTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=ROOT,
                                check=True, capture_output=True, encoding="utf-8").stdout.strip()
        cls.lean = str(Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean"))

    def check_module(self, source, accepted):
        module = "YesMetaZFC.Model.Arithmetic.GuardTest"
        with tempfile.TemporaryDirectory(prefix="arithmetic-guard-") as directory:
            root = Path(directory)
            path = root / (module.replace(".", "/") + ".lean")
            path.parent.mkdir(parents=True)
            path.write_text("import Lean\n" + source + "\n", encoding="utf-8")
            env = {**os.environ, "LEAN_NUM_THREADS": "1",
                   "LEAN_PATH": directory}
            build = subprocess.run(
                [self.lean, "-R", directory, str(path), "-o", str(path.with_suffix(".olean"))],
                cwd=ROOT, env=env, capture_output=True, encoding="utf-8", errors="replace")
            self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
            audit = subprocess.run(
                [self.lean, "--stdin"], input=f"import {module}\n" + DATA_GUARD,
                cwd=ROOT, env=env, capture_output=True, encoding="utf-8", errors="replace")
            log = audit.stdout + audit.stderr
            if accepted:
                self.assertEqual(audit.returncode, 0, log)
                self.assertIn("DATA_GUARD_PASS: 1 modules", log)
            else:
                self.assertNotEqual(audit.returncode, 0, log)
                self.assertNotIn("DATA_GUARD_PASS:", log)
                self.assertIn("bad_l", log)

    def test_computable_data_and_classical_proofs(self):
        self.check_module("""
def data_l (n : Nat) : Nat := n + 1
def graph_l (m n : Nat) : Prop := m + 1 = n
theorem classical_l (P : Prop) : P ∨ ¬P := Classical.em P
theorem witness_l {α : Type} (h : Nonempty α) : ∃ x : α, x = x :=
  ⟨Classical.choice h, rfl⟩
""", True)

    def test_data_choice(self):
        self.check_module("noncomputable def bad_l {α : Type} (h : Nonempty α) : α := Classical.choice h", False)

    def test_private_data_choice(self):
        self.check_module("private noncomputable def bad_l {α : Type} (h : Nonempty α) : α := Classical.choice h", False)

    def test_other_namespace(self):
        self.check_module("namespace Other\nnoncomputable def bad_l {α : Type} (h : Nonempty α) : α := Classical.choice h\nend Other", False)

    def test_custom_axiom(self):
        self.check_module("axiom bad_l : Nat", False)


if __name__ == "__main__":
    unittest.main()
