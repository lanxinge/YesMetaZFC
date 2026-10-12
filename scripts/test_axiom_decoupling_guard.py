"""用临时模块检查公理守卫的正例及拒绝路径，不增加生产公理。"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(os.environ.get("YESMETAZFC_GUARD_TEST_ROOT", Path(__file__).resolve().parents[1]))
MODULE = "AxiomDecouplingGuardTest"


class AxiomDecouplingGuardTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=ROOT,
                                check=True, capture_output=True, text=True).stdout.strip()
        cls.lean = str(Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean"))
        cls.lean_path = json.loads(subprocess.run(
            ["lake", "env", sys.executable, "-c",
             "import json, os; print(json.dumps(os.environ.get('LEAN_PATH', '')))"],
            cwd=ROOT, check=True, capture_output=True, text=True).stdout)

    def check_guard(self, declarations, expected, error=None, endpoint="target", dependency=None):
        with tempfile.TemporaryDirectory(prefix="axiom-decoupling-") as directory:
            root = Path(directory)
            source = root / f"{MODULE}.lean"
            extra_import = "import AxiomDecouplingDependency\n" if dependency is not None else ""
            source.write_text(f"import Lean\n{extra_import}namespace {MODULE}\n{declarations}\nend {MODULE}\n",
                              encoding="utf-8")
            env = {**os.environ, "LEAN_NUM_THREADS": "1",
                   "LEAN_PATH": os.pathsep.join([directory, self.lean_path])}
            if dependency is not None:
                dep = root / "AxiomDecouplingDependency.lean"
                dep.write_text("import Lean\n" + dependency, encoding="utf-8")
                dep_build = subprocess.run([self.lean, "-R", directory, str(dep), "-o",
                                            str(dep.with_suffix(".olean"))], cwd=ROOT, env=env,
                                           capture_output=True, text=True)
                self.assertEqual(dep_build.returncode, 0, dep_build.stdout + dep_build.stderr)
            built = subprocess.run([self.lean, "-R", directory, str(source), "-o",
                                    str(source.with_suffix(".olean"))], cwd=ROOT, env=env,
                                   capture_output=True, text=True)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            bounds = root / "bounds.json"
            bounds.write_text(json.dumps({"modules": [MODULE],
                "bounds": {(endpoint if endpoint.startswith("_private.") else f"{MODULE}.{endpoint}"): expected}}), encoding="utf-8")
            guard = root / "Guard.lean"
            emitted = subprocess.run([sys.executable, str(ROOT / "scripts/check_axiom_decoupling.py"),
                                      "--bounds", str(bounds), "--emit", str(guard)],
                                     cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
            audited = subprocess.run([self.lean, "--stdin"], input=guard.read_text(encoding="utf-8"),
                                     cwd=ROOT, env=env, capture_output=True, text=True)
            log = audited.stdout + audited.stderr
            if error is None:
                self.assertEqual(audited.returncode, 0, log)
                self.assertIn("AXIOM_DECOUPLING_PASS:", log)
            else:
                self.assertNotEqual(audited.returncode, 0, log)
                self.assertIn(error, log)

    def test_axiom_free_endpoint_passes(self):
        self.check_guard("theorem target : True := True.intro", [])

    def test_exact_propext_endpoint_passes(self):
        self.check_guard("theorem target : (True ∧ True) = True :=\n"
                         "  propext ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩",
                         ["propext"])

    def test_new_axiom_dependency_is_rejected(self):
        self.check_guard("theorem target : (True ∧ True) = True :=\n"
                         "  propext ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩",
                         [], "Raw axiom set changed")

    def test_stricter_dependency_requires_bound_update(self):
        self.check_guard("theorem target : True := True.intro", ["propext"],
                         "Raw axiom set changed")

    def test_project_axiom_is_rejected(self):
        self.check_guard("axiom forbidden : True\ntheorem target : True := True.intro", [],
                         "Unexpected project axiom")

    def test_imported_custom_axiom_is_rejected(self):
        self.check_guard("theorem target : True := Dependency.forbidden", [],
                         "Unexpected transitive axiom", dependency="axiom Dependency.forbidden : True\n")

    def test_unsafe_declaration_is_rejected(self):
        self.check_guard("unsafe def forbidden : Nat := 0\ntheorem target : True := True.intro", [],
                         "Unsafe declaration")

    def test_noncomputable_data_is_rejected(self):
        self.check_guard("noncomputable def forbidden : Nat := Classical.choice (show Nonempty Nat from ⟨0⟩)\n"
                         "theorem target : True := True.intro", [], "Noncomputable declaration")

    def test_recursive_constructor_closure_passes(self):
        self.check_guard("""
theorem leftTag : True := Eq.mp (propext (Iff.refl True)) True.intro
theorem rightTag : (fun x : Unit => x) = (fun x : Unit => x) := funext (fun _ => rfl)
inductive Tagged : Prop where
  | left : Tagged → leftTag = True.intro → Tagged
  | right : Tagged → rightTag = (rfl : (fun x : Unit => x) = (fun x : Unit => x)) → Tagged
""", ["propext", "Quot.sound"], endpoint="Tagged.left")

    def test_private_numeric_name_passes(self):
        self.check_guard("private theorem hidden : True := True.intro", [],
                         endpoint=f"_private.{MODULE}.0.{MODULE}.hidden")

    def test_missing_endpoint_is_rejected(self):
        self.check_guard("theorem target : True := True.intro", [], "Missing production declaration",
                         endpoint="absent")


if __name__ == "__main__":
    unittest.main()
