import YesMetaZFC.Model.SetTheory.ProjectSoundness
import YesMetaZFC.Model.SetTheory.ProjectExtensional
import YesMetaZFC.Model.FirstOrder.Substructure

/-! # 原 Project 公式的初等子模型对应

将有限参数环境直接送入原纯语言核。子模型的初等性逐公式传回 Project，保留
实际对象及隶属关系，供力迫公式的带参数反射使用。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
open Logic.FirstOrder
universe u
variable {ℳ : Logic.FirstOrder.Structure.{0,0,0,u} ℒ}

theorem submodel_extensional_l (A : Substructure_m ℳ) (h : A.Elementary_m)
    (hE : Extensional (reduct ℳ)) : Extensional (reduct A.structure_m) := by
  have ht : (fo_sentence SetTheory.Axioms.extensionality).TrueIn A.structure_m ↔
      (fo_sentence SetTheory.Axioms.extensionality).TrueIn ℳ := by
    simpa only [Formula.TrueIn, Env.map_empty] using h (fo_sentence SetTheory.Axioms.extensionality) Env.empty
  exact extensional_iff_l.mp (ht.mpr (extensional_iff_l.mpr hE))

/-- 原 Project 理论整体反射，只依赖初等性与源外延性。 -/
theorem submodel_models_l (A : Substructure_m ℳ) (h : A.Elementary_m)
    (hE : Extensional (reduct ℳ)) (T : SetTheory.Theory) :
    (reduct A.structure_m).Models T ↔ (reduct ℳ).Models T :=
  (models_iff (submodel_extensional_l A h hE) T).symm.trans
    ((A.models_iff_m h (fo_theory T)).trans (models_iff hE T))

def native_assignment_l : {n : Nat} → (Fin n → Carrier ℳ) → Assignment ℳ (fo_bound_context n)
  | 0, _, _, i => nomatch i
  | _+1, f, _, .here => f 0
  | _+1, f, _, .there i => native_assignment_l (fun j => f j.succ) i

theorem native_bound_l {n} (f : Fin n → Carrier ℳ) (i : Fin n) :
    native_assignment_l f (fo_bound_variable i) = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => exact Fin.cases rfl (fun i => ih (fun j => f j.succ) i) i

def native_env_l {n} (ρ : SetTheory.Env (reduct ℳ) n) : Logic.FirstOrder.Env ℳ (fo_bound_context n) [] where
  boundVal := native_assignment_l ρ.bound
  freeVal i := nomatch i

theorem project_native_l {n} (ρ : SetTheory.Env (reduct ℳ) n) :
    projectEnv (native_env_l ρ) ρ.free = ρ := by
  rw [SetTheory.Env.mk.injEq]
  exact ⟨funext (native_bound_l ρ.bound), rfl⟩

def submodel_env_l (A : Substructure_m ℳ) {n} (ρ : SetTheory.Env (reduct A.structure_m) n) :
    SetTheory.Env (reduct ℳ) n where
  bound i := (ρ.bound i).val
  free i := (ρ.free i).val

theorem submodel_env_push_l (A : Substructure_m ℳ) {n} (ρ : SetTheory.Env (reduct A.structure_m) n)
    (a : (reduct A.structure_m).Domain) : submodel_env_l A (ρ.push a) = (submodel_env_l A ρ).push a.val := by
  rw [SetTheory.Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩

theorem project_map_native_l (A : Substructure_m ℳ) {n} (ρ : SetTheory.Env (reduct A.structure_m) n) :
    projectEnv ((native_env_l ρ).map A.incl_m.map) (fun i => (ρ.free i).val) = submodel_env_l A ρ := by
  rw [SetTheory.Env.mk.injEq]
  exact ⟨funext (fun i => congrArg (fun a : A.structure_m.Carrier .set => a.val)
    (native_bound_l (ℳ := A.structure_m) ρ.bound i)), rfl⟩

/-- 原子及任意量词的初等对应直接消费原核的初等嵌入证明。 -/
theorem submodel_formula_l (A : Substructure_m ℳ) (h : A.Elementary_m)
    (hℳ : Extensional (reduct ℳ)) (hA : Extensional (reduct A.structure_m))
    {n} (φ : Project.Formula 1 n) (hφ : φ.FreeClosed) (ρ : SetTheory.Env (reduct A.structure_m) n) :
    Project.Formula.satisfies ρ φ ↔ Project.Formula.satisfies (submodel_env_l A ρ) φ := by
  have hs := formula_correct hA φ hφ (native_env_l ρ) ρ.free
  rw [project_native_l] at hs
  have ht := formula_correct hℳ φ hφ ((native_env_l ρ).map A.incl_m.map) (fun i => (ρ.free i).val)
  rw [project_map_native_l] at ht
  exact hs.symm.trans ((h (fo_formula φ hφ) (native_env_l ρ)).trans ht)

end YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
