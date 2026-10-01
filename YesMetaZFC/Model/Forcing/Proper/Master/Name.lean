import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.Model.Forcing.Internal.Functions.Rules

/-! # 主条件名称的原公式与局部消去规则 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def mstr_body_m : Formula 1 4 := mstr_m (.bound 3) (.bound 2) (.bound 3) (.bound 1) .newest
@[simp] theorem mstr_body_closed_l : mstr_body_m.FreeClosed := mstr_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl

def mstr_env_l {M : SetTheory.Structure.{u}} (A T μ t : M.Domain) : Env M 4 :=
  (((⟨fun _ => A, fun _ => A⟩ : Env M 1).push T).push μ).push t

def mstr_lower_sub_l : Fin 4 → Term 5 :=
  Fin.cases .newest (Fin.cases (.bound 2) (Fin.cases (.bound 3) (fun _ => .bound 4)))

def mstr_lower_s : UnarySchema 4 := {
  body := .conj (below_m (.bound 4) (.bound 3) (.bound 4) .newest (.bound 1))
    (mstr_body_m.bind mstr_lower_sub_l)
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    refine ⟨below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl, ?_⟩
    exact (Definitional.Formula.freeClosed_bind_iff_of_closed _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) _).mpr mstr_body_closed_l }

def mstr_lower_exists_m : Formula 1 4 := .existsE (.conj (.mem .newest (.bound 4)) mstr_lower_s.body)
@[simp] theorem mstr_lower_exists_closed_l : mstr_lower_exists_m.FreeClosed := by
  simp only [mstr_lower_exists_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨rfl, rfl⟩, mstr_lower_s.freeClosed⟩

theorem mstr_lower_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) (ρ : Env M 5) :
    Formula.satisfies ρ mstr_lower_s.body ↔ Below_d M (ρ.bound 4) (ρ.bound 3) (ρ.bound 4) (ρ.bound 0) (ρ.bound 1) ∧
      Mstr_d M (ρ.bound 4) (ρ.bound 3) (ρ.bound 4) (ρ.bound 2) (ρ.bound 0) := by
  simp only [mstr_lower_s, Formula.satisfies_conj_iff, below_sat_l M hE,
    Formula.satisfies_bind, mstr_body_m, mstr_sat_l M hE]
  rfl

/-- 一条被迫的主加强正文，同时给出第二坐标加强和同条件的主性。 -/
theorem force_mstr_lower_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {B R z A T μ s v p}
    (h : Forces_d M B R z mstr_lower_s.body ((mstr_env_l A T μ s).push v) p) :
    Rel_force_d M B R z T p v s ∧ Forces_d M B R z mstr_body_m (mstr_env_l A T μ v) p := by
  let ρ := mstr_env_l A T μ s
  obtain ⟨hl, hm⟩ := (forces_conj_l _ _ (ρ.push v) p).mp h
  refine ⟨(force_entry_l hE (ρ.push v) p .newest (.bound 1) (.bound 3)).mp
    ((forces_conj_l _ _ (ρ.push v) p).mp ((forces_conj_l _ _ (ρ.push v) p).mp hl).2).2, ?_⟩
  have hf := (forces_bind_l hE mstr_body_m mstr_lower_sub_l (ρ.push v) p).mp hm
  exact (forces_env_l hE mstr_body_m mstr_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) p).mp hf

end YesMetaZFC.Model.Forcing.Internal
