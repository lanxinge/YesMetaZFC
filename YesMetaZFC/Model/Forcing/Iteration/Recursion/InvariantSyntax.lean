import YesMetaZFC.Model.Forcing.Iteration.Recursion.Syntax

/-! # 递归轨迹合法性的实际归纳公式 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def row_invariant_s {n} (φ : BinarySchema (n+4)) (k : Bool) : UnarySchema (n+2) := {
  body := .forallE (.imp (Formula.isRecursiveSequence kpair_convention_l (row_op_s φ k)
    (Definitional.TermVector.boundParameters (n+2) 2) .newest (.bound 1))
    (.existsE (.existsE (row_good_m k (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) .newest))))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨Formula.isRecursiveSequence_freeClosed _ _ _ _ _ (Definitional.TermVector.boundParameters_freeClosed _ _) rfl rfl,
      row_good_m_freeClosed _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl⟩ }

theorem row_invariant_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (k : Bool) (ω e α) :
    (row_invariant_s φ k).denote (row_op_env_l ρ ω e) α ↔
      ∀ S, M.IsRecursiveSequence I (Row_op_d I k ω e φ ρ) S α → ∃ F H, Row_good_d I k ω e S α F H := by
  have ho : (row_op_s φ k).denote (row_op_env_l ρ ω e) = Row_op_d I k ω e φ ρ :=
    funext fun S => funext fun c => propext (row_op_denote_l I hE φ ρ k ω e S c)
  simp only [row_invariant_s, UnarySchema.denote, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isRecursiveSequence_iff I hE,
    Definitional.TermVector.evalEnv_boundParameters_two, Formula.satisfies_exists_iff,
    row_good_sat_l I hE, ho]
  rfl

end YesMetaZFC.Model.Forcing.Internal
