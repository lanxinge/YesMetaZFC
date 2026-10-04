import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 滤子族的内部可数交性质

只要求每个内部 ω 族有共同成员，不附加任意 κ 短交封闭或选择公理。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Cc_d (ω D U : M.Domain) : Prop := ∀ F, Fn0_d ω U F →
  ∃ v, M.mem v D ∧ ∀ n B, M.mem n ω → Rd_entry_d n B F → M.mem v B

def cc_m {d} (ω D U : Term d) : Formula 1 d := .forallE (.imp (fn0_m ω.weaken U.weaken .newest)
  (Formula.existsMem D.weaken (.forallE (.forallE (.imp
    (.mem (.bound 1) ω.weaken.weaken.weaken.weaken)
    (.imp (rd_entry_m (.bound 1) .newest (.bound 3)) (.mem (.bound 2) .newest)))))))
derive_free_closed cc_m

theorem cc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D U : Term d) :
    Formula.satisfies ρ (cc_m ω D U) ↔ Cc_d (ω.eval ρ) (D.eval ρ) (U.eval ρ) := by
  simp only [cc_m, Cc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE,
    Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.FilterZF
