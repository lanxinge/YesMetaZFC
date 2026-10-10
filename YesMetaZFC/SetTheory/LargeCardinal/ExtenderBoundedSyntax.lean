import YesMetaZFC.SetTheory.LargeCardinal.ExtenderPrefix
import YesMetaZFC.SetTheory.OrdinalChoice

/-! # 有界投影的实际图条件

最后一项严格小于指定的旧坐标。保留任意指定坐标，第一坐标的通常定义为其实例。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_bp_at_d (κ n i A s x : M.Domain) : Prop := M.mem x κ ∧ ∃ t, M.mem t A ∧ M.MemberSubset s t ∧
  Rd_entry_d n x t ∧ ∃ y, M.mem y κ ∧ Rd_entry_d i y s ∧ M.mem x y

def ex_bp_at_m {d} (κ n i A s x : Term d) : Formula 1 d := .conj (.mem x κ)
  (Formula.existsMem A (.conj (Formula.subset s.weaken .newest) (.conj
    (rd_entry0_m n.weaken x.weaken .newest) (Formula.existsMem κ.weaken
      (.conj (rd_entry0_m i.weaken.weaken .newest s.weaken.weaken) (.mem x.weaken.weaken .newest))))))
derive_free_closed ex_bp_at_m
theorem ex_bp_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ n i A s x : Term d) :
    Formula.satisfies ρ (ex_bp_at_m κ n i A s x) ↔
      Ex_bp_at_d (κ.eval ρ) (n.eval ρ) (i.eval ρ) (A.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ex_bp_at_m, Ex_bp_at_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Ex_bp_d (κ n i A B : M.Domain) : Prop := ∀ s, M.mem s B ↔ Fn0_d n κ s ∧ ∃ x, Ex_bp_at_d κ n i A s x

theorem ex_bp_exists_l (hZF : M.Models ZF) (κ n i A : M.Domain) : ∃ B, Ex_bp_d κ n i A B := by
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n κ
  let ρ := (((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push n).push i).push A
  let φ : UnarySchema 4 := { body := .existsE (ex_bp_at_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨B, fun s => (hb s).trans (and_congr ?_ ?_)⟩
  · exact (hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  · simp only [φ, Formula.satisfies_exists_iff, ex_bp_at_sat_l hZF.1]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
