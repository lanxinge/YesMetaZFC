import YesMetaZFC.Model.Forcing.Iteration.Condition.Support
import YesMetaZFC.Model.Forcing.Stage.Transport
import YesMetaZFC.Model.Forcing.TwoStep.Order

/-! # 任意名称后继步的部分函数条件实现

把真实二步条件 (p,s) 编成省略顶坐标的部分函数。该编码是模型内部双射，
自动搬运偏序与完全嵌入；旧条件的定义域限制和两类支撑均有精确证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Row_code_d (M : SetTheory.Structure.{u}) (α t c q : M.Domain) : Prop :=
  ∃ p s, KPair_d M c p s ∧ Row_append_d M α t p s q

def row_code_m {n} (α t c q : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m c.weaken.weaken (.bound 1) .newest)
    (row_append_m α.weaken.weaken t.weaken.weaken (.bound 1) .newest q.weaken.weaken)))
derive_free_closed row_code_m

theorem row_code_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (α t c q : Term n) : Formula.satisfies ρ (row_code_m α t c q) ↔
      Row_code_d M (α.eval ρ) (t.eval ρ) (c.eval ρ) (q.eval ρ) := by
  simp only [row_code_m, Row_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, row_append_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 一次重编码全部二步条件，返回实际偏序、模型内双射、限制和支撑保持。 -/
theorem two_step_rows_l {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
    {B R z b A T W C S α β t : M.Domain} (h : Two_step_d M B R z b A T W C S)
    (L : Cond_order_d M C S C) (hβ : M.SuccessorOf β α) (hrow : ∀ p, M.mem p B → Row_d M α p) :
    ∃ D V F, (∀ q, M.mem q D ↔ ∃ c, M.mem c C ∧ Row_code_d M α t c q) ∧
      (∀ c q, Entry_d M c q F ↔ M.mem c C ∧ Row_code_d M α t c q) ∧
      M.IsSetBijectionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F C D ∧
      (∀ v, M.mem v V → ∃ p q, KPair_d M v p q) ∧
      (∀ p q, Entry_d M p q V ↔ ∃ c d, Entry_d M c p F ∧ Entry_d M d q F ∧ Entry_d M c d S) ∧
      Cond_order_d M D V D ∧ Reg_embed_d M C S C D V D F ∧
      (∀ q, M.mem q D → Row_d M β q) ∧
      (∀ q, M.mem q D → ∃ p, M.mem p B ∧ M.IsRestrictionOf
        (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α) ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
        (∀ p, M.mem p B → Row_supp_d I k ω p) → ∀ q, M.mem q D → Row_supp_d I k ω q := by
  have hα := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  let ρ : Env M 2 := (⟨fun _ => α, fun _ => α⟩ : Env M 1).push t
  let φ : BinarySchema 2 := { body := row_code_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ c q : φ.denote ρ c q ↔ Row_code_d M α t c q := row_code_sat_l hZF.1 ((ρ.push c).push q) _ _ _ _
  have total c (hc : M.mem c C) : ∃ q, φ.denote ρ c q := by
    obtain ⟨p, s, hcp, _, _, _⟩ := (h.conditions c).mp hc
    obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
    exact ⟨q, (hφ c q).mpr ⟨p, s, hcp, hq⟩⟩
  have unique c (_ : M.mem c C) q r (hq : φ.denote ρ c q) (hr : φ.denote ρ c r) : q = r := by
    obtain ⟨p, s, hcp, hq⟩ := (hφ c q).mp hq
    obtain ⟨p', s', hcp', hr⟩ := (hφ c r).mp hr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hcp hcp'
    exact row_append_unique_l M hZF.1 hq hr
  have inj c d q (hc : M.mem c C) (hd : M.mem d C) (hcq : φ.denote ρ c q) (hdq : φ.denote ρ d q) : c = d := by
    obtain ⟨p, s, hcp, hpq⟩ := (hφ c q).mp hcq
    obtain ⟨p', s', hdp, hp'q⟩ := (hφ d q).mp hdq
    have hp := hrow p ((two_step_mem_l h hcp).mp hc).2.1.1
    have hp' := hrow p' ((two_step_mem_l h hdp).mp hd).2.1.1
    obtain ⟨rfl, rfl⟩ := row_append_injective_l hZF.1 hα hp hp' hpq hp'q
    exact kpair_unique_l M hZF.1 hcp hdp
  obtain ⟨D, V, F, hD', hF', hBij, hGraph, hV, K, hReg⟩ := order_recode_l hZF L φ ρ total unique inj
  have hD q : M.mem q D ↔ ∃ c, M.mem c C ∧ Row_code_d M α t c q :=
    (hD' q).trans (exists_congr fun c => and_congr_right fun _ => hφ c q)
  have hF c q : Entry_d M c q F ↔ M.mem c C ∧ Row_code_d M α t c q :=
    (hF' c q).trans (and_congr_right fun _ => hφ c q)
  have pre q (hq : M.mem q D) : ∃ p s, M.mem p B ∧ Row_append_d M α t p s q := by
    obtain ⟨c, hc, p, s, hcp, hpq⟩ := (hD q).mp hq
    exact ⟨p, s, ((two_step_mem_l h hcp).mp hc).2.1.1, hpq⟩
  refine ⟨D, V, F, hD, hF, hBij, hGraph, hV, K, hReg, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, s, hp, hpq⟩ := pre q hq
    exact row_append_row_l hα (hrow p hp) hβ hpq
  · intro q hq
    obtain ⟨p, s, hp, hpq⟩ := pre q hq
    exact ⟨p, hp, (hrow p hp).graph, row_append_prefix_l hα (hrow p hp) hpq⟩
  · intro 𝒞 I k ω hω hs q hq
    obtain ⟨p, s, hp, hpq⟩ := pre q hq
    exact row_append_supp_l I hZF hω (hs p hp) hpq

end YesMetaZFC.Model.Forcing.Internal
