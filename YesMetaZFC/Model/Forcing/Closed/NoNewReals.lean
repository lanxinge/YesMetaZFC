import YesMetaZFC.Model.Forcing.Applications.Collapse.Basic
import YesMetaZFC.Model.Forcing.Internal.Extension.Operations

/-! # 内部可数闭力迫不增加实数

同时判定规范自然数对名称的隶属；内部可数闭性给出稠密的全判定条件。
泛型滤子遇到该实际可定义稠密集后，地模型分离得到解释完全相同的旧实数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable (M : SetTheory.Structure.{u})

def Dec_check_d (B R z b t n p : M.Domain) : Prop := ∃ s, Check_d M b n s ∧
  (Mem_force_d M B R z p s t ∨ Neg_d M B R z (fun q => Mem_force_d M B R z q s t) p)

def dec_check_m {n} (B R z b t a p : Term n) : Formula 1 n :=
  .existsE (.conj (check_m b.weaken a.weaken .newest) (.disj
    (mem_force_m B.weaken R.weaken z.weaken p.weaken .newest t.weaken)
    (.forallE (.imp (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest p.weaken.weaken)
      (.neg (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1) t.weaken.weaken))))))
derive_free_closed dec_check_m

theorem dec_check_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b t a p : Term n) :
    Formula.satisfies ρ (dec_check_m B R z b t a p) ↔
      Dec_check_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (t.eval ρ) (a.eval ρ) (p.eval ρ) := by
  simp only [dec_check_m, Dec_check_d, Neg_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, check_sat_l M hE,
    mem_force_sat_l M hE, below_sat_l M hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push]

variable {M} {B R z ω : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
include O hZFC hU

/-- 每个扩张实数都是一个模型内部旧子集的规范名称解释。 -/
theorem no_new_reals_l (hω : M.IsOmega ω)
    (hc : Closed_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z ω)
    {b w t : M.Domain} {W x : Name_quot_l M B R z U} (hb : U b)
    (hw : Check_d M b ω w) (hv : Qval_d M B R z U w W) (ht : Qval_d M B R z U t x)
    (hx : ∀ y, y ∈ x → y ∈ W) :
    ∃ a s, M.MemberSubset a ω ∧ Check_d M b a s ∧ Qval_d M B R z U s x := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  have hbB := (hU.proper b hb).1
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push t
  let φ : BinarySchema 5 := {
    body := dec_check_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ n p : φ.denote ρ n p ↔ Dec_check_d M B R z b t n p :=
    dec_check_sat_l M hZF.1 ((ρ.push n).push p) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have hd n (_ : M.mem n ω) p (_ : M.mem p B) (_ : p ≠ z) : Dense_d M B R z (φ.denote ρ n) p := by
    obtain ⟨s, hs, _, _⟩ := zf_check_l M hZF hbB n
    intro q hq
    by_cases h : ∃ r, Below_d M B R z r q ∧ Mem_force_d M B R z r s t
    · obtain ⟨r, hr, hm⟩ := h
      exact ⟨r, hr, (hφ n r).mpr ⟨s, hs, Or.inl hm⟩⟩
    · exact ⟨q, below_refl_l O hq.1 hq.2.1, (hφ n q).mpr
        ⟨s, hs, Or.inr (fun r hr hm => h ⟨r, hr, hm⟩)⟩⟩
  have hl n (_ : M.mem n ω) : Lower_d M B R z (φ.denote ρ n) := by
    intro p q hp hq h
    obtain ⟨s, hs, hm⟩ := (hφ n p).mp h
    exact (hφ n q).mpr ⟨s, hs, hm.elim
      (fun hm => Or.inl ((regular_mem_l O s t).1 p q hp hq hm))
      (fun hm => Or.inr (neg_lower_l O _ p q hp hq hm))⟩
  let ψ : UnarySchema 6 := {
    body := .forallE (.imp (.mem .newest (.bound 2))
      (dec_check_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1))) }
  have hψ p : ψ.denote (ρ.push ω) p ↔ ∀ n, M.mem n ω → Dec_check_d M B R z b t n p := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, dec_check_sat_l M hZF.1]
    rfl
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  obtain ⟨p, hp, hdec⟩ := generic_pick_l hZF hU ⟨6, ψ, ρ.push ω, hψ⟩ hp₀ (by
    intro q hq
    obtain ⟨r, hr, hd⟩ := closed_intersection_l O hZFC hω hc φ ρ (fun i hi => hd i hi q hq.1 hq.2.1) hl hq.1 hq.2.1
    exact ⟨r, hr, fun n hn => (hφ n r).mp (hd n hn)⟩)
  let χ : UnarySchema 6 := {
    body := .existsE (.conj (check_m (.bound 4) (.bound 1) .newest)
      (mem_force_m (.bound 7) (.bound 6) (.bound 5) (.bound 2) .newest (.bound 3))) }
  obtain ⟨a, ha⟩ := ZF.separation_exists_d hZF χ (ρ.push p) ω
  have ha n : M.mem n a ↔ M.mem n ω ∧ ∃ s, Check_d M b n s ∧ Mem_force_d M B R z p s t := by
    rw [ha n]
    simp only [χ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      check_sat_l M hZF.1, mem_force_sat_l M hZF.1]
    rfl
  obtain ⟨s, hsa, hsn, _⟩ := zf_check_l M hZF hbB a
  obtain ⟨y, hsy⟩ := name_value_l (R := R) (z := z) (U := U) hsn
  have heq : y = x := by
    apply (extension_ext_l O hZF hU).eq_of_same_members
    intro v
    constructor
    · intro hvy
      obtain ⟨n, r, hna, hnr, hrv⟩ := (check_val_mem_l O hZF hU hsa hsy hb).mp hvy
      obtain ⟨_, r', hnr', hm⟩ := (ha n).mp hna
      have hr := check_unique_l M hZF.1 (check_ind_l M hZF) b n r' r hnr' hnr
      subst r'
      exact (qval_mem_forcing_l O hZF hU hrv ht).mp ⟨p, hp, hm⟩
    · intro hvx
      obtain ⟨n, r, hnω, hnr, hrv⟩ := (check_val_mem_l O hZF hU hw hv hb).mp (hx v hvx)
      obtain ⟨r', hnr', hm⟩ := hdec n hnω
      have hr := check_unique_l M hZF.1 (check_ind_l M hZF) b n r' r hnr' hnr
      subst r'
      rcases hm with hm | hm
      · exact (check_val_mem_l O hZF hU hsa hsy hb).mpr
          ⟨n, r, (ha n).mpr ⟨hnω, r, hnr, hm⟩, hnr, hrv⟩
      · have hn := (generic_neg_l O hZF hU (mem_force_defined_l M hZF.1 B R z r t)
          (regular_mem_l O r t).1).mp ⟨p, hp, hm⟩
        exact False.elim (hn ((qval_mem_forcing_l O hZF hU hrv ht).mpr hvx))
  exact ⟨a, s, fun n hn => ((ha n).mp hn).1, hsa, heq ▸ hsy⟩

end YesMetaZFC.Model.Forcing.Internal
