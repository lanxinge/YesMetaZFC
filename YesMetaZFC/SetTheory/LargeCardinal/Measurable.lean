import YesMetaZFC.SetTheory.LargeCardinal.MeasureCompleteness

/-! # 武丁基数以下的实际可测基数

非主 κ 完备超滤迫使 κ 为初始序数：若较短序数枚举 κ，
各枚举值的补单点集都测度一，但它们的短交为空，矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_cardinal_l (hZF : M.Models ZF) {κ U} (hκ : M.IsOrdinal κ)
    (hU : FilterZF.Maximal_d (ℳ := M) κ U) (hn : Ed_nonprincipal_d U) (hc : Ed_complete_d κ κ U) :
    M.IsCardinal I κ := by
  refine ⟨hκ, fun μ hμ ⟨f, hf⟩ => ?_⟩
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => κ), fun _ => κ⟩
  let φ : BinarySchema 2 := { body := .forallE (.iff (.mem .newest (.bound 1))
    (.conj (.mem .newest (.bound 4)) (.neg (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))))) }
  have sat i r : φ.denote ρ i r ↔ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ M.PairMember I i x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have total i (hi : M.mem i μ) : ∃ r, φ.denote ρ i r ∧ M.mem r U := by
    obtain ⟨x, hx, hix⟩ := hf.1.1.2.2 i hi
    obtain ⟨s, hs⟩ := KP.exists_singleton (ZF.modelsKP hZF) x
    obtain ⟨r, hr⟩ := KP.difference_exists_d (ZF.modelsKP hZF) s κ
    have eq y : M.mem y s ↔ M.PairMember I i y f :=
      (hs y).trans ⟨fun hy => hy.symm ▸ hix, fun hy => hf.1.1.1.2 i y x hy hix⟩
    refine ⟨r, (sat i r).mpr (fun y => (hr y).trans (and_congr_right fun _ => not_congr (eq y))), ?_⟩
    exact (FilterZF.maximal_decides_d hZF hU (fun y hy => (hs y).mp hy ▸ hx) hr).elim
      (fun h => (hn x s hs h).elim) id
  have unique i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s :=
    hZF.1.eq_of_same_members r s (fun x => ((sat i r).mp hr x).trans ((sat i s).mp hs x).symm)
  obtain ⟨g, hg, hgp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (fun i hi => (total i hi).imp fun _ hr => hr.1)
    (fun i _ r s hr hs => unique i r s hr hs) (fun i r hi hr => by
      obtain ⟨s, hs, hsU⟩ := total i hi
      exact (unique i s r hs hr) ▸ hsU)
  obtain ⟨r, hrU, hr⟩ := hc μ hμ g (fn0_of_function_l (ZF.modelsKP hZF) hg)
  obtain ⟨x, hx⟩ := hU.2.1 r hrU
  obtain ⟨hxκ, hall⟩ := (hr x).mp hx
  obtain ⟨i, hi, hix⟩ := hf.2 x hxκ
  obtain ⟨s, hs, his⟩ := hg.2.2 i hi
  exact (((sat i s).mp ((hgp i s).mp his).2 x).mp (hall i hi s hs his)).2 hix

def Measurable_d (κ : M.Domain) : Prop := M.IsCardinal I κ ∧ ∃ ω U, M.IsOmega ω ∧ M.mem ω κ ∧
  FilterZF.Maximal_d (ℳ := M) κ U ∧ Ed_nonprincipal_d U ∧ Ed_complete_d κ κ U

def measurable_m {d} (κ : Term d) : Formula 1 d := .conj (Formula.isCardinal 𝒞 κ)
  (.existsE (.existsE (.conj (Formula.isOmega (.bound 1)) (.conj (.mem (.bound 1) κ.weaken.weaken)
    (.conj (FilterZF.maximal_m κ.weaken.weaken .newest)
      (.conj (ed_nonprincipal_m .newest) (ed_complete_m κ.weaken.weaken κ.weaken.weaken .newest)))))))
derive_free_closed measurable_m

theorem measurable_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ : Term d) :
    Formula.satisfies ρ (measurable_m (𝒞 := 𝒞) κ) ↔ Measurable_d I (κ.eval ρ) := by
  simp only [measurable_m, Measurable_d, Formula.satisfies_conj_iff, Formula.satisfies_isCardinal_iff I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff,
    FilterZF.maximal_sat_d, ed_nonprincipal_sat_l hE, ed_complete_sat_l hE, Definitional.Term.eval_weaken]
  rfl

/-- 武丁基数以下的可测基数无界，测度由原定义中的实际嵌入构造。 -/
theorem woodin_measurable_above_l (hZF : M.Models ZF) {δ α} (hδ : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ κ, M.mem α κ ∧ M.mem κ δ ∧ Measurable_d I κ := by
  obtain ⟨ω, κ, U, hω, hωκ, hακ, hκδ, hκ, hU, hn, hc⟩ := wd_complete_ultrafilter_l I hZF hδ hα
  exact ⟨κ, hακ, hκδ, ed_cardinal_l I hZF hκ hU hn hc, ω, U, hω, hωκ, hU, hn, hc⟩

theorem woodin_proper_measurables_l (hZF : M.Models ZF) (h : Wd_proper_d I) :
    ∀ α, M.IsOrdinal α → ∃ κ, M.mem α κ ∧ Measurable_d I κ := by
  intro α hα
  obtain ⟨δ, hαδ, hδ⟩ := h α hα
  obtain ⟨κ, hακ, _, hκ⟩ := woodin_measurable_above_l I hZF hδ hαδ
  exact ⟨κ, hακ, hκ⟩

end YesMetaZFC.SetTheory.LargeCardinal
