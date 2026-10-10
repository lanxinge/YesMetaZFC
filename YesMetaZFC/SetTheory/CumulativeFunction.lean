import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.Rank
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.Card.SmallBound
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.InnerModel.Recursion.FunctionGraph

/-! # 共尾度以下定义域的秩有界性

逐点读取函数值的秩，再由定义域的小基数界和共尾度给出公共秩界。
结论同时保留源内值域界与函数图；不要求整座 Vδ 满足收集模式。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (modelsKP hZF)

include hZF in
/-- Vδ 中的序数恰在 δ 以下；这里先给出装配初始层级所需的反向界。 -/
theorem v_ordinal_height_l {𝒞 : OrderedPairConvention} {J : 𝒞.Interpretation M} {δ X α : M.Domain}
    (hX : V_d J δ X) (hα : M.IsOrdinal α) (ha : M.mem α X) : M.mem α δ := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => δ⟩
  let φ : UnarySchema 0 := { body := .forallE (.imp (v_m 𝒞 (.bound 1) .newest)
    (.forallE (.imp (KP.ord0_m .newest) (.imp (.mem .newest (.bound 1)) (.mem .newest (.bound 2)))))) }
  have sat β : φ.denote ρ β ↔ ∀ V, V_d J β V → ∀ γ, M.IsOrdinal γ → M.mem γ V → M.mem γ β := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      v_sat_l J hZF.1, KP.ord0_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff]; rfl
  apply (sat δ).mp (ZF.mem_ind_l M hZF I φ ρ ?_ δ) X hX α hα ha
  intro β ih
  apply (sat β).mpr
  intro V hV γ hγ hγV
  obtain ⟨η, W, hη, hW, sub⟩ := (ZF.v_unfold_l J hZF hV γ).mp hγV
  exact ordinal_down_l (ZF.modelsKP hZF) hγ (v_ordinal_l J hV)
    (fun x hx => (sat η).mp (ih η hη) W hW x (hγ.mem hx) (sub x hx)) hη

theorem v_small_function_l {δ ν Z D F μ : M.Domain} (hcf : M.IsCofinality I ν δ)
    (hμ : M.mem μ ν) (hD : M.CardinalLessOrEqual I D μ) (hDZ : M.mem D Z)
    (hZ : V_d I δ Z) (hf : M.IsSetFunctionFromTo I F D Z) :
    ∃ C, M.mem C Z ∧ M.IsSetFunctionFromTo I F D C ∧ M.mem F Z := by
  obtain ⟨Q, hQ⟩ := hcf.hasCofinalSequence
  have hδ := hQ.isLimitOrdinal
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => Z), fun _ => F⟩
  let φ : BinarySchema 2 := {
    body := Formula.existsMem (.bound 3) (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
      (rk_m (𝒞 := kpair_convention_l) .newest (.bound 1))) }
  have sat i α : φ.denote ρ i α ↔ ∃ x, M.mem x Z ∧ Rd_entry_d i x F ∧ Rk_d I x α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rk_sat_l I hZF.1]; rfl
  obtain ⟨G, hg, spec⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := δ)
    (fun i hi => by
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨α, hα⟩ := rk_exists_l I hZF x
      exact ⟨α, (sat i α).mpr ⟨x, hx, hix, hα⟩⟩)
    (fun i _ α β ha hb => by
      obtain ⟨x, _, hix, ha⟩ := (sat i α).mp ha
      obtain ⟨y, _, hiy, hb⟩ := (sat i β).mp hb
      exact rk_unique_l I hZF.1 ha (hf.1.2 i y x hiy hix ▸ hb))
    (fun i α _ h => by
      obtain ⟨x, hx, _, hα⟩ := (sat i α).mp h
      exact (rk_mem_l I hZF hα hZ).mp hx)
  obtain ⟨S, hS⟩ := exists_range_of_setFunction hZF I hg.1 hg.2.1
  have gs : M.IsSetFunctionFromTo I G D S := ⟨hg.1, hg.2.1, fun i hi =>
    (hg.2.2 i hi).imp fun α ha => ⟨(hS α).mpr ⟨i, ha.2⟩, ha.2⟩⟩
  have size := ordinal_image_bound_l I hZF (hcf.isCardinal.1.mem hμ) hD gs
    (fun α hα => ((hS α).mp hα).imp fun i hi => ⟨hg.input_mem_of_pairMember hi, hi⟩)
  obtain ⟨γ, hγ, bound⟩ := (small_subset_bounded_l I hZF hcf
    (fun α hα => ((hS α).mp hα).elim fun _ hi => hg.output_mem_of_pairMember hi) hμ size).exists_bound
  obtain ⟨β, hβ, hγβ⟩ := hδ.2.2 γ hγ
  obtain ⟨C, hc⟩ := v_exists_l I hZF (hδ.1.mem hβ)
  have hC := v_mem_l I hZF hc hZ hβ
  have values i x (hix : Rd_entry_d i x F) : M.mem x C := by
    obtain ⟨α, _, hiα⟩ := hg.2.2 i (hf.input_mem_of_pairMember hix)
    obtain ⟨y, _, hiy, hy⟩ := (sat i α).mp ((spec i α).mp hiα).2
    have hx : Rk_d I x α := hf.1.2 i y x hiy hix ▸ hy
    exact (rk_mem_l I hZF hx hc).mpr ((bound α ((hS α).mpr ⟨i, hiα⟩)).elim
      (fun eq => eq.symm ▸ hγβ) (fun hαγ => (hδ.1.mem hβ).transitive γ hγβ α hαγ))
  have fc : M.IsSetFunctionFromTo I F D C := ⟨hf.1, hf.2.1,
    fun i hi => (hf.2.2 i hi).imp fun x hx => ⟨values i x hx.2, hx.2⟩⟩
  obtain ⟨Y, hY, hDY, hCY⟩ := v_joint_bound_l I hZF hZ hDZ hC
  exact ⟨C, hC, fc, v_relation_mem_l I hZF hZ hδ hY fun p hp =>
    (fn0_of_function_l (modelsKP hZF) fc).1 p hp |>.elim fun i hi => hi.2.elim fun x hx =>
      ⟨i, hDY i hi.1, x, hCY x hx.1, hx.2⟩⟩

end YesMetaZFC.SetTheory.ZF
