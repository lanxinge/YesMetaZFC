import YesMetaZFC.SetTheory.LargeCardinal.DerivedEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystem
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource

/-! # 原嵌入对实际源分量的因子图

规范类中任意一个代表都有同一个种子求值。唯一值替代构造真正的商函数，
原子真值定理同时证明单射性和成员关系的保持、反映。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

theorem ee_component_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L S F a c : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (hm : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ C T e, Smdl_d I c C T ∧ M.IsSetInjectionFromTo I e C Y ∧
      (∀ D y, Rd_entry_d D y e ↔ M.mem D C ∧ ∃ f, M.mem f D ∧ Ee_value_d j a f y) ∧
      (∀ D y f, Rd_entry_d D y e → M.mem f D → Ee_value_d j a f y) ∧
      ∀ D E y z, Rd_entry_d D y e → Rd_entry_d E z e → (Rd_entry_d D E T ↔ M.mem y z) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨n, D, U, G, p, C, T, hn, ha, hD, haU, hG, model⟩ := hm
  obtain ⟨haS, m, D₀, ha₀, hD₀, hu⟩ := (hF.2.2 a U).mp haU
  have eq := ha₀.domain_eq_l hZF.1 ha
  subst m
  have eq := hZF.1.eq_of_same_members D₀ D (fun s => (hD₀ s).trans (hD s).symm)
  subst D₀
  have hDX := source.space_mem_l hZF hn hD
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  have haD := es_seed_l I hZF source.omega h source.transitive hY
    (hc.fixed n (hc.ordinal.transitive ω hωκ n hn)) hc.image hjD hD hL (hSY a haS) ha
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  have hPX := source.transitive P (ZF.v_power_mem_l I hZF hV hδ hDX hP)
  obtain ⟨b, hX⟩ := source.code
  have sf f (hf : M.mem f G) := sc_function_domain_l source.theory.algebra ((hG f).mp hf).1 ((hG f).mp hf).2
  have eval f (hf : M.mem f G) := ed_evaluation_l hZF source.omega h source.transitive hY hjD haD (sf f hf)
  have atoms f g y z (hf : M.mem f G) (hg : M.mem g G) (hy : Ee_value_d j a f y) (hz : Ee_value_d j a g z) :=
    ed_evaluation_atoms_l hZF source.omega h source.transitive hY hjD haD hP hPX hu hX (sf f hf) (sf g hg) hy hz
  have ultra := (es_measures_l hZF source.omega hV hδ h hY hc hL hS hSY hF).at_l hZF.1 haU ha hD
  have represent E (hE : M.mem E C) f (hf : M.mem f E) := model.map.member_l I hZF.1 ultra.1.base_l hE hf
  let ρ := (⟨fun _ => j, fun _ => j⟩ : Env M 1).push a
  let φ : BinarySchema 2 := {
    body := Formula.existsMem (.bound 1) (ee_value_m (.bound 4) (.bound 3) .newest (.bound 1)) }
  have sat E y : φ.denote ρ E y ↔ ∃ f, M.mem f E ∧ Ee_value_d j a f y := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, ee_value_sat_l hZF.1]; rfl
  have any E y (hE : M.mem E C) (hy : φ.denote ρ E y) f (hf : M.mem f E) : Ee_value_d j a f y := by
    obtain ⟨g, hg, hgy⟩ := (sat E y).mp hy
    have hgp := represent E hE g hg
    have hfp := represent E hE f hf
    have hfg := (rp_kernel_l I hZF.1 ultra.1.base_l model.map hfp hgp).mp rfl
    obtain ⟨z, _, hfz, _⟩ := eval f (model.map.projection.input_mem_of_pairMember hfp)
    exact (atoms f g z y (model.map.projection.input_mem_of_pairMember hfp)
      (model.map.projection.input_mem_of_pairMember hgp) hfz hgy).1.mp hfg ▸ hfz
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := Y)
    (fun E hE => by
      obtain ⟨f, hfp⟩ := (model.map.range E).mp hE
      obtain ⟨y, _, hy, _⟩ := eval f (model.map.projection.input_mem_of_pairMember hfp)
      exact ⟨y, (sat E y).mpr ⟨f, model.map.representative_l I ultra.1.base_l hfp, hy⟩⟩)
    (fun E hE y z hy hz => by
      obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
      obtain ⟨v, _, _, unique⟩ := eval f (model.map.projection.input_mem_of_pairMember (represent E hE f hf))
      exact (unique y hfy).trans (unique z (any E z hE hz f hf)).symm)
    (fun E y hE hy => by
      obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
      obtain ⟨z, hz, _, unique⟩ := eval f (model.map.projection.input_mem_of_pairMember (represent E hE f hf))
      exact (unique y hfy).symm ▸ hz)
  have repr E y (hy : Rd_entry_d E y e) : ∃ f, M.PairMember I f E p ∧ Ee_value_d j a f y := by
    obtain ⟨hE, hy⟩ := (es E y).mp hy
    obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
    exact ⟨f, represent E hE f hf, hfy⟩
  refine ⟨C, T, e, model.code, ⟨he, ?_⟩, fun E y => (es E y).trans (and_congr_right fun _ => sat E y),
    fun E y f hy hf => any E y ((es E y).mp hy).1 ((es E y).mp hy).2 f hf, ?_⟩
  · intro E H y hy hz
    obtain ⟨f, hfp, hfy⟩ := repr E y hy
    obtain ⟨g, hgp, hgy⟩ := repr H y hz
    exact (rp_kernel_l I hZF.1 ultra.1.base_l model.map hfp hgp).mpr
      ((atoms f g y y (model.map.projection.input_mem_of_pairMember hfp)
        (model.map.projection.input_mem_of_pairMember hgp) hfy hgy).1.mpr rfl)
  · intro E H y z hy hz
    obtain ⟨f, hfp, hfy⟩ := repr E y hy
    obtain ⟨g, hgp, hgz⟩ := repr H z hz
    exact (model.relation f g E H hfp hgp).trans (atoms f g y z
      (model.map.projection.input_mem_of_pairMember hfp) (model.map.projection.input_mem_of_pairMember hgp) hfy hgz).2

end YesMetaZFC.SetTheory.LargeCardinal
