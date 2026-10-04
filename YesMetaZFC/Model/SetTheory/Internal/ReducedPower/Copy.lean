import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.CopyKernel
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction

/-! # 两个不同源模型的完整超幂复制

π 在代表上的限制给出 [f]↦[π(f)]。两个相对测度只需在源中子集的像上
对应；任意内部公式的真值集合由同一程序搬运，再以两侧 Łoś 证明初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_copy_embedding_l {ω c d X R Y S π D D' P Q U V o₀ o₁ G H p₀ p₁ C₀ C₁ T₀ T₁ : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (source : Sc_theory_d I ω X R) (target : Sc_theory_d I ω Y S) (hD : M.PairMember I D D' π)
    (hP : Source_d X D P) (hQ : Source_d Y D' Q) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d D' Q V)
    (measure : ∀ A A', M.mem A P → M.PairMember I A A' π → (M.mem A U ↔ M.mem A' V))
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f)
    (hH : ∀ f, M.mem f H ↔ M.mem f Y ∧ Fn0_d D' Y f)
    (hM₀ : Rp_model_d I D X U R o₀ G p₀ C₀ T₀) (hM₁ : Rp_model_d I D' Y V S o₁ H p₁ C₁ T₁) :
    ∃ K j, M.IsSetFunctionFromTo I K G H ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G ∧ M.PairMember I f g π) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I K p₀ p₁ j := by
  have hDX := hπ.1.1.input_mem_of_pairMember hD
  have hDY := hπ.1.1.output_mem_of_pairMember hD
  have sf f (hf : M.mem f G) := sc_function_domain_l hZF hω hX hm source hDX ((hG f).mp hf).1 ((hG f).mp hf).2
  have sg f (hf : M.mem f H) := sc_function_domain_l hZF hω hY hn target hDY ((hH f).mp hf).1 ((hH f).mp hf).2
  obtain ⟨K, hK, ks⟩ := rs_copy_family_l hZF hω hX hY hm hn hπ source hD hG hH
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU.base hV.base hM₀.map hM₁.map hK (fun f g f' g' hf hg =>
    rs_copy_kernel_l hZF hω hX hY hm hn hπ source hD hP hQ hU hV measure
      ((ks f f').mp hf).2 ((ks g g').mp hg).2 (sf f (hK.input_mem_of_pairMember hf)) (sf g (hK.input_mem_of_pairMember hg)))
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨E', hE'⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨Q₀, hQ₀⟩ := ZF.exists_functionSpace hZF I ω C₀
  obtain ⟨Q₁, hQ₁⟩ := ZF.exists_functionSpace hZF I ω C₁
  refine ⟨K, j, hK, ks, ⟨hj, A, hA, fun z e₀ e₁ hz he₀ he₁ hh => ?_⟩, lift⟩
  obtain ⟨a, ha, eval₀⟩ := rp_representatives_l I hZFC hM₀.map he₀
  obtain ⟨a', ha', comp⟩ := ZF.exists_compositionFunction hZF I ha hK
  have ax : M.IsSetFunctionFromTo I a ω X := ⟨ha.1, ha.2.1, fun i hi =>
    (ha.2.2 i hi).imp fun f hf => ⟨((hG f).mp hf.1).1, hf.2⟩⟩
  have ay : M.IsSetFunctionFromTo I a' ω Y := ⟨ha'.1, ha'.2.1, fun i hi =>
    (ha'.2.2 i hi).imp fun f hf => ⟨((hH f).mp hf.1).1, hf.2⟩⟩
  have assign : Smap_assign_d I ω π a a' := by
    intro i hi f f' hif hff
    obtain ⟨g, _, hfg⟩ := hK.2.2 f (ha.output_mem_of_pairMember hif)
    have eq := hπ.1.1.1.2 f g f' ((ks f g).mp hfg).2 hff
    exact (comp i f').mpr ⟨hi, f, hif, eq ▸ hfg⟩
  have r₀ : Rs_eval_d I ω D X p₀ a e₀ := by
    intro i hi
    obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
    obtain ⟨B, _, hfp⟩ := hM₀.map.projection.2.2 f hf
    exact ⟨f, B, hif, sf f hf, hfp, eval₀ i hi f B hif hfp⟩
  have r₁ : Rs_eval_d I ω D' Y p₁ a' e₁ := by
    intro i hi
    obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
    obtain ⟨g, hg, hfg⟩ := hK.2.2 f hf
    obtain ⟨B, _, hfp⟩ := hM₀.map.projection.2.2 f hf
    obtain ⟨C, _, hgp⟩ := hM₁.map.projection.2.2 g hg
    exact ⟨g, C, (comp i g).mpr ⟨hi, f, hif, hfg⟩, sg g hg, hgp,
      hh i hi B C (eval₀ i hi f B hif hfp) (lift f g B C hfg hfp hgp)⟩
  obtain ⟨n, F, r, code⟩ := (hA z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  have bω := hω.transitive hZF b hb
  obtain ⟨B, B', hBX, hBB, trace, trace'⟩ := hπ.pe_trace_l hZF hω hX hY hm hn source target hD hE hE'
    code.2.1 code.2.2 hb bound ((hE a).mpr ax) ((hE' a').mpr ay)
    (fun i g hi => r₀.repr_l I ha.1 i g (bω i hi)) (fun i g hi => r₁.repr_l I ha'.1 i g (bω i hi)) assign
  have hBP := (hP B).mpr ⟨hBX, fun v hv => ((trace v).mp hv).1⟩
  have hBQ := (hQ B').mpr ⟨hπ.1.1.output_mem_of_pairMember hBB, fun v hv => ((trace' v).mp hv).1⟩
  have old := rs_los_l hZF hω hX hm source hDX hP hU hG hM₀ hE hQ₀ code.2.1 hb bound code.2.2
    a e₀ ((hE a).mpr ax) ((hQ₀ e₀).mpr he₀) (fun i hi => r₀ i (bω i hi))
  have next := rs_los_l hZF hω hY hn target hDY hQ hV hH hM₁ hE' hQ₁ code.2.1 hb bound code.2.2
    a' e₁ ((hE' a').mpr ay) ((hQ₁ e₁).mpr he₁) (fun i hi => r₁ i (bω i hi))
  exact (satisfies_decode_l I hZF.1 hM₀.code code hQ₀).trans
    (old.symm.trans ((pe_holds_member_l I hU hBP trace).symm.trans ((measure B B' hBP hBB).trans
      ((pe_holds_member_l I hV hBQ trace').trans (next.trans (satisfies_decode_l I hZF.1 hM₁.code code hQ₁).symm)))))

end YesMetaZFC.SetTheory.Internal
