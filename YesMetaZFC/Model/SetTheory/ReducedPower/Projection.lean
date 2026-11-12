import YesMetaZFC.Model.SetTheory.ReducedPower.SourceProjection
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceComposition
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 坐标拉回精确保持代表等价

先在源中构造原代表的相等集，再取容许逆像。测度投影方程由此同时给出
等价保持与反映，供商图构造直接使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rs_pullback_eq_l (hZF : M.Models ZF) {ω c X R D E P Q U V t f g f' g'}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hP : Source_d X D P) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hf : Sfun_d X D f) (hg : Sfun_d X D g)
    (hF : Cp0_d E D X t f f') (hG : Cp0_d E D X t g g') : Rp_eq_d X U f g ↔ Rp_eq_d X V f' g' := by
  obtain ⟨A, hAX, ha⟩ := sc_equalizer_l I hZF hω hX hm theory hD hf hg.1
  have hAP := (hP A).mpr ⟨hAX, fun v hv => ((ha v).mp hv).1⟩
  obtain ⟨B, hB, hb, he⟩ := ht.2 A hAP
  have spec v : M.mem v B ↔ M.mem v E ∧ ∃ x, M.mem x X ∧ Rd_entry_d v x f' ∧ Rd_entry_d v x g' := by
    refine (hb v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, w, hw, hvw⟩
      obtain ⟨_, x, hx, hfx, hgx⟩ := (ha w).mp hw
      exact ⟨hv, x, hx, (hF.value_l ht.1 (hf.function_l hX) hvw).mpr hfx,
        (hG.value_l ht.1 (hg.function_l hX) hvw).mpr hgx⟩
    · rintro ⟨hv, x, hx, hfx, hgx⟩
      obtain ⟨w, hw, hvw⟩ := ht.1.2.1 v hv
      exact ⟨hv, w, (ha w).mpr ⟨hw, x, hx, (hF.value_l ht.1 (hf.function_l hX) hvw).mp hfx,
        (hG.value_l ht.1 (hg.function_l hX) hvw).mp hgx⟩, hvw⟩
  exact (rp_eq_member_l hU hAP ha).symm.trans (he.symm.trans (rp_eq_member_l hV hB spec))

end YesMetaZFC.SetTheory.Internal

/-! ## 全坐标代表赋值的源内真值集

内部程序只读取有限支撑，故源内逐点分离集也精确表示全坐标赋值下的
统一满足关系；分量映射可直接对这个实际集合应用测度协调律。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_full_trace_l {ω c X R D E z n F r a}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hz : Sformula_d I ω z n F r) (ha : M.mem a E) (hh : Pe_repr_d I ω D X R a) :
    ∃ A, M.mem A X ∧ ∀ v, M.mem v A ↔ M.mem v D ∧
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X R a f v ∧ Satisfies_d I ω c z f := by
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hz.2.1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  obtain ⟨A, hAX, hA⟩ := sc_pe_trace_l hZF hω hX hm theory hD hE hz.2.1 hz.2.2 hb hB ha
    (fun i g hi => hh i g (bω i hi))
  refine ⟨A, hAX, fun v => (hA v).trans (and_congr_right fun hv => ?_)⟩
  apply (pe_sat_full_l I hZF (rf_ext_mem_l I hZF.1 hX hm) hE hz.2.1 hB bω hz.2.2 ha hh (hX D hD v hv) ((hm.2 v D).mpr ⟨hX D hD v hv, hD, hv⟩)).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 hm.1 hz hE).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 分量超幂之间的完整初等映射

实际坐标图 t:D₁→D₀ 先诱导源中代表的复合，再下降为 [f]↦[f∘t]。
每个内部代码只在其内部有限支撑上提升代表。真值逆像沿 t 精确拉回，
测度协调与两边 Łoś 给出完整初等性；背景只需 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_projection_embedding_l {ω c X R D₀ D₁ P₀ P₁ U₀ U₁ t o₀ o₁ G₀ G₁ p₀ p₁ C₀ C₁ T₀ T₁}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform₀ : Sc_uniform_d I ω X R D₀) (uniform₁ : Sc_uniform_d I ω X R D₁) (hD₀ : M.mem D₀ X) (hD₁ : M.mem D₁ X) (htX : M.mem t X)
    (hP₀ : Source_d X D₀ P₀) (hP₁ : Source_d X D₁ P₁)
    (hU₀ : Rel_ultra_d D₀ P₀ U₀) (hU₁ : Rel_ultra_d D₁ P₁ U₁) (ht : Push_d D₀ D₁ P₀ P₁ U₀ U₁ t)
    (hG₀ : ∀ g, M.mem g G₀ ↔ M.mem g X ∧ Fn0_d D₀ X g)
    (hG₁ : ∀ g, M.mem g G₁ ↔ M.mem g X ∧ Fn0_d D₁ X g)
    (hM₀ : Rp_model_d I D₀ X U₀ R o₀ G₀ p₀ C₀ T₀) (hM₁ : Rp_model_d I D₁ X U₁ R o₁ G₁ p₁ C₁ T₁) :
    ∃ K j, M.IsSetFunctionFromTo I K G₀ G₁ ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d D₁ D₀ X t f g) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I K p₀ p₁ j := by
  have s₀ g (hg : M.mem g G₀) := sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm)
    ((hG₀ g).mp hg).1 ((hG₀ g).mp hg).2
  have s₁ g (hg : M.mem g G₁) := sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm)
    ((hG₁ g).mp hg).1 ((hG₁ g).mp hg).2
  obtain ⟨K, hK, hk⟩ := rs_pullback_family_l hZF hω hX hm theory hD₁ hD₀ htX ht.1 hG₀ hG₁
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU₀.base hU₁.base hM₀.map hM₁.map hK (fun f g f' g' hf hg =>
    rs_pullback_eq_l I hZF hω hX hm theory hD₀ hP₀ hU₀ hU₁ ht
      (s₀ f (hK.input_mem_of_pairMember hf)) (s₀ g (hK.input_mem_of_pairMember hg)) ((hk f f').mp hf).2.2 ((hk g g').mp hg).2.2)
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨K, j, hK, hk, ⟨hj, A, hA, fun z e₀ e₁ hz he₀ he₁ hh => ?_⟩, lift⟩
  obtain ⟨n, F, r, hcode⟩ := (hA z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω hcode.2.1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  obtain ⟨a₀, ha₀, finite⟩ := rp_finite_representatives_l I hZF hω hb hM₀.map he₀
  obtain ⟨u₀, hu₀, eval₀⟩ := smap_assign_exists_l I hZF hM₀.map.projection ha₀
  obtain ⟨u₁, hu₁, image⟩ := smap_assign_exists_l I hZF hj.1 hu₀
  -- 两端的新赋值只需在本公式的内部有限支撑上与原赋值一致。
  have agree {C f g} (hf : M.IsSetFunctionFromTo I f ω C) (hg : M.IsSetFunctionFromTo I g ω C)
      (forward : ∀ i x, M.mem i b → M.PairMember I i x f → M.PairMember I i x g) :
      Senv_agree_d I b f g := by
    intro i x hi
    refine ⟨forward i x hi, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := hf.2.2 i (bω i hi)
    exact hg.1.2 i y x (forward i y hi hy) hx ▸ hy
  have left := agree hu₀ he₀ (fun i B hi hiB => by
    obtain ⟨g, hg, hig⟩ := ha₀.2.2 i (bω i hi)
    obtain ⟨C, _, hgC⟩ := hM₀.map.projection.2.2 g hg
    exact hu₀.1.2 i C B (eval₀ i (bω i hi) g C hig hgC) hiB ▸ finite i hi g C hig hgC)
  have right := agree hu₁ he₁ (fun i C hi hiC => by
    obtain ⟨B, hB, hiB⟩ := hu₀.2.2 i (bω i hi)
    obtain ⟨D, _, hBD⟩ := hj.1.2.2 B hB
    exact hu₁.1.2 i D C (image i (bω i hi) B D hiB hBD) hiC ▸
      hh i (bω i hi) B D ((left i B hi).mp hiB) hBD)
  have truth {o C T f g} (model : Smdl_d I o C T)
      (hf : M.IsSetFunctionFromTo I f ω C) (hg : M.IsSetFunctionFromTo I g ω C)
      (same : Senv_agree_d I b f g) : Satisfies_d I ω o z f ↔ Satisfies_d I ω o z g := by
    obtain ⟨Q, hQ⟩ := ZF.exists_functionSpace hZF I ω C
    exact (satisfies_decode_l I hZF.1 model hcode hQ).trans
      ((ssat_agree_l I hZF hcode.2.1 bound hQ hcode.2.2 ((hQ f).mpr hf) ((hQ g).mpr hg) same).trans
        (satisfies_decode_l I hZF.1 model hcode hQ).symm)
  apply (truth hM₀.code hu₀ he₀ left).symm.trans
  apply Iff.trans ?_ (truth hM₁.code hu₁ he₁ right)
  obtain ⟨a₁, ha₁, comp⟩ := ZF.exists_compositionFunction hZF I ha₀ hK
  have a₀X : M.IsSetFunctionFromTo I a₀ ω X := ⟨ha₀.1, ha₀.2.1, fun i hi =>
    (ha₀.2.2 i hi).imp fun g hg => ⟨((hG₀ g).mp hg.1).1, hg.2⟩⟩
  have a₁X : M.IsSetFunctionFromTo I a₁ ω X := ⟨ha₁.1, ha₁.2.1, fun i hi =>
    (ha₁.2.2 i hi).imp fun g hg => ⟨((hG₁ g).mp hg.1).1, hg.2⟩⟩
  have r₀ : Rs_eval_d I ω D₀ X R p₀ a₀ u₀ := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := ha₀.2.2 i hi
    obtain ⟨B, _, hgp⟩ := hM₀.map.projection.2.2 g hg
    exact ⟨g, B, hig, (rf_fun_mem_l I hZF.1 hX hm hD₀).mpr (s₀ g hg), hgp, eval₀ i hi g B hig hgp⟩
  have r₁ : Rs_eval_d I ω D₁ X R p₁ a₁ u₁ := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := ha₀.2.2 i hi
    obtain ⟨B, _, hgp⟩ := hM₀.map.projection.2.2 g hg
    obtain ⟨g', hg', hgg⟩ := hK.2.2 g hg
    obtain ⟨C, _, hgp'⟩ := hM₁.map.projection.2.2 g' hg'
    exact ⟨g', C, (comp i g').mpr ⟨hi, g, hig, hgg⟩, (rf_fun_mem_l I hZF.1 hX hm hD₁).mpr (s₁ g' hg'), hgp',
      image i hi B C (eval₀ i hi g B hig hgp) (lift g g' B C hgg hgp hgp')⟩
  have point v w (hvw : Rd_entry_d v w t) f :
      Pe_assign_d I ω D₀ X R a₀ f w ↔ Pe_assign_d I ω D₁ X R a₁ f v := by
    constructor
    · intro h i hi
      obtain ⟨g, x, hig, _, hwx, hix⟩ := h i hi
      have hg := ha₀.output_mem_of_pairMember hig
      obtain ⟨g', hg', hgg⟩ := hK.2.2 g hg
      exact ⟨g', x, (comp i g').mpr ⟨hi, g, hig, hgg⟩, (rf_fun_mem_l I hZF.1 hX hm hD₁).mpr (s₁ g' hg'),
        (rf_val_mem_l I hZF.1 hX hm ((hG₁ g').mp hg').1).mpr
          ((((hk g g').mp hgg).2.2.value_l ht.1 ((hG₀ g).mp hg).2 hvw).mpr
            ((rf_val_mem_l I hZF.1 hX hm ((hG₀ g).mp hg).1).mp hwx)), hix⟩
    · intro h i hi
      obtain ⟨g', x, hig', _, hvx, hix⟩ := h i hi
      obtain ⟨g, hg, hig⟩ := ha₀.2.2 i hi
      obtain ⟨g'', hg'', hgg⟩ := hK.2.2 g hg
      have eq := ha₁.1.2 i g' g'' hig' ((comp i g'').mpr ⟨hi, g, hig, hgg⟩)
      exact ⟨g, x, hig, (rf_fun_mem_l I hZF.1 hX hm hD₀).mpr (s₀ g hg), (rf_val_mem_l I hZF.1 hX hm ((hG₀ g).mp hg).1).mpr
        ((((hk g g'').mp hgg).2.2.value_l ht.1 ((hG₀ g).mp hg).2 hvw).mp
          ((rf_val_mem_l I hZF.1 hX hm ((hG₁ g'').mp hg'').1).mp (eq ▸ hvx))), hix⟩
  obtain ⟨B, hBX, hB⟩ := sc_full_trace_l hZF hω hX hm theory hD₀ hE hcode
    ((hE a₀).mpr a₀X) (r₀.repr_l I ha₀.1)
  have hBP := (hP₀ B).mpr ⟨hBX, fun v hv => ((hB v).mp hv).1⟩
  obtain ⟨C, hCQ, hC, measure⟩ := ht.2 B hBP
  have trace v : M.mem v C ↔ M.mem v D₁ ∧
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D₁ X R a₁ f v ∧ Satisfies_d I ω c z f := by
    refine (hC v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, w, hw, hvw⟩
      obtain ⟨_, f, hf, hval, hs⟩ := (hB w).mp hw
      exact ⟨hv, f, hf, (point v w hvw f).mp hval, hs⟩
    · rintro ⟨hv, f, hf, hval, hs⟩
      obtain ⟨w, hw, hvw⟩ := ht.1.2.1 v hv
      exact ⟨hv, w, (hB w).mpr ⟨hw, f, hf, (point v w hvw f).mpr hval, hs⟩, hvw⟩
  have read {D P U A : M.Domain} (hU : Rel_ultra_d D P U) (hAP : M.mem A P) (ψ : M.Domain → Prop)
      (hA : ∀ v, M.mem v A ↔ M.mem v D ∧ ψ v) : M.mem A U ↔ ∃ B, M.mem B U ∧ ∀ v, M.mem v B → ψ v := by
    refine ⟨fun h => ⟨A, h, fun v hv => ((hA v).mp hv).2⟩, ?_⟩
    rintro ⟨B, hB, hb⟩
    exact hU.upward B A hB hAP (fun v hv => (hA v).mpr ⟨hU.base.bounds B hB v hv, hb v hv⟩)
  have los₀ := rs_satisfies_l hZF hω hX hm theory uniform₀ hD₀ hP₀ hU₀ hG₀ hM₀ hE hA ((hE a₀).mpr a₀X) hu₀ r₀ hz
  have los₁ := rs_satisfies_l hZF hω hX hm theory uniform₁ hD₁ hP₁ hU₁ hG₁ hM₁ hE hA ((hE a₁).mpr a₁X) hu₁ r₁ hz
  exact los₀.trans ((read hU₀ hBP _ hB).symm.trans (measure.symm.trans ((read hU₁ hCQ _ trace).trans los₁.symm)))

end YesMetaZFC.SetTheory.Internal
