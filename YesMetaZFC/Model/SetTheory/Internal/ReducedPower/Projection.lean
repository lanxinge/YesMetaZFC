import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Lift
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceComposition
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.PullbackKernel
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceTrace
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction

/-! # 分量超幂之间的完整初等映射

实际坐标图 t:D₁→D₀ 先诱导源中代表的复合，再下降为 [f]↦[f∘t]。
任意内部代码的真值逆像沿 t 精确拉回，测度协调与两边 Łoś 给出完整初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_projection_embedding_l {ω c X R D₀ D₁ P₀ P₁ U₀ U₁ t o₀ o₁ G₀ G₁ p₀ p₁ C₀ C₁ T₀ T₁}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (u₀ : Sc_uniform_d I ω X R D₀) (u₁ : Sc_uniform_d I ω X R D₁) (hD₀ : M.mem D₀ X) (hD₁ : M.mem D₁ X) (htX : M.mem t X)
    (hP₀ : Source_d X D₀ P₀) (hP₁ : Source_d X D₁ P₁)
    (hU₀ : Rel_ultra_d D₀ P₀ U₀) (hU₁ : Rel_ultra_d D₁ P₁ U₁) (ht : Push_d D₀ D₁ P₀ P₁ U₀ U₁ t)
    (hG₀ : ∀ g, M.mem g G₀ ↔ M.mem g X ∧ Fn0_d D₀ X g)
    (hG₁ : ∀ g, M.mem g G₁ ↔ M.mem g X ∧ Fn0_d D₁ X g)
    (hM₀ : Rp_model_d I D₀ X U₀ R o₀ G₀ p₀ C₀ T₀) (hM₁ : Rp_model_d I D₁ X U₁ R o₁ G₁ p₁ C₁ T₁) :
    ∃ K j, M.IsSetFunctionFromTo I K G₀ G₁ ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d D₁ D₀ X t f g) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I K p₀ p₁ j := by
  have s₀ g (hg : M.mem g G₀) := sc_function_domain_l theory.algebra
    ((hG₀ g).mp hg).1 ((hG₀ g).mp hg).2
  have s₁ g (hg : M.mem g G₁) := sc_function_domain_l theory.algebra
    ((hG₁ g).mp hg).1 ((hG₁ g).mp hg).2
  obtain ⟨K, hK, hk⟩ := rs_pullback_family_l hZF hω hX hm theory hD₁ hD₀ htX ht.1 hG₀ hG₁
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU₀.base hU₁.base hM₀.map hM₁.map hK (fun f g f' g' hf hg =>
    rs_pullback_eq_l I hZF hω hX hm theory hD₀ hP₀ hU₀ hU₁ ht
      (s₀ f (hK.input_mem_of_pairMember hf)) (s₀ g (hK.input_mem_of_pairMember hg)) ((hk f f').mp hf).2.2 ((hk g g').mp hg).2.2)
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨K, j, hK, hk, ⟨hj, A, hA, fun z e₀ e₁ hz he₀ he₁ hh => ?_⟩, lift⟩
  obtain ⟨a₀, ha₀, eval₀⟩ := rp_representatives_l I hZFC hM₀.map he₀
  obtain ⟨a₁, ha₁, comp⟩ := ZF.exists_compositionFunction hZF I ha₀ hK
  have a₀X : M.IsSetFunctionFromTo I a₀ ω X := ⟨ha₀.1, ha₀.2.1, fun i hi =>
    (ha₀.2.2 i hi).imp fun g hg => ⟨((hG₀ g).mp hg.1).1, hg.2⟩⟩
  have a₁X : M.IsSetFunctionFromTo I a₁ ω X := ⟨ha₁.1, ha₁.2.1, fun i hi =>
    (ha₁.2.2 i hi).imp fun g hg => ⟨((hG₁ g).mp hg.1).1, hg.2⟩⟩
  have r₀ : Rs_eval_d I ω D₀ X R p₀ a₀ e₀ := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := ha₀.2.2 i hi
    obtain ⟨B, _, hgp⟩ := hM₀.map.projection.2.2 g hg
    exact ⟨g, B, hig, (rf_fun_mem_l I hZF.1 hX hm hD₀).mpr (s₀ g hg), hgp, eval₀ i hi g B hig hgp⟩
  have r₁ : Rs_eval_d I ω D₁ X R p₁ a₁ e₁ := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := ha₀.2.2 i hi
    obtain ⟨B, _, hgp⟩ := hM₀.map.projection.2.2 g hg
    obtain ⟨g', hg', hgg⟩ := hK.2.2 g hg
    obtain ⟨C, _, hgp'⟩ := hM₁.map.projection.2.2 g' hg'
    exact ⟨g', C, (comp i g').mpr ⟨hi, g, hig, hgg⟩, (rf_fun_mem_l I hZF.1 hX hm hD₁).mpr (s₁ g' hg'), hgp',
      hh i hi B C (eval₀ i hi g B hig hgp) (lift g g' B C hgg hgp hgp')⟩
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
  obtain ⟨n, F, r, hcode⟩ := (hA z).mp hz
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
  have los₀ := rs_satisfies_l hZF hω hX hm theory u₀ hD₀ hP₀ hU₀ hG₀ hM₀ hE hA ((hE a₀).mpr a₀X) he₀ r₀ hz
  have los₁ := rs_satisfies_l hZF hω hX hm theory u₁ hD₁ hP₁ hU₁ hG₁ hM₁ hE hA ((hE a₁).mpr a₁X) he₁ r₁ hz
  exact los₀.trans ((read hU₀ hBP _ hB).symm.trans (measure.symm.trans ((read hU₁ hCQ _ trace).trans los₁.symm)))

end YesMetaZFC.SetTheory.Internal
