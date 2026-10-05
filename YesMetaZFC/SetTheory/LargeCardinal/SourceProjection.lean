import YesMetaZFC.SetTheory.LargeCardinal.Coherence
import YesMetaZFC.Model.SetTheory.Internal.SourceField
import YesMetaZFC.Model.SetTheory.Internal.SourceReindex
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.ProjectionLaws

/-! # 有限支撑测度的源内分量与初等交换图

把已经构造的有限支撑协调律限制到实际源子集代数，自动构造坐标投影、
两侧源内部超幂、常值嵌入及分量间初等映射。全部集合和函数图均实际生成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel FilterZF
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_source_push_l {ω c X R κ L F m n q a b U V D E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X)
    (hDX : M.mem D X) (hEX : M.mem E X) (hmω : M.mem m ω) (hnω : M.mem n ω)
    (hq : Fn0_d m n q) (ha : Fn0_d n L a) (hb : Cp0_d m n L q a b)
    (haV : M.PairMember I a V F) (hbU : M.PairMember I b U F) (hc : Es_coherent_d I ω κ L F)
    (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s)
    (hU : Maximal_d (ℳ := M) D U) (hV : Maximal_d (ℳ := M) E V) : ∃ P Q U' V' t,
      Source_d X D P ∧ Source_d X E Q ∧ Rel_ultra_d D P U' ∧ Rel_ultra_d E Q V' ∧
      (∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) ∧ (∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V) ∧ M.mem t X ∧
      (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧ Push_d D E P Q U' V' t := by
  obtain ⟨t, htX, ht, spec⟩ := sc_reindex_l hZF hω hX hm theory hmX hnX hκX hqX hEX hq hD hE
  obtain ⟨P, U', hP, hU', hu⟩ := sc_source_ultrafilter_l I hZF hω hX hm theory hDX (hU.source_l hZF X)
  obtain ⟨Q, V', hQ, hV', hv⟩ := sc_source_ultrafilter_l I hZF hω hX hm theory hEX (hV.source_l hZF X)
  refine ⟨P, Q, U', V', t, hP, hQ, hU', hV', hu, hv, htX, spec, ht, fun A hA => ?_⟩
  obtain ⟨B, hBX, hB⟩ := sc_pull_l I hZF hω hX hm theory hEX htX ((hP A).mp hA).1
  have hBQ := (hQ B).mpr ⟨hBX, fun v hv => ((hB v).mp hv).1⟩
  obtain ⟨Z, hZ, hz⟩ := hc m n q a b U V A hmω hnω hq ha hb haV hbU
    (fun r hr => (hD r).mp (((hP A).mp hA).2 r hr))
  have eq : Z = B := by
    apply hZF.1.eq_of_same_members Z B
    intro s
    rw [hZ s, hB s]
    constructor
    · rintro ⟨hs, r, hr, hsρ⟩
      exact ⟨(hE s).mpr hs, r, hr, (spec s r).mpr ⟨(hE s).mpr hs, hsρ⟩⟩
    · rintro ⟨hs, r, hr, hsr⟩
      exact ⟨(hE s).mp hs, r, hr, ((spec s r).mp hsr).2⟩
  have readU : M.mem A U' ↔ M.mem A U := (hu A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩
  have readV : M.mem B V' ↔ M.mem B V := (hv B).trans ⟨And.right, fun h => ⟨hBQ, h⟩⟩
  exact ⟨B, hBQ, hB, readV.trans ((eq ▸ hz).trans readU.symm)⟩

end
section
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从真实有限支撑分量一次构造两侧超幂与三个初等映射，并给出交换方程。 -/
theorem es_source_projection_l {ω c X R κ L F m n q a b U V D E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (u₀ : Sc_uniform_d I ω X R D) (u₁ : Sc_uniform_d I ω X R E)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X)
    (hDX : M.mem D X) (hEX : M.mem E X) (hmω : M.mem m ω) (hnω : M.mem n ω)
    (hq : Fn0_d m n q) (ha : Fn0_d n L a) (hb : Cp0_d m n L q a b)
    (haV : M.PairMember I a V F) (hbU : M.PairMember I b U F) (hc : Es_coherent_d I ω κ L F)
    (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s)
    (hU : Maximal_d (ℳ := M) D U) (hV : Maximal_d (ℳ := M) E V) :
    ∃ P Q U' V' t G₀ G₁ o₀ o₁ p₀ p₁ C₀ C₁ T₀ T₁ i₀ i₁ K j,
      Source_d X D P ∧ Source_d X E Q ∧ Rel_ultra_d D P U' ∧ Rel_ultra_d E Q V' ∧
      (∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) ∧ (∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V) ∧
      M.mem t X ∧ Push_d D E P Q U' V' t ∧ (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧
      (∀ f, M.mem f G₀ ↔ M.mem f X ∧ Fn0_d D X f) ∧ (∀ f, M.mem f G₁ ↔ M.mem f X ∧ Fn0_d E X f) ∧
      Rp_model_d I D X U' R o₀ G₀ p₀ C₀ T₀ ∧ Rp_model_d I E X V' R o₁ G₁ p₁ C₁ T₁ ∧
      Smap_d I ω c o₀ X C₀ i₀ ∧ Smap_d I ω c o₁ X C₁ i₁ ∧ Smap_d I ω o₀ o₁ C₀ C₁ j ∧
      (∀ x B, M.PairMember I x B i₀ ↔ M.mem x X ∧ ∃ f, M.mem f G₀ ∧ Rs_const_d D x f ∧ M.PairMember I f B p₀) ∧
      (∀ x B, M.PairMember I x B i₁ ↔ M.mem x X ∧ ∃ f, M.mem f G₁ ∧ Rs_const_d E x f ∧ M.PairMember I f B p₁) ∧
      M.IsSetFunctionFromTo I K G₀ G₁ ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d E D X t f g) ∧ Rp_lift_d I K p₀ p₁ j ∧
      ∀ x B A, M.PairMember I x B i₀ → (M.PairMember I B A j ↔ M.PairMember I x A i₁) := by
  obtain ⟨P, Q, U', V', t, hP, hQ, hU', hV', hu, hv, htX, coord, ht⟩ := es_source_push_l hZF hω hX hm theory
    hmX hnX hκX hqX hDX hEX hmω hnω hq ha hb haV hbU hc hD hE hU hV
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF hω hX hm theory hDX hDX
  obtain ⟨G₀, o₀, p₀, C₀, T₀, hG₀, hM₀⟩ := rp_family_model_l I hZF hU'.base hfX (hf.mono_target_l (hX A hAX)) R
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF hω hX hm theory hEX hDX
  obtain ⟨G₁, o₁, p₁, C₁, T₁, hG₁, hM₁⟩ := rp_family_model_l I hZF hV'.base hfX (hf.mono_target_l (hX A hAX)) R
  obtain ⟨K, j, hK, hk, hj, hl⟩ := rs_projection_embedding_l hZFC hω hX hm theory u₀ u₁
    hDX hEX htX hP hQ hU' hV' ht hG₀ hG₁ hM₀ hM₁
  obtain ⟨i₀, hi₀, h₀⟩ := rs_constant_embedding_l hZF hω hX hm theory u₀ hDX hP hU' hG₀ hM₀
  obtain ⟨i₁, hi₁, h₁⟩ := rs_constant_embedding_l hZF hω hX hm theory u₁ hEX hQ hV' hG₁ hM₁
  exact ⟨P, Q, U', V', t, G₀, G₁, o₀, o₁, p₀, p₁, C₀, C₁, T₀, T₁, i₀, i₁, K, j,
    hP, hQ, hU', hV', hu, hv, htX, ht, coord, hG₀, hG₁, hM₀, hM₁, hi₀, hi₁, hj, h₀, h₁, hK, hk, hl,
    rs_projection_constant_l I hM₀.map hM₁.map ht.1 hK (fun f g h => ((hk f g).mp h).2.2)
      hj.1.1 hl hi₁.1.1 h₀ h₁⟩

end
end YesMetaZFC.SetTheory.LargeCardinal
