import YesMetaZFC.Model.SetTheory.ReducedPower.Projection
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize

/-! # 分量映射的恒等、复合及常值交换律

证明只读取实际图的代表方程与商投影，不重新选择商代表。坐标复合的结合律
在代表层成立后，函数图单值性将它下降到全部等价类。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rs_projection_id_l {D X U G p C K j t}
    (hp : Rp_map_d I D X U G p C) (hj : M.IsSetFunctionFromTo I j C C)
    (ht : ∀ v w, Rd_entry_d v w t ↔ M.mem v D ∧ v = w)
    (hK : ∀ f g, M.PairMember I f g K ↔ M.mem f G ∧ M.mem g G ∧ Cp0_d D D X t f g)
    (hl : Rp_lift_d I K p p j) : ∀ B A, M.PairMember I B A j ↔ M.mem B C ∧ B = A := by
  have fixed B (hB : M.mem B C) : M.PairMember I B B j := by
    obtain ⟨f, hf⟩ := (hp.range B).mp hB
    have hfG := hp.projection.input_mem_of_pairMember hf
    have hF := hp.functions f hfG
    have hcp : Cp0_d D D X t f f := ⟨hF, fun v hv => by
      obtain ⟨x, hx, hvx⟩ := hF.2.1 v hv
      exact ⟨v, hv, x, hx, (ht v v).mpr ⟨hv, rfl⟩, hvx, hvx⟩⟩
    exact hl f f B B ((hK f f).mpr ⟨hfG, hfG, hcp⟩) hf hf
  exact fun B A => ⟨fun h => ⟨hj.input_mem_of_pairMember h,
    hj.1.2 B B A (fixed B (hj.input_mem_of_pairMember h)) h⟩, fun ⟨hB, he⟩ => he ▸ fixed B hB⟩

theorem rs_projection_comp_l {D₀ D₁ D₂ X U₀ U₁ U₂ G₀ G₁ G₂ p₀ p₁ p₂ C₀ C₁ C₂ K₀₁ K₁₂ K₀₂ j₀₁ j₁₂ j₀₂ t s u}
    (hp₀ : Rp_map_d I D₀ X U₀ G₀ p₀ C₀) (hp₁ : Rp_map_d I D₁ X U₁ G₁ p₁ C₁) (hp₂ : Rp_map_d I D₂ X U₂ G₂ p₂ C₂)
    (ht : Fn0_d D₁ D₀ t) (hs : Fn0_d D₂ D₁ s) (hu : Cp0_d D₂ D₁ D₀ s t u)
    (hK₀₁ : M.IsSetFunctionFromTo I K₀₁ G₀ G₁) (hK₁₂ : M.IsSetFunctionFromTo I K₁₂ G₁ G₂)
    (k₀₁ : ∀ f g, M.PairMember I f g K₀₁ → Cp0_d D₁ D₀ X t f g)
    (k₁₂ : ∀ f g, M.PairMember I f g K₁₂ → Cp0_d D₂ D₁ X s f g)
    (k₀₂ : ∀ f g, M.mem f G₀ → M.mem g G₂ → Cp0_d D₂ D₀ X u f g → M.PairMember I f g K₀₂)
    (hj₀₁ : M.IsSetFunctionFromTo I j₀₁ C₀ C₁) (hj₁₂ : M.IsSetFunctionFromTo I j₁₂ C₁ C₂)
    (hj₀₂ : M.IsSetFunctionFromTo I j₀₂ C₀ C₂)
    (l₀₁ : Rp_lift_d I K₀₁ p₀ p₁ j₀₁) (l₁₂ : Rp_lift_d I K₁₂ p₁ p₂ j₁₂) (l₀₂ : Rp_lift_d I K₀₂ p₀ p₂ j₀₂) :
    ∀ B C, M.PairMember I B C j₀₂ ↔ M.mem B C₀ ∧ ∃ A, M.PairMember I B A j₀₁ ∧ M.PairMember I A C j₁₂ := by
  have triangle B (hB : M.mem B C₀) : ∃ A C,
      M.PairMember I B A j₀₁ ∧ M.PairMember I A C j₁₂ ∧ M.PairMember I B C j₀₂ := by
    obtain ⟨f, hf⟩ := (hp₀.range B).mp hB
    have hfG := hp₀.projection.input_mem_of_pairMember hf
    obtain ⟨g, hg, hfg⟩ := hK₀₁.2.2 f hfG
    obtain ⟨h, hh, hgh⟩ := hK₁₂.2.2 g hg
    obtain ⟨A, _, hgp⟩ := hp₁.projection.2.2 g hg
    obtain ⟨C, _, hhp⟩ := hp₂.projection.2.2 h hh
    have hfh := k₀₂ f h hfG hh (Cp0_d.assoc_l ht hs hu (hp₀.functions f hfG) (k₀₁ f g hfg) (k₁₂ g h hgh))
    exact ⟨A, C, l₀₁ f g B A hfg hf hgp, l₁₂ g h A C hgh hgp hhp, l₀₂ f h B C hfh hf hhp⟩
  intro B C
  constructor
  · intro h
    have hB := hj₀₂.input_mem_of_pairMember h
    obtain ⟨A, C', hBA, hAC, hBC⟩ := triangle B hB
    exact ⟨hB, A, hBA, hj₀₂.1.2 B C' C hBC h ▸ hAC⟩
  · rintro ⟨hB, A, hBA, hAC⟩
    obtain ⟨A', C', hBA', hAC', hBC'⟩ := triangle B hB
    have ea := hj₀₁.1.2 B A' A hBA' hBA
    exact hj₁₂.1.2 A C' C (ea ▸ hAC') hAC ▸ hBC'

theorem rs_projection_constant_l {D E X U V F G p q C N K j i₀ i₁ t}
    (hp : Rp_map_d I D X U F p C) (hq : Rp_map_d I E X V G q N)
    (ht : Fn0_d E D t) (hK : M.IsSetFunctionFromTo I K F G)
    (hk : ∀ f g, M.PairMember I f g K → Cp0_d E D X t f g)
    (hj : M.IsSetFunctionFromTo I j C N) (hl : Rp_lift_d I K p q j)
    (hi₁ : M.IsSetFunctionFromTo I i₁ X N)
    (h₀ : ∀ x B, M.PairMember I x B i₀ ↔ M.mem x X ∧ ∃ f, M.mem f F ∧ Rs_const_d D x f ∧ M.PairMember I f B p)
    (h₁ : ∀ x B, M.PairMember I x B i₁ ↔ M.mem x X ∧ ∃ f, M.mem f G ∧ Rs_const_d E x f ∧ M.PairMember I f B q) :
    ∀ x B A, M.PairMember I x B i₀ → (M.PairMember I B A j ↔ M.PairMember I x A i₁) := by
  intro x B A hxB
  obtain ⟨hx, f, hf, hconst, hfp⟩ := (h₀ x B).mp hxB
  obtain ⟨g, hg, hfg⟩ := hK.2.2 f hf
  obtain ⟨C, _, hgq⟩ := hq.projection.2.2 g hg
  have constant : Rs_const_d E x g := fun v hv => by
    obtain ⟨w, hw, hvw⟩ := ht.2.1 v hv
    exact ((hk f g hfg).value_l ht (hp.functions f hf) hvw).mpr (hconst w hw)
  have hxC := (h₁ x C).mpr ⟨hx, g, hg, constant, hgq⟩
  have hBC := hl f g B C hfg hfp hgq
  exact ⟨fun hBA => hj.1.2 B C A hBC hBA ▸ hxC, fun hxA => hi₁.1.2 x C A hxC hxA ▸ hBC⟩

end YesMetaZFC.SetTheory.Internal
