import YesMetaZFC.Model.SetTheory.Internal.Builder
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 任意内部公式的分离实例代码

给原程序追加 x∈A ↔ (x∈D ∧ φ)，再量化 x 和 A。A 使用真实支撑外坐标，
有限支撑真值定理保证这一新参数不捕获原公式；最后的规格是实际集合的成员方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ssep_d (X R E F n r i f D A : M.Domain) : Prop := ∀ x, M.mem x A ↔ M.mem x D ∧
  ∃ g, Senv_update_d I f i x g ∧ Ssat_d I X R E F n r g

theorem ssep_agree_l (hZF : M.Models ZF) {ω X R E F n r i f g b D A}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n) (hi : M.mem i ω)
    (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E) (hg : M.mem g E)
    (ha : Senv_agree_d I b f g) (hD : M.MemberSubset D X) :
    Ssep_d I X R E F n r i f D A ↔ Ssep_d I X R E F n r i g D A := by
  have transfer {f g} (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g)
      x (hx : M.mem x D) : (∃ v, Senv_update_d I f i x v ∧ Ssat_d I X R E F n r v) →
        ∃ w, Senv_update_d I g i x w ∧ Ssat_d I X R E F n r w := by
    rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw, hwE⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi (hD x hx)
    exact ⟨w, hw, (ssat_agree_l I hZF hF hb hE hr
      ((hE v).mpr (hv.function_l I ((hE f).mp hf) hi (hD x hx))) ((hE w).mpr hwE)
      (ha.update_l I hv hw)).mp ht⟩
  exact forall_congr' fun x => iff_congr Iff.rfl (and_congr_right fun hx =>
    ⟨transfer hf hg ha x hx, transfer hg hf (ha.symm_l I) x hx⟩)

theorem sfm_sep_l (hZF : M.Models ZF) {ω n F r i s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) (hst : s ≠ t) (hb : Sbound_d I F b) (htb : ¬ M.mem t b) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → (Ssat_d I X R E G m k f ↔ ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hi hs
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, h₃, a₃⟩ := sfm_rel_l I hZF hω h₂.program hi ht
  obtain ⟨n₄, F₄, r₄, h₄, a₄⟩ := sfm_iff_l I hZF hω h₃.program h₃.root (h₃.span r₂ h₂.root)
  obtain ⟨n₅, F₅, r₅, h₅, a₅⟩ := sfm_all_l I hZF hω h₄.program hi h₄.root
  obtain ⟨m, G, k, h₆, a₆⟩ := sfm_ex_l I hZF hω h₅.program ht h₅.root
  refine ⟨m, G, k, ((((h₁.comp I h₂).comp I h₃).comp I h₄).comp I h₅).comp I h₆,
    fun X R E c f D hX hm hE hf hD => ?_⟩
  have hDX := ((hE f).mp hf).output_mem_of_pairMember hD
  have matrix v x A (hv : M.mem v E) (hix : M.PairMember I i x v)
      (hsD : M.PairMember I s D v) (htA : M.PairMember I t A v) :
      Ssat_d I X R E F₄ n₄ r₄ v ↔ (M.PairMember I x A R ↔
        M.PairMember I x D R ∧ Ssat_d I X R E F n r v) := by
    rw [a₄ X R E v hv, a₃ X R E v x A hE hv hix htA,
      ← h₃.sat_l I hZF h₂.program h₂.root X R E v, a₂ X R E v hv,
      a₁ X R E v x D hE hv hix hsD, ← h₁.sat_l I hZF hF hr X R E v]
  have body A g (hAX : M.mem A X) (hu : Senv_update_d I f t A g) :
      Ssat_d I X R E F₅ n₅ r₅ g ↔ Ssep_d I X R E F n r i f D A := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) ht hAX)
    have value x v (hx : M.mem x X) (hv : Senv_update_d I g i x v) :
        (∃ w, Senv_update_d I f i x w ∧ Ssat_d I X R E F n r w) ↔ Ssat_d I X R E F n r v := by
      have compare w (hw : Senv_update_d I f i x w) :
          Ssat_d I X R E F n r w ↔ Ssat_d I X R E F n r v :=
        ssat_agree_l I hZF hF hb hE hr ((hE w).mpr (hw.function_l I ((hE f).mp hf) hi hx))
          ((hE v).mpr (hv.function_l I ((hE g).mp hg) hi hx)) ((hu.agree_l I htb).update_l I hw hv)
      refine ⟨fun ⟨w, hw, hh⟩ => (compare w hw).mp hh, fun hh => ?_⟩
      obtain ⟨w, hw, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
      exact ⟨w, hw, (compare w hw).mpr hh⟩
    have read x v (hx : M.mem x X) (hv : Senv_update_d I g i x v) :
        Ssat_d I X R E F₄ n₄ r₄ v ↔ (M.mem x A ↔ M.mem x D ∧
          ∃ w, Senv_update_d I f i x w ∧ Ssat_d I X R E F n r w) := by
      have hvφ := matrix v x A ((hE v).mpr (hv.function_l I ((hE g).mp hg) hi hx))
        ((hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
        ((hv.2 s D).mpr (Or.inr ⟨hsi, (hu.2 s D).mpr (Or.inr ⟨hst, hD⟩)⟩))
        ((hv.2 t A).mpr (Or.inr ⟨hti, (hu.2 t A).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      have memA : M.PairMember I x A R ↔ M.mem x A := (hm.2 x A).trans
        ⟨fun h => h.2.2, fun h => ⟨hx, hAX, h⟩⟩
      have memD : M.PairMember I x D R ↔ M.mem x D := (hm.2 x D).trans
        ⟨fun h => h.2.2, fun h => ⟨hx, hDX, h⟩⟩
      exact hvφ.trans (iff_congr memA (and_congr memD (value x v hx hv).symm))
    rw [a₅ X R E g hE hg]
    constructor
    · intro hh x
      by_cases hx : M.mem x X
      · obtain ⟨v, hv, _⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
        exact (read x v hx hv).mp (hh x v hx hv)
      · exact iff_of_false (fun h => hx (hX A hAX x h)) (fun h => hx (hX D hDX x h.1))
    · exact fun hh x v hx hv => (read x v hx hv).mpr (hh x)
  rw [a₆ X R E f hf]
  constructor
  · exact fun ⟨A, g, ha, hu, hh⟩ => ⟨A, ha, (body A g ha hu).mp hh⟩
  · rintro ⟨A, ha, hh⟩
    obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht ha
    exact ⟨A, g, ha, hu, (body A g ha hu).mpr hh⟩

end YesMetaZFC.SetTheory.Internal
