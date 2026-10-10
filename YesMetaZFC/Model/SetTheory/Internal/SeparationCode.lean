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

/-- 检查指定 A 的分离方程；A、D 是赋值中的参数。 -/
theorem sfm_sep_test_l (hZF : M.Models ZF) {ω n F r i s t} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D A,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → M.PairMember I t A f →
      (Ssat_d I X R E G m k f ↔ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hi hs
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, h₃, a₃⟩ := sfm_rel_l I hZF hω h₂.program hi ht
  obtain ⟨n₄, F₄, r₄, h₄, a₄⟩ := sfm_iff_l I hZF hω h₃.program h₃.root (h₃.span r₂ h₂.root)
  obtain ⟨m, G, k, h₅, a₅⟩ := sfm_all_l I hZF hω h₄.program hi h₄.root
  refine ⟨m, G, k, (((h₁.comp I h₂).comp I h₃).comp I h₄).comp I h₅,
    fun X R E c f D A hX hm hE hf hD hA => ?_⟩
  have hDX := ((hE f).mp hf).output_mem_of_pairMember hD
  have hAX := ((hE f).mp hf).output_mem_of_pairMember hA
  have read x v (hx : M.mem x X) (hv : Senv_update_d I f i x v) :
      Ssat_d I X R E F₄ n₄ r₄ v ↔ (M.mem x A ↔ M.mem x D ∧
        ∃ w, Senv_update_d I f i x w ∧ Ssat_d I X R E F n r w) := by
    have hve := (hE v).mpr (hv.function_l I ((hE f).mp hf) hi hx)
    rw [a₄ X R E v hve, a₃ X R E v x A hE hve
      ((hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)) ((hv.2 t A).mpr (Or.inr ⟨hti, hA⟩)),
      ← h₃.sat_l I hZF h₂.program h₂.root X R E v, a₂ X R E v hve,
      a₁ X R E v x D hE hve ((hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
        ((hv.2 s D).mpr (Or.inr ⟨hsi, hD⟩)), ← h₁.sat_l I hZF hF hr X R E v]
    have memA := (hm.2 x A).trans (show (M.mem x X ∧ M.mem A X ∧ M.mem x A) ↔ M.mem x A from
      ⟨fun h => h.2.2, fun h => ⟨hx, hAX, h⟩⟩)
    have memD := (hm.2 x D).trans (show (M.mem x X ∧ M.mem D X ∧ M.mem x D) ↔ M.mem x D from
      ⟨fun h => h.2.2, fun h => ⟨hx, hDX, h⟩⟩)
    exact iff_congr memA (and_congr Iff.rfl ⟨fun h => ⟨v, hv, h⟩,
      fun ⟨w, hw, h⟩ => senv_update_unique_l I hZF.1 hw hv ▸ h⟩) |>.trans (iff_congr Iff.rfl (and_congr memD Iff.rfl))
  rw [a₅ X R E f hE hf]
  constructor
  · intro h x
    by_cases hx : M.mem x X
    · obtain ⟨v, hv, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
      exact (read x v hx hv).mp (h x v hx hv)
    · exact iff_of_false (fun h => hx (hX A hAX x h)) (fun h => hx (hX D hDX x h.1))
  · exact fun h x v hx hv => (read x v hx hv).mpr (h x)

theorem sfm_sep_l (hZF : M.Models ZF) {ω n F r i s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) (hst : s ≠ t) (hb : Sbound_d I F b) (htb : ¬ M.mem t b) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → (Ssat_d I X R E G m k f ↔ ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨v, J, u, h, test⟩ := sfm_sep_test_l I hZF hω hF hr hi hs ht hsi hti
  obtain ⟨m, G, k, build, read⟩ := sfm_ex_l I hZF hω h.program ht h.root
  refine ⟨m, G, k, h.comp I build, fun X R E c f D hX hm hE hf hD => ?_⟩
  have body A g (hA : M.mem A X) (hu : Senv_update_d I f t A g) :
      Ssat_d I X R E J v u g ↔ Ssep_d I X R E F n r i f D A := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) ht hA)
    exact (test X R E c g D A hX hm hE hg ((hu.2 s D).mpr (Or.inr ⟨hst, hD⟩))
      ((hu.2 t A).mpr (Or.inl ⟨rfl, rfl⟩))).trans
      (ssep_agree_l I hZF hF hb hr hi hE hf hg (hu.agree_l I htb)
        (hX D (((hE f).mp hf).output_mem_of_pairMember hD))).symm
  rw [read X R E f hf]
  constructor
  · exact fun ⟨A, g, hA, hu, hh⟩ => ⟨A, hA, (body A g hA hu).mp hh⟩
  · rintro ⟨A, hA, hh⟩
    obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht hA
    exact ⟨A, g, hA, hu, (body A g hA hu).mpr hh⟩

end YesMetaZFC.SetTheory.Internal
