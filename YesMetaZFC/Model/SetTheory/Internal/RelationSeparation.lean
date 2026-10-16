import YesMetaZFC.Model.SetTheory.Internal.Builder
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 原关系模型中的全内部分离程序

分离集按原关系读取其成员，原公式仍由同一个内部程序解释。
全称量词只遍历载体；不把目标对象误读成背景集合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_sep_d (X R E F n r i f D A : M.Domain) : Prop := ∀ x, M.mem x X →
  (M.PairMember I x A R ↔ M.PairMember I x D R ∧ ∃ g, Senv_update_d I f i x g ∧ Ssat_d I X R E F n r g)

theorem sr_sep_agree_l (hZF : M.Models ZF) {ω X R E F n r i f g b D A}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n) (hi : M.mem i ω)
    (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) :
    Sr_sep_d I X R E F n r i f D A ↔ Sr_sep_d I X R E F n r i g D A := by
  have transfer {f g} (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) x (hx : M.mem x X) :
      (∃ v, Senv_update_d I f i x v ∧ Ssat_d I X R E F n r v) →
        ∃ w, Senv_update_d I g i x w ∧ Ssat_d I X R E F n r w := by
    rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw, hwE⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
    exact ⟨w, hw, (ssat_agree_l I hZF hF hb hE hr
      ((hE v).mpr (hv.function_l I ((hE f).mp hf) hi hx)) ((hE w).mpr hwE) (ha.update_l I hv hw)).mp ht⟩
  exact forall_congr' fun x => imp_congr_right fun hx => iff_congr Iff.rfl (and_congr Iff.rfl
    ⟨transfer hf hg ha x hx, transfer hg hf (ha.symm_l I) x hx⟩)

theorem sfm_sep_test_raw_l (hZF : M.Models ZF) {ω n F r i s t} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E f D A,
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f → M.PairMember I t A f →
      (Ssat_d I X R E G m k f ↔ Sr_sep_d I X R E F n r i f D A) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hi hs
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, h₃, a₃⟩ := sfm_rel_l I hZF hω h₂.program hi ht
  obtain ⟨n₄, F₄, r₄, h₄, a₄⟩ := sfm_iff_l I hZF hω h₃.program h₃.root (h₃.span r₂ h₂.root)
  obtain ⟨m, G, k, h₅, a₅⟩ := sfm_all_l I hZF hω h₄.program hi h₄.root
  refine ⟨m, G, k, (((h₁.comp I h₂).comp I h₃).comp I h₄).comp I h₅, fun X R E f D A hE hf hD hA => ?_⟩
  have read x v (hx : M.mem x X) (hv : Senv_update_d I f i x v) :
      Ssat_d I X R E F₄ n₄ r₄ v ↔ (M.PairMember I x A R ↔ M.PairMember I x D R ∧
        ∃ w, Senv_update_d I f i x w ∧ Ssat_d I X R E F n r w) := by
    have hve := (hE v).mpr (hv.function_l I ((hE f).mp hf) hi hx)
    rw [a₄ X R E v hve, a₃ X R E v x A hE hve
      ((hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)) ((hv.2 t A).mpr (Or.inr ⟨hti, hA⟩)),
      ← h₃.sat_l I hZF h₂.program h₂.root X R E v, a₂ X R E v hve,
      a₁ X R E v x D hE hve ((hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)) ((hv.2 s D).mpr (Or.inr ⟨hsi, hD⟩)),
      ← h₁.sat_l I hZF hF hr X R E v]
    exact iff_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ⟨v, hv, h⟩,
      fun ⟨w, hw, h⟩ => senv_update_unique_l I hZF.1 hw hv ▸ h⟩)
  rw [a₅ X R E f hE hf]
  constructor
  · intro h x hx
    obtain ⟨v, hv, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
    exact (read x v hx hv).mp (h x v hx hv)
  · exact fun h x v hx hv => (read x v hx hv).mpr (h x hx)

theorem sfm_sep_raw_l (hZF : M.Models ZF) {ω n F r i s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) (hst : s ≠ t) (hb : Sbound_d I F b) (htb : ¬ M.mem t b) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E f D,
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ ∃ A, M.mem A X ∧ Sr_sep_d I X R E F n r i f D A) := by
  obtain ⟨v, J, u, h, test⟩ := sfm_sep_test_raw_l I hZF hω hF hr hi hs ht hsi hti
  obtain ⟨m, G, k, build, read⟩ := sfm_ex_l I hZF hω h.program ht h.root
  refine ⟨m, G, k, h.comp I build, fun X R E f D hE hf hD => ?_⟩
  have body A g (hA : M.mem A X) (hu : Senv_update_d I f t A g) :
      Ssat_d I X R E J v u g ↔ Sr_sep_d I X R E F n r i f D A := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) ht hA)
    exact (test X R E g D A hE hg ((hu.2 s D).mpr (Or.inr ⟨hst, hD⟩)) ((hu.2 t A).mpr (Or.inl ⟨rfl, rfl⟩))).trans
      (sr_sep_agree_l I hZF hF hb hr hi hE hf hg (hu.agree_l I htb)).symm
  rw [read X R E f hf]
  constructor
  · exact fun ⟨A, g, hA, hu, hh⟩ => ⟨A, hA, (body A g hA hu).mp hh⟩
  · rintro ⟨A, hA, hh⟩
    obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht hA
    exact ⟨A, g, hA, hu, (body A g hA hu).mpr hh⟩

end YesMetaZFC.SetTheory.Internal
