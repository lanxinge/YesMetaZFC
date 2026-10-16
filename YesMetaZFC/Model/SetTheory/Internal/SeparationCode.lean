import YesMetaZFC.Model.SetTheory.Internal.RelationSeparation

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

/-- 传递隶属结构中的分离集读取是原关系方程的特例。 -/
theorem ssep_relation_l {c X R E F n r i f D A : M.Domain} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hD : M.mem D X) (hA : M.mem A X) :
    Sr_sep_d I X R E F n r i f D A ↔ Ssep_d I X R E F n r i f D A := by
  have mem x y (hx : M.mem x X) (hy : M.mem y X) : M.PairMember I x y R ↔ M.mem x y :=
    (hm.2 x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
  constructor
  · intro h x
    by_cases hx : M.mem x X
    · exact (mem x A hx hA).symm.trans ((h x hx).trans (and_congr (mem x D hx hD) Iff.rfl))
    · exact iff_of_false (fun ha => hx (hX A hA x ha)) (fun hd => hx (hX D hD x hd.1))
  · exact fun h x hx => (mem x A hx hA).trans ((h x).trans (and_congr (mem x D hx hD).symm Iff.rfl))

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
  obtain ⟨m, G, k, build, read⟩ := sfm_sep_test_raw_l I hZF hω hF hr hi hs ht hsi hti
  exact ⟨m, G, k, build, fun X R E c f D A hX hm hE hf hD hA =>
    (read X R E f D A hE hf hD hA).trans (ssep_relation_l I hX hm
      (((hE f).mp hf).output_mem_of_pairMember hD) (((hE f).mp hf).output_mem_of_pairMember hA))⟩

theorem sfm_sep_l (hZF : M.Models ZF) {ω n F r i s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) (hst : s ≠ t) (hb : Sbound_d I F b) (htb : ¬ M.mem t b) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → (Ssat_d I X R E G m k f ↔ ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨m, G, k, build, read⟩ := sfm_sep_raw_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  refine ⟨m, G, k, build, fun X R E c f D hX hm hE hf hD => ?_⟩
  exact (read X R E f D hE hf hD).trans (exists_congr fun A => and_congr_right fun hA =>
    ssep_relation_l I hX hm (((hE f).mp hf).output_mem_of_pairMember hD) hA)

end YesMetaZFC.SetTheory.Internal
