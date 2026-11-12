import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.SeparationHull

/-! # 全内部公式的收集实例代码

先构造 ∀x∈D ∃y φ，再把 y∈C 加入矩阵并量化 C。所有程序均保留原前缀，
新集合坐标取在实际支撑之外，所得规格直接读取内部见证而非宿主函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_total_l (hZF : M.Models ZF) {ω n F r i j s} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (hsi : s ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ Scollect_d I X R E F n r i j f D X) := by
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_ex_l I hZF hω hF hj hr
  obtain ⟨n₂, F₂, h₂, a₂⟩ := sfm_rel_l I hZF hω h₁.program hi hs
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_imp_l I hZF hω h₂.program h₂.root (h₂.span r₁ h₁.root)
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_all_l I hZF hω h₃.program hi h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f D hX hm hE hf hD => ?_⟩
  have hDX := ((hE f).mp hf).output_mem_of_pairMember hD
  have read x g (hx : M.mem x X) (hu : Senv_update_d I f i x g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ (M.mem x D → ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) hi hx)
    rw [a₃ X R E g hg, a₂ X R E g x D hE hg ((hu.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
      ((hu.2 s D).mpr (Or.inr ⟨hsi, hD⟩)), ← h₂.sat_l I hZF h₁.program h₁.root X R E g, a₁ X R E g hg]
    have memD : M.PairMember I x D R ↔ M.mem x D := (hm.2 x D).trans
      ⟨fun h => h.2.2, fun h => ⟨hx, hDX, h⟩⟩
    refine imp_congr memD (exists_congr fun y => ?_)
    exact ⟨fun ⟨v, hy, hv, ht⟩ => ⟨hy, (sbin_update_l I hZF.1 hu).mpr ⟨v, hv, ht⟩⟩,
      fun ⟨hy, ht⟩ => ((sbin_update_l I hZF.1 hu).mp ht).elim fun v hv => ⟨v, hy, hv⟩⟩
  rw [a₄ X R E f hE hf]
  constructor
  · intro hh x hx
    have hxX := hX D hDX x hx
    obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hxX
    exact (read x g hxX hu).mp (hh x g hxX hu) hx
  · exact fun hh x g hx hu => (read x g hx hu).mpr (hh x)

theorem sfm_collect_l (hZF : M.Models ZF) {ω n F r i j s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (ht : M.mem t ω) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ ∃ C, M.mem C X ∧ Scollect_d I X R E F n r i j f D C) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hj ht
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_l I hZF hω h₂.program h₂.root hi hj hs hsi
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_ex_l I hZF hω h₃.program ht h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f D hX hm hE hf hD => ?_⟩
  have hDX := ((hE f).mp hf).output_mem_of_pairMember hD
  have body C g (hC : M.mem C X) (hu : Senv_update_d I f t C g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ Scollect_d I X R E F n r i j f D C := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) ht hC)
    have point x y (hx : M.mem x X) (hy : M.mem y X) :
        Sbin_d I X R E F₂ n₂ r₂ i j g x y ↔ M.mem y C ∧ Sbin_d I X R E F n r i j f x y := by
      obtain ⟨u, hv, huf⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
      obtain ⟨v, hw, hvf⟩ := senv_update_exists_l I hZF huf hj hy
      have htC := (hw.2 t C).mpr (Or.inr ⟨htj, (hv.2 t C).mpr
        (Or.inr ⟨hti, (hu.2 t C).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
      have hjy := (hw.2 j y).mpr (Or.inl ⟨rfl, rfl⟩)
      have memC : M.PairMember I y C R ↔ M.mem y C := (hm.2 y C).trans
        ⟨fun h => h.2.2, fun h => ⟨hy, hC, h⟩⟩
      have val : Sbin_d I X R E F n r i j f x y ↔ Ssat_d I X R E F n r v :=
        (sbin_agree_l I hZF hF hb hr hi hj hE hf hg (hu.agree_l I htb) hx hy).trans
        (sbin_value_l I hZF.1 hv hw)
      apply (sbin_value_l I hZF.1 hv hw).trans
      rw [a₂ X R E v ((hE v).mpr hvf), a₁ X R E v y C hE ((hE v).mpr hvf) hjy htC,
        ← h₁.sat_l I hZF hF hr X R E v]
      exact and_congr memC val.symm
    rw [a₃ X R E c g D hX hm hE hg ((hu.2 s D).mpr (Or.inr ⟨hst, hD⟩))]
    exact forall_congr' fun x => imp_congr_right fun hx =>
      ⟨fun ⟨y, hy, hh⟩ => ⟨y, (point x y (hX D hDX x hx) hy).mp hh⟩,
        fun ⟨y, hy, hh⟩ => ⟨y, hX C hC y hy, (point x y (hX D hDX x hx) (hX C hC y hy)).mpr ⟨hy, hh⟩⟩⟩
  rw [a₄ X R E f hf]
  constructor
  · exact fun ⟨C, g, hc, hu, hh⟩ => ⟨C, hc, (body C g hc hu).mp hh⟩
  · rintro ⟨C, hc, hh⟩
    obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht hc
    exact ⟨C, g, hc, hu, (body C g hc hu).mpr hh⟩

end YesMetaZFC.SetTheory.Internal
