import YesMetaZFC.Model.SetTheory.Internal.RelationUniformCode

/-! # 原关系模型的普通收集程序

集合界按原成员关系读取。追加的集合变量位于旧程序支撑外，原公式的所有
内部赋值保持不变；这给完整内部 ZFC 的后继传输提供真正的模式程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem sfm_collect_raw_l {ω n F r i j s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (ht : M.mem t ω) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ C : (smdl_structure_l I (R := R) model.2.1).Domain,
        ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain, M.PairMember I x.val D.val R →
          ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
            M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val) := by
  obtain ⟨n₁, F₁, h₁, a₁⟩ := sfm_rel_l I hZF hω hF hj ht
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_raw_l I hZF hω h₂.program h₂.root hi hj hs hsi
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_ex_l I hZF hω h₃.program ht h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f model D hE hf hD => ?_⟩
  have body (C : (smdl_structure_l I (R := R) model.2.1).Domain) g (ug : Senv_update_d I f t C.val g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain,
        M.PairMember I x.val D.val R → ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
          M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val := by
    have hg := (hE g).mpr (ug.function_l I ((hE f).mp hf) ht C.property)
    have point (x y : (smdl_structure_l I (R := R) model.2.1).Domain) :
        Sbin_d I X R E F₂ n₂ r₂ i j g x.val y.val ↔
          M.PairMember I y.val C.val R ∧ Sbin_d I X R E F n r i j f x.val y.val := by
      obtain ⟨u, uv, fu⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi x.property
      obtain ⟨v, vv, fv⟩ := senv_update_exists_l I hZF fu hj y.property
      have htC := (vv.2 t C.val).mpr (Or.inr ⟨htj, (uv.2 t C.val).mpr
        (Or.inr ⟨hti, (ug.2 t C.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
      have val : Sbin_d I X R E F n r i j f x.val y.val ↔ Ssat_d I X R E F n r v :=
        (sbin_agree_l I hZF hF hb hr hi hj hE hf hg (ug.agree_l I htb) x.property y.property).trans
          (sbin_value_l I hZF.1 uv vv)
      apply (sbin_value_l I hZF.1 uv vv).trans
      rw [a₂ X R E v ((hE v).mpr fv), a₁ X R E v y.val C.val hE ((hE v).mpr fv)
        ((vv.2 j y.val).mpr (Or.inl ⟨rfl, rfl⟩)) htC, ← h₁.sat_l I hZF hF hr X R E v]
      exact and_congr Iff.rfl val.symm
    rw [a₃ X R E c g model D hE hg ((ug.2 s D.val).mpr (Or.inr ⟨hst, hD⟩))]
    exact forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => point x y
  rw [a₄ X R E f hf]
  constructor
  · rintro ⟨C, g, hc, ug, truth⟩
    exact ⟨⟨C, hc⟩, (body ⟨C, hc⟩ g ug).mp truth⟩
  · rintro ⟨C, truth⟩
    obtain ⟨g, ug, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ht C.property
    exact ⟨C.val, g, C.property, ug, (body C g ug).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
