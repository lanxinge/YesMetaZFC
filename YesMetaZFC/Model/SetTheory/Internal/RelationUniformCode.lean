import YesMetaZFC.Model.SetTheory.Internal.CollectionCode
import YesMetaZFC.Model.SetTheory.Internal.FunctionCode
import YesMetaZFC.Model.SetTheory.Internal.RelationFunction

/-! # 任意关系模型中的内部统一见证程序

原公式可以有非标准内部长度；这里只追加固定的函数图模板和量词。
函数对象、定义域及值域均按原关系解释，不要求整个模型坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem sfm_total_raw_l {ω n F r i j s} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω)
    (hs : M.mem s ω) (hsi : s ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∀ x : (smdl_structure_l I (R := R) model.2.1).Domain,
        M.PairMember I x.val D.val R → ∃ y : (smdl_structure_l I (R := R) model.2.1).Domain,
          Sbin_d I X R E F n r i j f x.val y.val) := by
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_ex_l I hZF hω hF hj hr
  obtain ⟨n₂, F₂, h₂, a₂⟩ := sfm_rel_l I hZF hω h₁.program hi hs
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_imp_l I hZF hω h₂.program h₂.root (h₂.span r₁ h₁.root)
  obtain ⟨m, G, k, h₄, a₄⟩ := sfm_all_l I hZF hω h₃.program hi h₃.root
  refine ⟨m, G, k, ((h₁.comp I h₂).comp I h₃).comp I h₄, fun X R E c f model D hE hf hD => ?_⟩
  have read x g (hx : M.mem x X) (hu : Senv_update_d I f i x g) :
      Ssat_d I X R E F₃ n₃ r₃ g ↔ (M.PairMember I x D.val R →
        ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) := by
    have hg := (hE g).mpr (hu.function_l I ((hE f).mp hf) hi hx)
    rw [a₃ X R E g hg, a₂ X R E g x D.val hE hg ((hu.2 i x).mpr (Or.inl ⟨rfl, rfl⟩))
      ((hu.2 s D.val).mpr (Or.inr ⟨hsi, hD⟩)), ← h₂.sat_l I hZF h₁.program h₁.root X R E g, a₁ X R E g hg]
    exact imp_congr Iff.rfl (exists_congr fun y =>
      ⟨fun ⟨v, hy, hv, ht⟩ => ⟨hy, (sbin_update_l I hZF.1 hu).mpr ⟨v, hv, ht⟩⟩,
        fun ⟨hy, ht⟩ => ((sbin_update_l I hZF.1 hu).mp ht).elim fun v hv => ⟨v, hy, hv⟩⟩)
  rw [a₄ X R E f hE hf]
  constructor
  · intro h x hx
    obtain ⟨g, hg, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi x.property
    obtain ⟨y, hy, hxy⟩ := (read x.val g x.property hg).mp (h x.val g x.property hg) hx
    exact ⟨⟨y, hy⟩, hxy⟩
  · intro h x g hx hg
    exact (read x g hx hg).mpr fun hd => (h ⟨x, hx⟩ hd).elim fun y hy => ⟨y.val, y.property, hy⟩

theorem sfm_function_raw_l {ω n F i s u σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hσ : M.mem σ ω) (hi : M.mem i σ) (hs : M.mem s σ) (hu : M.mem u σ)
    (hus : u ≠ s) (hui : u ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (B D : (smdl_structure_l I (R := R) model.2.1).Domain),
      Extensional (smdl_structure_l I (R := R) model.2.1) →
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I i B.val f → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ C : (smdl_structure_l I (R := R) model.2.1).Domain, Fn0_d D C B) := by
  let q : Fin 3 → M.Domain := Fin.cases s (Fin.cases u (fun _ => i))
  let φ : Formula 1 3 := fn0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, r, h, template⟩ := sfm_template_l I hZF hω hF φ (by simp -implicitDefEqProofs [φ])
    q hσ (Fin.cases hs (Fin.cases hu (fun _ => hi)))
  have huω := hω.transitive hZF σ hσ u hu
  obtain ⟨m, G, k, g, quantifier⟩ := sfm_ex_l I hZF hω h.program huω h.root
  refine ⟨m, G, k, h.comp I g, fun X R E c f model B D ext hE hf hiB hsD => ?_⟩
  have read (C : (smdl_structure_l I (R := R) model.2.1).Domain) a (ha : Senv_update_d I f u C.val a) :
      Ssat_d I X R E J v r a ↔ Fn0_d D C B := by
    let ρ : Env (smdl_structure_l I (R := R) model.2.1) 3 := ⟨Fin.cases D (Fin.cases C (fun _ => B)), fun _ => B⟩
    exact (template X R model.2.1 E hE a ((hE a).mpr (ha.function_l I ((hE f).mp hf) huω C.property))
      ρ
      (Fin.cases ((ha.2 s D.val).mpr (Or.inr ⟨Ne.symm hus, hsD⟩))
        (Fin.cases ((ha.2 u C.val).mpr (Or.inl ⟨rfl, rfl⟩))
          (fun _ => (ha.2 i B.val).mpr (Or.inr ⟨Ne.symm hui, hiB⟩))))).trans
      (fn0_sat_l ext ρ .newest (.bound 1) (.bound 2))
  rw [quantifier X R E f hf]
  constructor
  · rintro ⟨C, a, hC, ha, ht⟩
    exact ⟨⟨C, hC⟩, (read ⟨C, hC⟩ a ha).mp ht⟩
  · rintro ⟨C, ht⟩
    obtain ⟨a, ha, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) huω C.property
    exact ⟨C.val, a, C.property, ha, (read C a ha).mpr ht⟩

/-- 对内部原程序统一取值，输出的是原关系模型拥有的函数对象。 -/
theorem sfm_uniform_raw_l {ω n F r i j s t u σ b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hj : M.mem j σ) (hs : M.mem s σ) (ht : M.mem t σ) (hu : M.mem u σ)
    (hij : i ≠ j) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t) (hus : u ≠ s) (hut : u ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f
      (model : Smdl_d I c X R) (D : (smdl_structure_l I (R := R) model.2.1).Domain),
      Extensional (smdl_structure_l I (R := R) model.2.1) →
      M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D.val f →
      (Ssat_d I X R E G m k f ↔ ∃ B C : (smdl_structure_l I (R := R) model.2.1).Domain,
        Fn0_d D C B ∧ ∀ x y : (smdl_structure_l I (R := R) model.2.1).Domain,
          Rd_entry_d x y B → Sbin_d I X R E F n r i j f x.val y.val) := by
  have into a (ha : M.mem a σ) := hω.transitive hZF σ hσ a ha
  -- s 保存定义域，t 保存待选函数，u 保存其值域；i、j 仍是原公式变量。
  let p : Fin 3 → M.Domain := Fin.cases i (Fin.cases j (fun _ => t))
  let φ : Formula 1 3 := rd_entry0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_template_l I hZF hω hF φ (by simp -implicitDefEqProofs [φ])
    p hσ (Fin.cases hi (Fin.cases hj (fun _ => ht)))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_raw_l I hZF hω h₂.program h₂.root (into i hi) (into j hj) (into s hs) hsi
  obtain ⟨n₅, F₅, r₅, h₅, a₅⟩ := sfm_function_raw_l I hZF hω h₃.program hσ ht hs hu hus hut
  obtain ⟨n₆, F₆, r₆, h₆, a₆⟩ := sfm_and_l I hZF hω h₅.program (h₅.span r₃ h₃.root) h₅.root
  obtain ⟨m, G, k, h₇, a₇⟩ := sfm_ex_l I hZF hω h₆.program (into t ht) h₆.root
  refine ⟨m, G, k, ((((h₁.comp I h₂).comp I h₃).comp I h₅).comp I h₆).comp I h₇,
    fun X R E c f model D ext hE hf hD => ?_⟩
  let N := smdl_structure_l I (R := R) model.2.1
  have en := ext
  have body (B : N.Domain) g (hg : Senv_update_d I f t B.val g) :
      Ssat_d I X R E F₆ n₆ r₆ g ↔ ∃ C : N.Domain, Fn0_d D C B ∧
        ∀ x y : N.Domain, Rd_entry_d x y B → Sbin_d I X R E F n r i j f x.val y.val := by
    have hgE := (hE g).mpr (hg.function_l I ((hE f).mp hf) (into t ht) B.property)
    have hsD := (hg.2 s D.val).mpr (Or.inr ⟨hst, hD⟩)
    have htB := (hg.2 t B.val).mpr (Or.inl ⟨rfl, rfl⟩)
    have point (x y : N.Domain) : Sbin_d I X R E F₂ n₂ r₂ i j g x.val y.val ↔
        Rd_entry_d x y B ∧ Sbin_d I X R E F n r i j f x.val y.val := by
      obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF ((hE g).mp hgE) (into i hi) x.property
      obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF hvf (into j hj) y.property
      let ρ : Env N 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
      have hp : ∀ z, M.PairMember I (p z) (ρ.bound z).val w := Fin.cases
        ((hw.2 i x.val).mpr (Or.inr ⟨hij, (hv.2 i x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
        (Fin.cases ((hw.2 j y.val).mpr (Or.inl ⟨rfl, rfl⟩)) (fun _ => (hw.2 t B.val).mpr
          (Or.inr ⟨htj, (hv.2 t B.val).mpr (Or.inr ⟨hti, htB⟩)⟩)))
      have atom := (a₁ X R model.2.1 E hE w ((hE w).mpr hwf) ρ hp).trans
        (rd_entry0_sat_l en ρ .newest (.bound 1) (.bound 2))
      have val : Sbin_d I X R E F n r i j f x.val y.val ↔ Ssat_d I X R E F n r w :=
        (sbin_agree_l I hZF hF hb hr (into i hi) (into j hj) hE hf hgE
        (hg.agree_l I htb) x.property y.property).trans (sbin_value_l I hZF.1 hv hw)
      apply (sbin_value_l I hZF.1 hv hw).trans
      rw [a₂ X R E w ((hE w).mpr hwf), ← h₁.sat_l I hZF hF hr X R E w]
      exact and_congr atom val.symm
    rw [a₆ X R E g hgE, ← h₅.sat_l I hZF h₃.program h₃.root X R E g,
      a₃ X R E c g model D hE hgE hsD, a₅ X R E c g model B D ext hE hgE htB hsD]
    constructor
    · rintro ⟨total, C, fn⟩
      refine ⟨C, fn, fun x y hxy => ?_⟩
      obtain ⟨z, hz⟩ := total x (fn.bound_l hxy).1
      obtain ⟨hxz, truth⟩ := (point x z).mp hz
      have eq := fn.2.2 x (fn.bound_l hxy).1 z (fn.bound_l hxz).2 y (fn.bound_l hxy).2 hxz hxy
      exact congrArg Subtype.val eq ▸ truth
    · rintro ⟨C, fn, truth⟩
      refine ⟨fun x hx => ?_, C, fn⟩
      obtain ⟨y, _, hxy⟩ := fn.2.1 x hx
      exact ⟨y, (point x y).mpr ⟨hxy, truth x y hxy⟩⟩
  rw [a₇ X R E f hf]
  constructor
  · rintro ⟨B, g, hB, hg, h⟩
    obtain ⟨C, fn, truth⟩ := (body ⟨B, hB⟩ g hg).mp h
    exact ⟨⟨B, hB⟩, C, fn, truth⟩
  · rintro ⟨B, C, fn, truth⟩
    obtain ⟨g, hg, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (into t ht) B.property
    exact ⟨B.val, g, B.property, hg, (body B g hg).mpr ⟨C, fn, truth⟩⟩

end YesMetaZFC.SetTheory.Internal
