import YesMetaZFC.SetTheory.Card.Finite
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 内部有限集合的可定义像与积

有限性始终由模型内的自然数界见证；像的编号取最小原像，不用选择公理。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem finite_image_l {ω X Y F} (hω : M.IsOmega ω) (hx : Finite_d I ω X)
    (hf : M.IsSetFunctionFromTo I F X Y) (onto : M.IsSetSurjectiveOnto I F X Y) :
    Finite_d I ω Y := by
  obtain ⟨n, hn, hi⟩ := hx
  exact ⟨n, hn, ordinal_image_bound_l I hZF
    (hω.members_areOrdinals (ZF.modelsKP hZF) n hn) hi hf onto⟩

theorem finite_defined_image_l {ω X Y} (hω : M.IsOmega ω) (hx : Finite_d I ω X)
    {k} (φ : BinarySchema k) (ρ : Env M k)
    (total : ∀ x, M.mem x X → ∃ y, φ.denote ρ x y)
    (unique : ∀ x, M.mem x X → ∀ y z, φ.denote ρ x y → φ.denote ρ x z → y = z)
    (image : ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ φ.denote ρ x y) : Finite_d I ω Y := by
  obtain ⟨f, hf, graph⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun x y hx hy => (image y).mpr ⟨x, hx, hy⟩)
  exact finite_image_l I hZF hω hx hf (fun y hy => by
    obtain ⟨x, hx, hxy⟩ := (image y).mp hy
    exact ⟨x, hx, (graph x y).mpr ⟨hx, hxy⟩⟩)

/-- 两个内部有限指标集的积仍内部有限，包括非标准有限长度。 -/
theorem finite_product_l {ω X Y W} (hω : M.IsOmega ω)
    (hx : Finite_d I ω X) (hy : Finite_d I ω Y)
    (hw : M.IsCartesianProduct I W X Y) : Finite_d I ω W := by
  let ρ : Env M 2 := (⟨fun _ => Y, fun _ => Y⟩ : Env M 1).push ω
  let φ : UnarySchema 2 := {
    body := .forallE (.imp (Formula.isCartesianProduct 𝒞 .newest (.bound 1) (.bound 3))
      (finite_m 𝒞 (.bound 2) .newest)) }
  have sat A : φ.denote ρ A ↔ ∀ P, M.IsCartesianProduct I P A Y → Finite_d I ω P := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isCartesianProduct_iff I, finite_sat_l I hZF.1]; rfl
  apply (sat X).mp (finite_ind_l I hZF hω φ ρ ?_ ?_ X hx) W hw
  · intro A empty
    exact (sat A).mpr (fun P hp => finite_empty_l I hZF hω (fun p hm => by
      obtain ⟨a, ha, _⟩ := (hp p).mp hm
      exact empty a ha))
  · intro A a B _ ih insert
    apply (sat B).mpr
    intro P hp
    obtain ⟨D, hd⟩ := exists_cartesianProduct hZF I A Y
    obtain ⟨E, he⟩ := exists_cartesianRow hZF I a Y
    let η : Env M 1 := ⟨fun _ => a, fun _ => a⟩
    have row := finite_defined_image_l I hZF hω hy (BinarySchema.orderedPairWithLeft 𝒞) η
      (fun y _ => (I.total a y).imp (fun _ h => (Formula.denote_orderedPairWithLeft_iff I η _ _).mpr h))
      (fun y _ p q h g => I.unique ((Formula.denote_orderedPairWithLeft_iff I η y p).mp h)
        ((Formula.denote_orderedPairWithLeft_iff I η y q).mp g))
      (fun p => (he p).trans (exists_congr fun y => and_congr_right fun _ =>
        (Formula.denote_orderedPairWithLeft_iff I η y p).symm))
    apply finite_union_l I hZF hω ((sat A).mp ih D hd) row
    intro p
    constructor
    · rintro hm
      obtain ⟨x, hx, y, hy, code⟩ := (hp p).mp hm
      rcases (insert x).mp hx with hx | rfl
      · exact Or.inl ((hd p).mpr ⟨x, hx, y, hy, code⟩)
      · exact Or.inr ((he p).mpr ⟨y, hy, code⟩)
    · rintro (hm | hm)
      · obtain ⟨x, hx, y, hy, code⟩ := (hd p).mp hm
        exact (hp p).mpr ⟨x, (insert x).mpr (Or.inl hx), y, hy, code⟩
      · obtain ⟨y, hy, code⟩ := (he p).mp hm
        exact (hp p).mpr ⟨a, (insert a).mpr (Or.inr rfl), y, hy, code⟩

end YesMetaZFC.SetTheory.ZF
