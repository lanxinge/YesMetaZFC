import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication

/-! # 原 ZF 内两个可数集的积与并

两个已给出的单射足以构造积和并的单射。并集用零、一标记来源，再通过
内部 ω×ω 的计数压回 ω；这里不使用可数选择或全局选择。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem countable_product_l (hZF : M.Models ZF) {ω X Y W} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hY : M.CardinalLessOrEqual I Y ω)
    (hW : M.IsCartesianProduct I W X Y) : M.CardinalLessOrEqual I W ω := by
  obtain ⟨S, hS⟩ := exists_cartesianProduct hZF I ω ω
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  obtain ⟨F, hF⟩ := exists_cartesianProductInjection hZF I hW hS hf hg
  have hωc := omega_cardinal_l I hZF hω
  obtain ⟨G, hG⟩ := cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hωc, Structure.Equinumerous.refl hZF I ω⟩ hS (omega_selfMultiplication hZF I hω hωc)
  exact exists_compositionInjection hZF I hF hG

/-- 两个可数集的实际并仍可数；重叠部分统一使用左侧编号。 -/
theorem countable_union_two_l (hZF : M.Models ZF) {ω X Y U} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hY : M.CardinalLessOrEqual I Y ω)
    (hU : M.IsUnionOfTwo U X Y) : M.CardinalLessOrEqual I U ω := by
  classical
  obtain ⟨F, hF⟩ := hX
  obtain ⟨G, hG⟩ := hY
  obtain ⟨e, he, heω⟩ := hω.1.1
  obtain ⟨l, hl, hlω⟩ := hω.1.2 e heω
  have hne : e ≠ l := by intro hh; subst l; exact he e hl.predecessor_mem
  obtain ⟨W, hW⟩ := exists_cartesianProduct hZF I ω ω
  let ρ : Env M 5 := ((((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push X).push e).push l
  let φ : BinarySchema 5 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 4)) (.existsE
      (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 7)) (𝒞.code (.bound 1) (.bound 4) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (.existsE
        (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 6)) (𝒞.code (.bound 1) (.bound 3) .newest)))) }
  have hφ x p : φ.denote ρ x p ↔
      (M.mem x X ∧ ∃ n, M.PairMember I x n F ∧ I.Codes p e n) ∨
      (¬ M.mem x X ∧ ∃ n, M.PairMember I x n G ∧ I.Codes p l n) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  obtain ⟨H, hH⟩ := exists_setInjectionFromTo_of_denote hZF I φ ρ (source := U) (target := W) (by
    intro x hx
    by_cases hxx : M.mem x X
    · obtain ⟨n, _, hxn⟩ := hF.1.2.2 x hxx
      obtain ⟨p, hp⟩ := I.total e n
      exact ⟨p, (hφ x p).mpr (Or.inl ⟨hxx, n, hxn, hp⟩)⟩
    · obtain ⟨n, _, hxn⟩ := hG.1.2.2 x (((hU x).mp hx).resolve_left hxx)
      obtain ⟨p, hp⟩ := I.total l n
      exact ⟨p, (hφ x p).mpr (Or.inr ⟨hxx, n, hxn, hp⟩)⟩) (by
    intro x _ p q hp hq
    rcases (hφ x p).mp hp with ⟨hx, n, hn, hp⟩ | ⟨hx, n, hn, hp⟩ <;>
      rcases (hφ x q).mp hq with ⟨hy, m, hm, hq⟩ | ⟨hy, m, hm, hq⟩
    · have he := hF.1.1.2 x n m hn hm
      subst m
      exact I.unique hp hq
    · exact False.elim (hy hx)
    · exact False.elim (hx hy)
    · have he := hG.1.1.2 x n m hn hm
      subst m
      exact I.unique hp hq) (by
    intro x p _ hp
    rcases (hφ x p).mp hp with ⟨_, n, hn, hp⟩ | ⟨_, n, hn, hp⟩
    · exact (hW p).mpr ⟨e, heω, n, hF.1.output_mem_of_pairMember hn, hp⟩
    · exact (hW p).mpr ⟨l, hlω, n, hG.1.output_mem_of_pairMember hn, hp⟩) (by
    intro x y p _ _ hx hy
    rcases (hφ x p).mp hx with ⟨_, n, hn, hp⟩ | ⟨_, n, hn, hp⟩ <;>
      rcases (hφ y p).mp hy with ⟨_, m, hm, hp'⟩ | ⟨_, m, hm, hp'⟩
    · obtain ⟨_, hnm⟩ := I.injective hp hp'
      subst m
      exact hF.2 x y n hn hm
    · exact False.elim (hne (I.injective hp hp').1)
    · exact False.elim (hne (I.injective hp hp').1.symm)
    · obtain ⟨_, hnm⟩ := I.injective hp hp'
      subst m
      exact hG.2 x y n hn hm)
  obtain ⟨J, hJ⟩ := exists_identityBijection hZF I ω
  obtain ⟨K, hK⟩ := countable_product_l I hZF hω ⟨J, hJ.1⟩ ⟨J, hJ.1⟩ hW
  exact exists_compositionInjection hZF I hH hK

end YesMetaZFC.SetTheory.ZF
