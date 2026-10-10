import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Ord.Natural

/-! # 模型内部 ω 的基数性

跳过一个自然数给出 ω 到其真子集的实际单射。对内部自然数归纳，排除 ω 向
有限序数的单射，从而补全 ω 是初始序数的证书；不假设模型的 ω 外部标准。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem omega_skip_l (hZF : M.Models ZF) {ω i : M.Domain} (hω : M.IsOmega ω) (hi : M.mem i ω) :
    ∃ F, M.IsSetInjectionFromTo I F ω ω ∧ ∀ x, ¬ M.PairMember I x i F := by
  classical
  let φ : BinarySchema 1 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 1)))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.isSuccessor .newest (.bound 1))) }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have hφ x y : φ.denote ρ x y ↔ (M.mem x i ∧ y = x) ∨ (¬ M.mem x i ∧ M.SuccessorOf y x) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isSuccessor_iff]
    rfl
  obtain ⟨F, hF, he⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω) (by
    intro x hx
    by_cases hxi : M.mem x i
    · exact ⟨x, (hφ x x).mpr (Or.inl ⟨hxi, rfl⟩)⟩
    · obtain ⟨y, hy, _⟩ := hω.1.2 x hx
      exact ⟨y, (hφ x y).mpr (Or.inr ⟨hxi, hy⟩)⟩) (by
    intro x _ y z hy hz
    rcases (hφ x y).mp hy with hy | hy <;> rcases (hφ x z).mp hz with hz | hz
    · exact hy.2.trans hz.2.symm
    · exact False.elim (hz.1 hy.1)
    · exact False.elim (hy.1 hz.1)
    · exact Structure.SuccessorOf.eq hZF.1 hy.2 hz.2) (by
    intro x y hx hy
    rcases (hφ x y).mp hy with hy | hy
    · exact hy.2 ▸ hx
    · obtain ⟨z, hz, hzω⟩ := hω.1.2 x hx
      exact Structure.SuccessorOf.eq hZF.1 hy.2 hz ▸ hzω)
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · intro x y z hx hy
    have hxω := hF.input_mem_of_pairMember hx
    have hyω := hF.input_mem_of_pairMember hy
    rcases (hφ x z).mp ((he x z).mp hx).2 with hx | hx <;>
      rcases (hφ y z).mp ((he y z).mp hy).2 with hy | hy
    · exact hx.2.symm.trans hy.2
    · have hyz := hy.2.predecessor_mem
      exact False.elim (hy.1 ((hω.members_areOrdinals hZF i hi).transitive x hx.1 y (hx.2 ▸ hyz)))
    · have hxz := hx.2.predecessor_mem
      exact False.elim (hx.1 ((hω.members_areOrdinals hZF i hi).transitive y hy.1 x (hy.2 ▸ hxz)))
    · exact Structure.SuccessorOf.predecessor_eq hZF.1 (hω.members_areOrdinals hZF x hxω) hx.2 hy.2
  · intro x hx
    rcases (hφ x i).mp ((he x i).mp hx).2 with hx | hx
    · exact (hω.isOrdinal hZF).wellOrder.linear.irrefl i hi (hx.2.symm ▸ hx.1)
    · exact hx.1 hx.2.predecessor_mem

theorem omega_not_le_finite_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) :
    ∀ n, M.mem n ω → ¬ M.CardinalLessOrEqual I ω n := by
  classical
  apply hω.induction (fun n => ¬ M.CardinalLessOrEqual I ω n)
  · let φ : UnarySchema 1 := { body := .neg (Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest) }
    obtain ⟨T, hT⟩ := separation_exists_d hZF φ (⟨fun _ => ω, fun _ => ω⟩ : Env M 1) ω
    refine ⟨T, fun n => ?_⟩
    rw [hT n]
    simp only [φ, Formula.satisfies_neg_iff, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  · intro e he ⟨F, hF⟩
    obtain ⟨o, _, ho⟩ := hω.1.1
    obtain ⟨x, hx, _⟩ := hF.1.2.2 o ho
    exact he x hx
  · intro n hn ih s hs ⟨F, hF⟩
    by_cases hhit : ∃ i, M.PairMember I i n F
    · obtain ⟨i, hi⟩ := hhit
      obtain ⟨G, hG, hGi⟩ := omega_skip_l I hZF hω (hF.1.input_mem_of_pairMember hi)
      obtain ⟨H, hH, he⟩ := exists_compositionFunction hZF I hG.1 hF.1
      have hinj : M.IsSetInjective I H := by
        intro x y v hx hy
        obtain ⟨_, a, hxa, hav⟩ := (he x v).mp hx
        obtain ⟨_, b, hyb, hbv⟩ := (he y v).mp hy
        have hab := hF.2 a b v hav hbv
        exact hG.2 x y a hxa (hab ▸ hyb)
      apply ih
      refine ⟨H, ⟨hH.1, hH.2.1, fun x hx => ?_⟩, hinj⟩
      obtain ⟨y, hy, hxy⟩ := hH.2.2 x hx
      rcases (hs y).mp hy with hyn | heq
      · exact ⟨y, hyn, hxy⟩
      · have heq := hZF.1.eq_of_same_members y n heq
        subst y
        obtain ⟨_, a, hxa, han⟩ := (he x n).mp hxy
        have hai := hF.2 a i n han hi
        exact False.elim (hGi x (hai ▸ hxa))
    · apply ih
      refine ⟨F, ⟨hF.1.1, hF.1.2.1, fun x hx => ?_⟩, hF.2⟩
      obtain ⟨y, hy, hxy⟩ := hF.1.2.2 x hx
      rcases (hs y).mp hy with hyn | heq
      · exact ⟨y, hyn, hxy⟩
      · exact False.elim (hhit ⟨x, hZF.1.eq_of_same_members y n heq ▸ hxy⟩)

/-- ω 的基数性由原 ZF 自动取得，不再要求调用者另行给出。 -/
theorem omega_cardinal_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) : M.IsCardinal I ω := by
  refine ⟨hω.isOrdinal hZF, fun n hn he => ?_⟩
  obtain ⟨F, hF⟩ := he.symm hZF I
  exact omega_not_le_finite_l I hZF hω n hn ⟨F, hF.1⟩

/-- 可数集添加一个元素仍可数；旧值移到后继，新元素使用零。 -/
theorem countable_insert_l (hZF : M.Models ZF) {ω X S a : M.Domain} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hS : ∀ x, M.mem x S ↔ M.mem x X ∨ x = a) :
    M.CardinalLessOrEqual I S ω := by
  classical
  obtain ⟨F, hF⟩ := hX
  obtain ⟨e, he, heω⟩ := hω.1.1
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push a).push e
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
      (Formula.extensionalEq .newest (.bound 2))) (.conj
        (.neg (Formula.extensionalEq (.bound 1) (.bound 3))) (.existsE
          (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5))
            (Formula.isSuccessor (.bound 1) .newest)))) }
  have hφ x y : φ.denote ρ x y ↔ (x = a ∧ y = e) ∨
      (x ≠ a ∧ ∃ n, M.PairMember I x n F ∧ M.SuccessorOf y n) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff]
    rfl
  have hz {y n} (hy : y = e) (hs : M.SuccessorOf y n) : False := he n (hy ▸ hs.predecessor_mem)
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro x hx
    by_cases hxa : x = a
    · exact ⟨e, (hφ x e).mpr (Or.inl ⟨hxa, rfl⟩)⟩
    · have hxX := ((hS x).mp hx).resolve_right hxa
      obtain ⟨n, hn, hxn⟩ := hF.1.2.2 x hxX
      obtain ⟨y, hy, _⟩ := hω.1.2 n hn
      exact ⟨y, (hφ x y).mpr (Or.inr ⟨hxa, n, hxn, hy⟩)⟩
  · intro x _ y z hy hz'
    rcases (hφ x y).mp hy with hy | ⟨hne, n, hxn, hy⟩ <;>
      rcases (hφ x z).mp hz' with hz' | ⟨hne', m, hxm, hz'⟩
    · exact hy.2.trans hz'.2.symm
    · exact False.elim (hne' hy.1)
    · exact False.elim (hne hz'.1)
    · have hnm := hF.1.1.2 x n m hxn hxm
      subst m
      exact Structure.SuccessorOf.eq hZF.1 hy hz'
  · intro x y _ hy
    rcases (hφ x y).mp hy with hy | ⟨_, n, hxn, hy⟩
    · exact hy.2 ▸ heω
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 n (hF.1.output_mem_of_pairMember hxn)
      exact Structure.SuccessorOf.eq hZF.1 hy hs ▸ hsω
  · intro x y z _ _ hx hy
    rcases (hφ x z).mp hx with hx | ⟨_, n, hxn, hx⟩ <;>
      rcases (hφ y z).mp hy with hy | ⟨_, m, hym, hy⟩
    · exact hx.1.trans hy.1.symm
    · exact False.elim (hz hx.2 hy)
    · exact False.elim (hz hy.2 hx)
    · have heq := Structure.SuccessorOf.predecessor_eq hZF.1
        (hω.members_areOrdinals hZF n (hF.1.output_mem_of_pairMember hxn)) hx hy
      subst m
      exact hF.2 x y n hxn hym

end YesMetaZFC.SetTheory.ZF
