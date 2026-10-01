import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.Card.Cofinality.Basic
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 可数序数集合的内部共尾序列

先将给定单射反向延拓为内部 ω 枚举，再对每段内部有限初段取最小上界。
有限初段有界性在原公式上归纳；最小值唯一，整个序列由替代构造，只需 ZF。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 无最大元的内部可数序数集合有实际 ω 共尾列，全部值仍取在原集合中。 -/
theorem cc_cofinal_sequence_l (hZF : M.Models ZF) {ω β A a} (hω : M.IsOmega ω)
    (hβ : M.IsOrdinal β) (hAβ : M.MemberSubset A β) (hA : M.CardinalLessOrEqual I A ω)
    (ha : M.mem a A) (hn : ∀ x, M.mem x A → ∃ y, M.mem y A ∧ M.mem x y) :
    ∃ γ F, M.IsCofinalSubset A γ ∧ M.MemberSubset γ β ∧ M.IsSetFunctionFromTo I F ω A ∧
      M.IsCofinalNondecreasingOrdinalSequence I F ω γ ∧
      ∀ i x, M.PairMember I i x F → M.mem a x := by
  obtain ⟨G, hG⟩ := hA
  obtain ⟨g, hg, hgr⟩ := injection_retract_l I hZF hG (fun _ h => h) ha
  have upper x y (hx : M.mem x A) (hy : M.mem y A) : ∃ z, M.mem z A ∧ M.mem x z ∧ M.mem y z := by
    rcases hβ.wellOrder.linear.compare x (hAβ x hx) y (hAβ y hy) with he | hxy | hyx
    · obtain ⟨z, hz, hyz⟩ := hn y hy
      exact ⟨z, hz, (hZF.1.eq_of_same_members x y he).symm ▸ hyz, hyz⟩
    · obtain ⟨z, hz, hyz⟩ := hn y hy
      exact ⟨z, hz, (hβ.mem (hAβ z hz)).transitive y hyz x hxy, hyz⟩
    · obtain ⟨z, hz, hxz⟩ := hn x hx
      exact ⟨z, hz, hxz, (hβ.mem (hAβ z hz)).transitive x hxz y hyx⟩
  let ρ : Env M 3 := ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push a).push g
  let θ : UnarySchema 4 := {
    body := .conj (.mem .newest (.bound 4)) (.conj (.mem (.bound 3) .newest)
      (Formula.forallMem (.bound 1) (.forallE (.imp
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem .newest (.bound 2)))))) }
  have hθ i y : θ.denote (ρ.push i) y ↔ M.mem y A ∧ M.mem a y ∧
      ∀ j, M.mem j i → ∀ x, M.PairMember I j x g → M.mem x y := by
    simp only [UnarySchema.denote, θ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have total : ∀ i, M.mem i ω → ∃ y, θ.denote (ρ.push i) y := by
    apply hω.induction (fun i => ∃ y, θ.denote (ρ.push i) y)
    · let φ : UnarySchema 3 := { body := .existsE θ.body }
      obtain ⟨C, hC⟩ := separation_exists_d hZF φ ρ ω
      exact ⟨C, fun i => by simpa only [φ, Formula.satisfies_exists_iff] using! hC i⟩
    · intro e he
      obtain ⟨y, hy, hay⟩ := hn a ha
      exact ⟨y, (hθ e y).mpr ⟨hy, hay, fun j hj => (he j hj).elim⟩⟩
    · intro i hi ih j hij
      obtain ⟨y, hy⟩ := ih
      obtain ⟨hyA, hay, hy⟩ := (hθ i y).mp hy
      obtain ⟨x, hx, hix⟩ := hg.2.2 i hi
      obtain ⟨z, hz, hyz, hxz⟩ := upper y x hyA hx
      refine ⟨z, (hθ j z).mpr ⟨hz, (hβ.mem (hAβ z hz)).transitive y hyz a hay, fun k hk u hku => ?_⟩⟩
      rcases (hij k).mp hk with hk | hk
      · exact (hβ.mem (hAβ z hz)).transitive y hyz u (hy k hk u hku)
      · exact hg.1.2 i x u hix ((hZF.1.eq_of_same_members k i hk) ▸ hku) ▸ hxz
  let e : Fin 4 → Term 6 := fun i => .bound ⟨i.val+2, by omega⟩
  let ψ : BinarySchema 3 := {
    body := .conj θ.body (.forallE (.imp (pred_m θ e .newest) (Formula.subset (.bound 1) .newest)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, θ, e] }
  have hψ i y : ψ.denote ρ i y ↔ θ.denote (ρ.push i) y ∧
      ∀ z, θ.denote (ρ.push i) z → M.MemberSubset y z := by
    have he z : (⟨fun k => (e k).eval (((ρ.push i).push y).push z),
        (((ρ.push i).push y).push z).free⟩ : Env M 4) = ρ.push i := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))), rfl⟩
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, pred_sat_l M, he]
    rfl
  have least i (hi : M.mem i ω) : ∃ y, ψ.denote ρ i y := by
    obtain ⟨C, hC⟩ := separation_exists_d hZF θ (ρ.push i) A
    obtain ⟨y, hy⟩ := total i hi
    obtain ⟨z, hz, hmin⟩ := hβ.wellOrder.least C (fun x hx => hAβ x ((hC x).mp hx).1)
      ⟨y, (hC y).mpr ⟨((hθ i y).mp hy).1, hy⟩⟩
    refine ⟨z, (hψ i z).mpr ⟨((hC z).mp hz).2, fun x hx => ?_⟩⟩
    rcases hmin x ((hC x).mpr ⟨((hθ i x).mp hx).1, hx⟩) with he | hzx
    · exact fun t ht => (he t).mp ht
    · exact (hβ.mem (hAβ x ((hθ i x).mp hx).1)).transitive.memberSubset hzx
  obtain ⟨F, hF, hf⟩ := exists_setFunctionFromTo_of_denote hZF I ψ ρ least (by
    intro i _ x y hx hy
    obtain ⟨hx, hmin⟩ := (hψ i x).mp hx
    obtain ⟨hy, hmin'⟩ := (hψ i y).mp hy
    exact hZF.1.eq_of_same_members x y (fun t => ⟨hmin y hy t, hmin' x hx t⟩))
    (fun i y _ hy => ((hθ i y).mp ((hψ i y).mp hy).1).1)
  have bound {i x} (hix : M.PairMember I i x F) := (hθ i x).mp ((hψ i x).mp ((hf i x).mp hix).2).1
  have inc : Cc_increasing_d I F := by
    intro i j x y hij hix hjy
    have hiy : θ.denote (ρ.push i) y := (hθ i y).mpr
      ⟨(bound hjy).1, (bound hjy).2.1, fun k hk z hkz => (bound hjy).2.2 k
        (((hω.isOrdinal hZF).mem (hF.input_mem_of_pairMember hjy)).transitive i hij k hk) z hkz⟩
    exact ((hψ i x).mp ((hf i x).mp hix).2).2 y hiy
  obtain ⟨γ, hγ⟩ := KP.exists_union (modelsKP hZF) A
  have hγo := Structure.IsOrdinal.of_union (modelsKP hZF) hγ (fun x hx => hβ.mem (hAβ x hx))
  have hAγ x (hx : M.mem x A) : M.mem x γ := by
    obtain ⟨y, hy, hxy⟩ := hn x hx
    exact (hγ x).mpr ⟨y, hy, hxy⟩
  have hγlim : M.IsLimitOrdinal γ := ⟨hγo, ⟨a, hAγ a ha⟩, fun x hx => by
    obtain ⟨y, hy, hxy⟩ := (hγ x).mp hx
    exact ⟨y, hAγ y hy, hxy⟩⟩
  have cof x (hx : M.mem x γ) : ∃ i y, M.PairMember I i y F ∧ M.mem x y := by
    obtain ⟨y, hy, hxy⟩ := (hγ x).mp hx
    obtain ⟨i, hi, hyi⟩ := hG.1.2.2 y hy
    obtain ⟨j, hij, hj⟩ := hω.1.2 i hi
    obtain ⟨z, _, hjz⟩ := hF.2.2 j hj
    exact ⟨j, z, hjz, (hβ.mem (hAβ z (bound hjz).1)).transitive y
      ((bound hjz).2.2 i hij.predecessor_mem y (hgr y i hyi)) x hxy⟩
  have ord : M.IsOrdinalValuedSequence I F ω := ⟨⟨hω.isOrdinal hZF, hF.1, hF.2.1⟩,
    fun _ _ x hx => hβ.mem (hAβ x (hF.output_mem_of_pairMember hx))⟩
  obtain ⟨J, hJ⟩ := exists_range_of_setFunction hZF I hF.1 hF.2.1
  have lim : M.IsUnionOf γ J := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, y, hi, hxy⟩ := cof x hx
      exact ⟨y, (hJ y).mpr ⟨i, hi⟩, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨i, hi⟩ := (hJ y).mp hy
      exact (hγ x).mpr ⟨y, hF.output_mem_of_pairMember hi, hxy⟩
  refine ⟨γ, F, ⟨hγlim, hAγ, hγ⟩, fun x hx => ?_, hF, ⟨hγlim, ⟨ord, ?_⟩, ⟨hγo, ord, J, hJ, lim⟩,
    fun _ _ x hx => hAγ x (hF.output_mem_of_pairMember hx)⟩, fun _ _ hx => (bound hx).2.1⟩
  · obtain ⟨y, hy, hxy⟩ := (hγ x).mp hx
    exact hβ.transitive y (hAβ y hy) x hxy
  · intro i _ j _ hij x y hix hjy
    rcases hβ.wellOrder.linear.compare x (hAβ x (bound hix).1) y (hAβ y (bound hjy).1) with he | hxy | hyx
    · exact Or.inl (hZF.1.eq_of_same_members x y he)
    · exact Or.inr hxy
    · exact (hβ.wellOrder.linear.irrefl y (hAβ y (bound hjy).1) (inc i j x y hij hix hjy y hyx)).elim

end YesMetaZFC.SetTheory.ZF
