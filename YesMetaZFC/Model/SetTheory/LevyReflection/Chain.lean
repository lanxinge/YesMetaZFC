import YesMetaZFC.Model.SetTheory.LevyReflection.Step

/-! # 反射增长步的模型内 ω 递归

以已证明全定义且唯一的增长步作类递归。递归图和值域均由原 ZF 构造，归纳
长度是模型自身的 ω，不能替换成宿主的自然数序列。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def lr_iter_s (Φ : Lr_family) : BinarySchema 1 := {
  body := .disj (.conj (Formula.isZeroLengthSequence 𝒞 (.bound 1)) (Formula.extensionalEq .newest (.bound 2)))
    (.disj (.existsE (.conj (Formula.isSuccessorLengthSequenceWithLast 𝒞 (.bound 2) .newest)
      (lr_next_m (𝒞 := 𝒞) Φ .newest (.bound 1))))
      (Formula.isLimitLengthSequenceWithUnion 𝒞 (.bound 1) .newest)) }

theorem lr_iter_sat_l (hE : Extensional M) (Φ : Lr_family) (ρ : Env M 1) (s y : M.Domain) :
    (lr_iter_s (𝒞 := 𝒞) Φ).denote ρ s y ↔
      M.IsZeroSuccessorLimitStep I (fun x => x = ρ.bound 0) (Lr_next_d I Φ) s y := by
  simp only [lr_iter_s, BinarySchema.denote, Structure.IsZeroSuccessorLimitStep,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isZeroLengthSequence_iff I hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff I hE, lr_next_sat_l I hE,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff I hE]
  rfl

theorem ZF.lr_chain_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (Φ : Lr_family) (A : M.Domain) :
    ∃ P Q, M.IsSetFunctionFromTo I Q ω P ∧
      (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e A Q) ∧
      ∀ i j X Y, M.SuccessorOf j i → M.PairMember I i X Q → M.PairMember I j Y Q → Lr_next_d I Φ X Y := by
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  have ht := zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences hZF I (fun x => x = A)
    (Lr_next_d I Φ) ⟨A, rfl, fun _ h => h⟩ (fun X => by
      obtain ⟨Y, hy⟩ := lr_next_exists_l I hZF hω Φ X
      exact ⟨Y, hy, fun Z hz => hz.unique_l I hZF hy⟩)
  have hop : M.IsClassFunctionOnTransfiniteSequences I ((lr_iter_s (𝒞 := 𝒞) Φ).denote ρ) := by
    intro s hs
    obtain ⟨x, hx, hu⟩ := ht s hs
    exact ⟨x, (lr_iter_sat_l I hZF.1 Φ ρ s x).mpr hx,
      fun y hy => hu y ((lr_iter_sat_l I hZF.1 Φ ρ s y).mp hy)⟩
  obtain ⟨Q, hQ⟩ := recursiveSequence_exists hZF I ρ (lr_iter_s Φ) hop (hω.isOrdinal hZF)
  obtain ⟨P, hP⟩ := exists_range_of_setFunction hZF I hQ.1.2.1 hQ.1.2.2
  refine ⟨P, Q, ⟨hQ.1.2.1, hQ.1.2.2, fun i hi => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hQ.1.2.2 i).mp hi
    exact ⟨x, (hP x).mpr ⟨i, hx⟩, hx⟩
  · intro e he
    obtain ⟨e', he', heω⟩ := hω.1.1
    have heq := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he x))
    subst e'
    obtain ⟨x, hx⟩ := (hQ.1.2.2 e).mp heω
    obtain ⟨s, hs, hsx⟩ := hQ.2 e heω x hx
    have hs0 : M.IsZeroLengthSequence I s := ⟨e, hQ.1.restriction heω hs, he⟩
    rcases (lr_iter_sat_l I hZF.1 Φ ρ s x).mp hsx with hz | ⟨y, hy, _⟩ | hl
    · have hxA : x = A := hz.2
      exact hxA ▸ hx
    · exact (hs0.not_successorLength hZF.1 hy).elim
    · exact (hs0.not_limitLength hZF.1 hl).elim
  · intro i j X Y hij hi hj
    have hjω := (hQ.1.2.2 j).mpr ⟨Y, hj⟩
    obtain ⟨s, hs, hsy⟩ := hQ.2 j hjω Y hj
    have hsl : M.IsSuccessorLengthSequenceWithLast I s X :=
      ⟨i, hQ.1.1.mem ((hQ.1.2.2 i).mpr ⟨X, hi⟩), j, hij, hQ.1.restriction hjω hs,
        (hs.2 i X).mpr ⟨hij.predecessor_mem, hi⟩⟩
    rcases (lr_iter_sat_l I hZF.1 Φ ρ s Y).mp hsy with hz | ⟨Z, hz, hnext⟩ | hl
    · exact (hz.1.not_successorLength hZF.1 hsl).elim
    · exact hz.last_eq hZF.1 hsl ▸ hnext
    · exact (hsl.not_limitLength hZF.1 hl).elim

end YesMetaZFC.SetTheory
