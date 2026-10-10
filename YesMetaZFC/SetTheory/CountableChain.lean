import YesMetaZFC.SetTheory.CountableClub
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable

/-! # 内部递增链的有限参数截取

相邻阶段包含关系经实际公式的自然数归纳扩展到全部阶段；任意内部有限参数列
若取值于链的并，则已取值于某个阶段。两项只需 ZF，不枚举外部标准长度。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Structure.IsSetFunctionFromTo.mono_target_l {F A B C}
    (hF : M.IsSetFunctionFromTo I F A B) (h : M.MemberSubset B C) : M.IsSetFunctionFromTo I F A C :=
  ⟨hF.1, hF.2.1, fun i hi => (hF.2.2 i hi).elim fun x hx => ⟨x, h x hx.1, hx.2⟩⟩

namespace ZF

theorem cc_increasing_of_successor_l (hZF : M.Models ZF) {ω P Q} (hω : M.IsOmega ω)
    (hQ : M.IsSetFunctionFromTo I Q ω P)
    (hs : ∀ i j A B, M.SuccessorOf j i → M.PairMember I i A Q → M.PairMember I j B Q → M.MemberSubset A B) :
    Cc_increasing_d I Q := by
  let φ : BinarySchema 0 := { body := Formula.subset (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Q⟩
  have hφ x y : φ.denote ρ x y ↔ M.MemberSubset x y := Formula.satisfies_subset_iff _ _ _
  have hm := rel_chain_l I hZF φ ρ hω hQ
    (fun x y z _ _ _ hx hy => (hφ x z).mpr (fun t ht => (hφ y z).mp hy t ((hφ x y).mp hx t ht)))
    (fun i j x y hj hx hy => (hφ x y).mpr (hs i j x y hj hx hy))
  exact fun i j x y hij hx hy => (hφ x y).mp (hm i j x y hij hx hy)

/-- 内部有限参数列在递增链的并中，等价于它已落在某个阶段；此处给出所需方向。 -/
theorem cc_fseq_bound_l (hZF : M.Models ZF) {ω P Q N} (hω : M.IsOmega ω)
    (hQ : M.IsSetFunctionFromTo I Q ω P) (hm : Cc_increasing_d I Q) (hu : Cc_union_d I Q N)
    {n F} (hn : M.mem n ω) (hF : M.IsSetFunctionFromTo I F n N) :
    ∃ j B, M.PairMember I j B Q ∧ M.IsSetFunctionFromTo I F n B := by
  let ρ : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push N
  let φ : UnarySchema 2 := {
    body := .forallE (.imp (Formula.isFunctionFromTo 𝒞 .newest (.bound 1) (.bound 2))
      (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 5))
        (Formula.isFunctionFromTo 𝒞 (.bound 2) (.bound 3) .newest))))) }
  have hφ n : φ.denote ρ n ↔ ∀ F, M.IsSetFunctionFromTo I F n N →
      ∃ j B, M.PairMember I j B Q ∧ M.IsSetFunctionFromTo I F n B := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  have merge {j k B C} (hB : M.PairMember I j B Q) (hC : M.PairMember I k C Q) :
      ∃ l D, M.PairMember I l D Q ∧ M.MemberSubset B D ∧ M.MemberSubset C D := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare j (hQ.input_mem_of_pairMember hB)
        k (hQ.input_mem_of_pairMember hC) with he | hjk | hkj
    · have he := hZF.1.eq_of_same_members j k he
      subst k
      have he := hQ.1.2 j C B hC hB
      subst C
      exact ⟨j, B, hB, fun _ h => h, fun _ h => h⟩
    · exact ⟨k, C, hC, hm j k B C hjk hB hC, fun _ h => h⟩
    · exact ⟨j, B, hB, fun _ h => h, hm k j C B hkj hC hB⟩
  apply hω.induction (fun n => ∀ F, M.IsSetFunctionFromTo I F n N →
    ∃ j B, M.PairMember I j B Q ∧ M.IsSetFunctionFromTo I F n B) ?_ ?_ ?_ n hn F hF
  · obtain ⟨D, hD⟩ := separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro e he F hf
    obtain ⟨i, _, hi⟩ := hω.1.1
    obtain ⟨B, _, hB⟩ := hQ.2.2 i hi
    exact ⟨i, B, hB, hf.1, hf.2.1, fun k hk => (he k hk).elim⟩
  · intro m _ ih n hn F hf
    obtain ⟨G, hG⟩ := exists_restriction hZF I F m
    have hg := hG.isSetFunctionFromTo hf (fun i hi => (hn i).mpr (Or.inl hi))
    obtain ⟨j, B, hB, hgB⟩ := ih G hg
    obtain ⟨x, hx, hFx⟩ := hf.2.2 m hn.predecessor_mem
    obtain ⟨k, C, hC, hxC⟩ := (hu x).mp hx
    obtain ⟨l, D, hD, hBD, hCD⟩ := merge hB hC
    refine ⟨l, D, hD, hf.1, hf.2.1, fun i hi => ?_⟩
    obtain ⟨y, _, hy⟩ := hf.2.2 i hi
    refine ⟨y, ?_, hy⟩
    rcases (hn i).mp hi with hi | hi
    · exact hBD y (hgB.output_mem_of_pairMember ((hG.2 i y).mpr ⟨hi, hy⟩))
    · have he := hZF.1.eq_of_same_members i m hi
      subst i
      exact (hf.1.2 m x y hFx hy) ▸ hCD x hxC

end ZF
end YesMetaZFC.SetTheory
