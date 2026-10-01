import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 有限序列编号的单射性

前缀限制和末项唯一；自然数对编号的单射性反向恢复这两个组件，从而恢复
原序列。把这一纸面证明放进实际分离公式的 ω 归纳，得到所有内部长度的编号。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem fseq_snoc_unique_l (hE : Extensional M) {Q J L m F z w}
    (hQ : M.IsSetFunction I Q) (hJ : M.IsSetFunction I J) (hL : M.IsSetFunction I L)
    (hF : M.IsSetFunction I F) (hz : Fseq_snoc_d I Q J L m F z) (hw : Fseq_snoc_d I Q J L m F w) : z = w := by
  obtain ⟨P, x, hP, hx, a, b, p, ha, hb, hp, hz⟩ := hz
  obtain ⟨T, y, hT, hy, c, d, q, hc, hd, hq, hw⟩ := hw
  have he := hP.eq hE hT
  subst T
  have he := hF.2 m x y hx hy
  subst y
  have he := hL.2 P a c ha hc
  subst c
  have he := hQ.2 x b d hb hd
  subst d
  have he := I.unique hp hq
  subst q
  exact hJ.2 p z w hz hw

theorem fseq_snoc_injective_l (hE : Extensional M) {Q J L A X W ω m n F G z}
    (hQ : M.IsSetInjectionFromTo I Q X ω) (hJ : M.IsSetInjectionFromTo I J W ω)
    (hL : M.IsSetInjectionFromTo I L A ω) (hn : M.IsOrdinal n) (hs : M.SuccessorOf n m)
    (hF : M.IsSetFunctionFromTo I F n X) (hG : M.IsSetFunctionFromTo I G n X)
    (hz : Fseq_snoc_d I Q J L m F z) (hw : Fseq_snoc_d I Q J L m G z) : F = G := by
  obtain ⟨P, x, hP, hx, a, b, p, ha, hb, hp, hz⟩ := hz
  obtain ⟨T, y, hT, hy, c, d, q, hc, hd, hq, hw⟩ := hw
  have he := hJ.2 p q z hz hw
  subst q
  obtain ⟨he, hf⟩ := I.injective hp hq
  subst c
  subst d
  have hx' := hQ.2 x y b hb hd
  subst y
  exact Structure.IsSequenceOfLength.eq_of_restriction_eq_of_last hE
    ⟨hn, hF.1, hF.2.1⟩ ⟨hn, hG.1, hG.2.1⟩ hs hs hP hT (hL.2 P T a ha hc) hx hy

namespace ZF

theorem fseq_snoc_total_l (hZF : M.Models ZF) {ω X W Q J L A m n F}
    (hW : M.IsCartesianProduct I W ω ω) (hQ : M.IsSetFunctionFromTo I Q X ω)
    (hJ : M.IsSetFunctionFromTo I J W ω) (hA : M.IsFunctionSpace I A m X)
    (hL : M.IsSetFunctionFromTo I L A ω) (hs : M.SuccessorOf n m) (hF : M.IsSetFunctionFromTo I F n X) :
    ∃ z, M.mem z ω ∧ Fseq_snoc_d I Q J L m F z := by
  obtain ⟨P, hP⟩ := exists_restriction hZF I F m
  have hm : M.MemberSubset m n := fun i hi => (hs i).mpr (Or.inl hi)
  obtain ⟨a, ha, hPa⟩ := hL.2.2 P ((hA P).mpr (hP.isSetFunctionFromTo hF hm))
  obtain ⟨x, hx, hFx⟩ := hF.2.2 m hs.predecessor_mem
  obtain ⟨b, hb, hxb⟩ := hQ.2.2 x hx
  obtain ⟨p, hp⟩ := I.total a b
  obtain ⟨z, hz, hpz⟩ := hJ.2.2 p ((hW p).mpr ⟨a, ha, b, hb, hp⟩)
  exact ⟨z, hz, P, x, hP, hFx, a, b, p, hPa, hxb, hp, hpz⟩

/-- 同一内部递归表在每个内部自然数层都给出实际单射 X^n → ω。 -/
theorem fseq_numbering_l (hZF : M.Models ZF) {ω X S W Q J H}
    (hω : M.IsOmega ω) (hS : Fseq_space_d I ω X S) (hW : M.IsCartesianProduct I W ω ω)
    (hQ : M.IsSetInjectionFromTo I Q X ω) (hJ : M.IsSetInjectionFromTo I J W ω)
    (hH : M.IsRecursiveSequence I (Fseq_step_d I ω X S Q J) H ω) :
    ∀ n, M.mem n ω → ∀ K, M.PairMember I n K H →
      ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A ω := by
  let ρ : Env M 3 := ((⟨fun _ => H, fun _ => H⟩ : Env M 1).push X).push ω
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.existsE
      (.conj (Formula.isFunctionSpace 𝒞 .newest (.bound 2) (.bound 4))
        (Formula.isInjectionFromTo 𝒞 (.bound 1) .newest (.bound 3)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, Formula.isFunctionSpace] }
  have hφ n : φ.denote ρ n ↔ ∀ K, M.PairMember I n K H →
      ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A ω := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isFunctionSpace_iff I hZF.1, Formula.satisfies_isInjectionFromTo_iff I hZF.1]
    rfl
  apply hω.induction (fun n => ∀ K, M.PairMember I n K H →
    ∃ A, M.IsFunctionSpace I A n X ∧ M.IsSetInjectionFromTo I K A ω)
  · obtain ⟨D, hD⟩ := separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro n hn K hK
    -- 零层只有空函数，统一编号为内部零。
    have hnω := (hH.1.2.2 n).mpr ⟨K, hK⟩
    obtain ⟨P, hP, hStep⟩ := hH.2 n hnω K hK
    have hd := (hH.restriction hnω hP).1.2.2
    have he F z : M.PairMember I F z K ↔ M.mem F S ∧ M.mem z ω ∧
        M.IsSetFunctionFromTo I F n X ∧ ∀ i, ¬ M.mem i z :=
      (hStep.2 F z).trans (and_congr_right fun _ => and_congr_right fun _ => fseq_at_zero_l I hZF.1 hd hn F z)
    obtain ⟨A, hA⟩ := exists_functionSpace hZF I n X
    have total F (hF : M.mem F A) : ∃ z, M.mem z ω ∧ M.PairMember I F z K :=
      ⟨n, hnω, (he F n).mpr ⟨(hS F).mpr ⟨n, hnω, (hA F).mp hF⟩, hnω, (hA F).mp hF, hn⟩⟩
    refine ⟨A, hA, ⟨⟨hStep.1, ?_⟩, ?_, total⟩, ?_⟩
    · intro F z w hz hw
      exact hZF.1.eq_of_same_members z w (fun i => iff_of_false (((he F z).mp hz).2.2.2 i) (((he F w).mp hw).2.2.2 i))
    · intro F
      exact ⟨fun h => (total F h).elim fun z hz => ⟨z, hz.2⟩,
        fun ⟨z, hz⟩ => (hA F).mpr ((he F z).mp hz).2.2.1⟩
    · intro F G z hz hw
      have hf := ((he F z).mp hz).2.2.1
      have hg := ((he G z).mp hw).2.2.1
      exact hf.1.1.eq_of_pairMember_iff hZF.1 hg.1.1 (fun i x =>
        iff_of_false (fun h => hn i (hf.input_mem_of_pairMember h)) (fun h => hn i (hg.input_mem_of_pairMember h)))
  · intro m hm ih n hn K hK
    -- 后继层先限制到 m，再用固定的 J 合并前缀与末项编号。
    have hnω := (hH.1.2.2 n).mpr ⟨K, hK⟩
    obtain ⟨P, hP, hStep⟩ := hH.2 n hnω K hK
    have hd := (hH.restriction hnω hP).1.2.2
    obtain ⟨L, hL⟩ := (hH.1.2.2 m).mp hm
    obtain ⟨A, hA, hInj⟩ := ih L hL
    have hLP := (hP.2 m L).mpr ⟨hn.predecessor_mem, hL⟩
    have he F z : M.PairMember I F z K ↔ M.mem F S ∧ M.mem z ω ∧
        M.IsSetFunctionFromTo I F n X ∧ Fseq_snoc_d I Q J L m F z :=
      (hStep.2 F z).trans (and_congr_right fun _ => and_congr_right fun _ =>
        fseq_at_succ_l I hZF.1 hd (hP.isSetFunction hH.1.2.1) (hω.members_areOrdinals hZF m hm) hn hLP F z)
    obtain ⟨B, hB⟩ := exists_functionSpace hZF I n X
    have total F (hF : M.mem F B) : ∃ z, M.mem z ω ∧ M.PairMember I F z K := by
      obtain ⟨z, hz, hf⟩ := fseq_snoc_total_l I hZF hW hQ.1 hJ.1 hA hInj.1 hn ((hB F).mp hF)
      exact ⟨z, hz, (he F z).mpr ⟨(hS F).mpr ⟨n, hnω, (hB F).mp hF⟩, hz, (hB F).mp hF, hf⟩⟩
    refine ⟨B, hB, ⟨⟨hStep.1, ?_⟩, ?_, total⟩, ?_⟩
    · intro F z w hz hw
      have hf := (he F z).mp hz
      exact fseq_snoc_unique_l I hZF.1 hQ.1.1 hJ.1.1 hInj.1.1 hf.2.2.1.1 hf.2.2.2 ((he F w).mp hw).2.2.2
    · intro F
      exact ⟨fun h => (total F h).elim fun z hz => ⟨z, hz.2⟩,
        fun ⟨z, hz⟩ => (hB F).mpr ((he F z).mp hz).2.2.1⟩
    · intro F G z hz hw
      have hf := (he F z).mp hz
      have hg := (he G z).mp hw
      exact fseq_snoc_injective_l I hZF.1 hQ hJ hInj (hω.members_areOrdinals hZF n hnω) hn
        hf.2.2.1 hg.2.2.1 hf.2.2.2 hg.2.2.2

end ZF
end YesMetaZFC.SetTheory
