import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax

/-! # 有限序列编号表的内部递归

一步编号表始终由有界分离构造，再由原 ZF 超限递归得到整个 ω 序列。
零层和后继层的解码不使用外部长度归纳。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

namespace ZF

/-- 任意字母表的全部内部有限序列组成实际集合。 -/
theorem fseq_space_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (X : M.Domain) :
    ∃ S, Fseq_space_d I ω X S := by
  obtain ⟨D, hD⟩ := exists_cartesianProduct hZF I ω X
  obtain ⟨U, hU⟩ := exists_powerSet hZF D
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 3))
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest (.bound 2))) }
  have hφ F : φ.denote ρ F ↔ ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I F n X := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1]
    rfl
  obtain ⟨S, hS⟩ := separation_exists_d hZF φ ρ U
  refine ⟨S, fun F => (hS F).trans ?_⟩
  rw [show Formula.satisfies (ρ.push F) φ.body ↔ _ from hφ F]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨n, hn, hF⟩ := h
  apply (hU F).mpr
  intro p hp
  obtain ⟨i, x, hc⟩ := hF.1.1 p hp
  have hi : M.PairMember I i x F := ⟨p, hc, hp⟩
  exact (hD p).mpr ⟨i, hω.transitive hZF n hn i (hF.input_mem_of_pairMember hi),
    x, hF.output_mem_of_pairMember hi, hc⟩

theorem fseq_step_exists_l (hZF : M.Models ZF) (ω X S Q J H : M.Domain) :
    ∃ K, Fseq_step_d I ω X S Q J H K := by
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (modelsKP hZF) S ω
  let ρ := (fseq_env_l ω X S Q J).push H
  let φ : BinarySchema 6 := {
    body := .conj (.mem (.bound 1) (.bound 5)) (.conj (.mem .newest (.bound 7))
      (fseq_at_m (𝒞 := 𝒞) (.bound 6) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)) }
  have hφ F z : φ.denote ρ F z ↔ M.mem F S ∧ M.mem z ω ∧ Fseq_at_d I X Q J H F z := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      fseq_at_sat_l I hZF.1]
    rfl
  obtain ⟨K, hK, hk⟩ := exists_setRelationOn_of_denote hZF I φ ρ U
  refine ⟨K, hK.1, fun F z => (hk F z).trans ?_⟩
  exact ⟨fun h => (hφ F z).mp h.2.2, fun h =>
    ⟨(hU F).mpr (Or.inl h.1), (hU z).mpr (Or.inr h.2.1), (hφ F z).mpr h⟩⟩

/-- 全部编号层统一来自一条实际 ω 递归，尚不预设编号性质。 -/
theorem fseq_recursion_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) (X S Q J : M.Domain) :
    ∃ H, M.IsRecursiveSequence I (Fseq_step_d I ω X S Q J) H ω := by
  have ho := fseq_op_l I hZF.1 ω X S Q J
  have hc : M.IsClassFunctionOnTransfiniteSequences I ((fseq_step_s (𝒞 := 𝒞)).denote (fseq_env_l ω X S Q J)) := by
    rw [ho]
    intro P _
    obtain ⟨K, hK⟩ := fseq_step_exists_l I hZF ω X S Q J P
    exact ⟨K, hK, fun L hL => hL.1.eq_of_pairMember_iff hZF.1 hK.1
      (fun F z => (hL.2 F z).trans (hK.2 F z).symm)⟩
  obtain ⟨H, hH⟩ := recursiveSequence_exists hZF I (fseq_env_l ω X S Q J) (fseq_step_s (𝒞 := 𝒞)) hc (hω.isOrdinal hZF)
  exact ⟨H, by simpa only [ho] using hH⟩

end ZF

theorem fseq_at_zero_l (hE : Extensional M) {X Q J H n} (hd : M.IsDomainOf I n H)
    (hn : ∀ i, ¬ M.mem i n) (F z : M.Domain) :
    Fseq_at_d I X Q J H F z ↔ M.IsSetFunctionFromTo I F n X ∧ ∀ i, ¬ M.mem i z := by
  constructor
  · rintro ⟨m, hm, hF, he | ⟨i, L, hi, _⟩⟩
    · have hh := hm.eq hE hd
      subst m
      exact ⟨hF, he.2⟩
    · have hh := hm.eq hE hd
      subst m
      exact (hn i hi.predecessor_mem).elim
  · exact fun ⟨hF, hz⟩ => ⟨n, hd, hF, Or.inl ⟨hn, hz⟩⟩

theorem fseq_at_succ_l (hE : Extensional M) {X Q J H n m L}
    (hd : M.IsDomainOf I n H) (hH : M.IsSetFunction I H) (hm : M.IsOrdinal m)
    (hn : M.SuccessorOf n m) (hL : M.PairMember I m L H) (F z : M.Domain) :
    Fseq_at_d I X Q J H F z ↔ M.IsSetFunctionFromTo I F n X ∧ Fseq_snoc_d I Q J L m F z := by
  constructor
  · rintro ⟨s, hs, hF, he | ⟨i, K, hi, hK, hz⟩⟩
    · have hh := hs.eq hE hd
      subst s
      exact (he.1 m hn.predecessor_mem).elim
    · have hh := hs.eq hE hd
      subst s
      have hh := hn.predecessor_eq hE hm hi
      subst i
      have hh := hH.2 m K L hK hL
      subst K
      exact ⟨hF, hz⟩
  · exact fun ⟨hF, hz⟩ => ⟨n, hd, hF, Or.inr ⟨m, L, hn, hL, hz⟩⟩

end YesMetaZFC.SetTheory
