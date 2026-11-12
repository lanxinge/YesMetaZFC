import YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition

/-! # 序数的有限后继尾段

每个序数都落在零或极限序数之后的某个有限后继层。
相同尾长的两个不同序数之间容纳全部内部有限后继，供局部不可分辨点使用。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ot_tail_d (ω n ν : M.Domain) : Prop := M.mem n ω ∧ ∃ α, M.IsOrdinal α ∧
  ((∀ x, ¬ M.mem x α) ∨ M.IsLimitOrdinal α) ∧ M.IsOrdinalAddition I ν α n

def ot_tail_m {d} (ω n ν : Term d) : Formula 1 d := .conj (.mem n ω) (.existsE (.conj
  (Formula.isOrdinal .newest) (.conj
    (.disj (.forallE (.neg (.mem .newest (.bound 1)))) (Formula.isLimitOrdinal .newest))
    (Formula.isOrdinalAddition 𝒞 ν.weaken .newest n.weaken))))
derive_free_closed ot_tail_m

theorem ot_tail_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n ν : Term d) :
    Formula.satisfies ρ (ot_tail_m (𝒞 := 𝒞) ω n ν) ↔ Ot_tail_d I (ω.eval ρ) (n.eval ρ) (ν.eval ρ) := by
  simp only [ot_tail_m, Ot_tail_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isOrdinal_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_isOrdinalAddition_iff I hE, Definitional.Term.eval_weaken]
  rfl

theorem ZF.ot_tail_exists_l (hZF : M.Models ZF) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : M.IsOrdinal ν) :
    ∃ n, Ot_tail_d I ω n ν := by
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := .existsE (ot_tail_m (𝒞 := 𝒞) (.bound 2) .newest (.bound 1)) }
  have sat v : φ.denote ρ v ↔ ∃ n, Ot_tail_d I ω n v := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, ot_tail_sat_l I hZF.1]
    rfl
  apply hν.induction (fun v => ∃ n, Ot_tail_d I ω n v)
  · obtain ⟨D, cut⟩ := ZF.separation_exists_d hZF φ.neg ρ ν
    exact ⟨D, fun v => (cut v).trans (and_congr Iff.rfl (not_congr (sat v)))⟩
  · intro v hv ih
    rcases hv.classify hZF.1 with empty | ⟨u, _, next⟩ | limit
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨e, heω, v, hv, Or.inl empty, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩
    · obtain ⟨n, hn, a, ha, base, sum⟩ := ih u next.predecessor_mem
      obtain ⟨m, step, hm⟩ := hω.1.2 n hn
      exact ⟨m, hm, a, ha, base, (ZF.ordinalAddition_successor_iff hZF I
        (hω.members_areOrdinals (ZF.modelsKP hZF) n hn) step).mpr ⟨u, sum, next⟩⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨e, heω, v, hv, Or.inr limit, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩

/-- 同一有限尾长不可能在同一个相邻极限区间中出现两次。 -/
theorem ZF.ot_tail_gap_l (hZF : M.Models ZF) {ω n ν μ k β : M.Domain} (hω : M.IsOmega ω)
    (low : Ot_tail_d I ω n ν) (high : Ot_tail_d I ω n μ) (lt : M.mem ν μ)
    (hk : M.mem k ω) (sum : M.IsOrdinalAddition I β ν k) : M.mem β μ := by
  obtain ⟨hn, a, ha, za, sa⟩ := low
  obtain ⟨_, b, hb, zb, sb⟩ := high
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have om := ZF.ordinalAddition_isOrdinal hZF I hb on sb
  have ab : M.mem a b := by
    rcases ha.trichotomy hZF.1 hb (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) a b) with eq | ab | ba
    · have eq := hZF.1.eq_of_same_members a b eq
      subst b
      obtain ⟨v, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I a on
      have eq := (unique ν sa).trans (unique μ sb).symm
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) μ (eq ▸ lt)).elim
    · exact ab
    · have ma : M.mem μ a := za.elim (fun h => (h b ba).elim)
        (fun h => ZF.oa_finite_bound_l hZF I hω h ba hn sb)
      have mn := ZF.ordinalAddition_left_member_mem_value hZF I ha on ma sa
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) μ (om.transitive ν lt μ mn)).elim
  have limit : M.IsLimitOrdinal b := zb.elim (fun h => (h a ab).elim) id
  have nb := ZF.oa_finite_bound_l hZF I hω limit ab hn sa
  exact ZF.ordinalAddition_left_member_mem_value hZF I hb on
    (ZF.oa_finite_bound_l hZF I hω limit nb hk sum) sb

end YesMetaZFC.SetTheory
