import YesMetaZFC.SetTheory.Descriptive.GameContinuation
import YesMetaZFC.SetTheory.Ord.Recursion

/-! # 给定有限历史之后的实际策略对局

先复制指定前缀，之后在指定玩家的时刻调用原策略，其余时刻使用给定字母。
固定目标集的序数递归直接产生模型内部 ω 列；不需要选择公理或外部标准性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_tail_play_l {ι : Bool} {ω X F J σ n s a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (strategy : Fn0_d F X σ)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ M.MemberSubset s f ∧ Cg_tail_follows_d I ι ω J s σ f := by
  classical
  let P i := if ι then ¬ M.mem i J else M.mem i J
  let opp {d} (i J : Term d) : Formula 1 d := if ι then .neg (.mem i J) else .mem i J
  have oppSat {d} (η : Env M d) (i J : Term d) : Formula.satisfies η (opp i J) ↔
      (if ι then ¬ M.mem (i.eval η) (J.eval η) else M.mem (i.eval η) (J.eval η)) := by
    cases ι <;> simp only [opp, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
  let ρ : Env M 7 := ⟨fun i => [a, σ, J, s, n, X, ω].get i, fun _ => ω⟩
  let φ : BinarySchema 7 := {
    body := set[9] ⟪∃ i ∈ ⌜(.bound 8 : Term 9)⌝ₛ,
    ⌜fn0_m⌝ₚ(i, ⌜(.bound 7 : Term 9)⌝ₛ, ⌜(.bound 1 : Term 9)⌝ₛ) ∧
    ((i ∈ ⌜(.bound 6 : Term 9)⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(i, ⌜(.newest : Term 9)⌝ₛ, ⌜(.bound 5 : Term 9)⌝ₛ)) ∨
      (¬ (i ∈ ⌜(.bound 6 : Term 9)⌝ₛ) ∧
        ((¬ (⌜opp⌝ₚ(i, ⌜(.bound 4 : Term 9)⌝ₛ)) ∧
          ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ, ⌜(.newest : Term 9)⌝ₛ, ⌜(.bound 3 : Term 9)⌝ₛ)) ∨
          (⌜opp⌝ₚ(i, ⌜(.bound 4 : Term 9)⌝ₛ) ∧ ⌜(.newest : Term 9)⌝ₛ = ⌜(.bound 2 : Term 9)⌝ₛ))))⟫
    freeClosed := by cases ι <;> simp -implicitDefEqProofs [opp, Definitional.Formula.FreeClosed] }
  have sat g v : φ.denote ρ g v ↔ ∃ i, M.mem i ω ∧ Fn0_d i X g ∧
      ((M.mem i n ∧ Rd_entry_d i v s) ∨
        (¬ M.mem i n ∧ ((¬ P i ∧ Rd_entry_d g v σ) ∨ (P i ∧ v = a)))) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1, oppSat, Definitional.Term.eval_weaken]
    rfl
  have function : M.IsClassFunctionOnSequencesInBelow I (φ.denote ρ) ω X := by
    rintro g ⟨_, i, hi, _, fg⟩
    have fg₀ := fn0_of_function_l (ZF.modelsKP hZF) fg
    have total : ∃ v, φ.denote ρ g v := by
      by_cases hin : M.mem i n
      · obtain ⟨v, _, hv⟩ := fs.2.2 i hin
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inl ⟨hin, hv⟩⟩⟩
      · by_cases hij : P i
        · exact ⟨a, (sat g a).mpr ⟨i, hi, fg₀, Or.inr ⟨hin, Or.inr ⟨hij, rfl⟩⟩⟩⟩
        · obtain ⟨v, _, hv⟩ := strategy.2.1 g ((space g).mpr ⟨i, hi, fg⟩)
          exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inr ⟨hin, Or.inl ⟨hij, hv⟩⟩⟩⟩
    obtain ⟨v, hv⟩ := total
    refine ⟨v, hv, fun w hw => ?_⟩
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp hv
    obtain ⟨l, _, fl, hl⟩ := (sat g w).mp hw
    have ek := fk.domain_eq_l hZF.1 fg₀
    have el := fl.domain_eq_l hZF.1 fg₀
    subst k l
    rcases hl with ⟨hin, hw⟩ | ⟨hn', ⟨hj', hw⟩ | ⟨hj', rfl⟩⟩
    · rcases hk with ⟨_, hv⟩ | ⟨bad, _⟩
      · exact fs.1.2 i w v hw hv
      · exact (bad hin).elim
    · rcases hk with ⟨hn, _⟩ | ⟨_, ⟨_, hv⟩ | ⟨hj, _⟩⟩
      · exact (hn' hn).elim
      · exact (fn0_function_l (ZF.modelsKP hZF) strategy).1.2 g w v hw hv
      · exact (hj' hj).elim
    · rcases hk with ⟨hn, _⟩ | ⟨_, ⟨hj, _⟩ | ⟨_, rfl⟩⟩
      · exact (hn' hn).elim
      · exact (hj hj').elim
      · rfl
  have into : M.MapsSequencesInBelowInto I (φ.denote ρ) ω X := by
    intro g v _ hv
    obtain ⟨i, _, _, ⟨_, hv⟩ | ⟨_, ⟨_, hv⟩ | ⟨_, rfl⟩⟩⟩ := (sat g v).mp hv
    · exact fs.output_mem_of_pairMember hv
    · exact (strategy.bound_l hv).2
    · exact ha
  obtain ⟨f, rec⟩ := ZF.recursiveSequenceIn_exists hZF I ρ φ
    (hω.isOrdinal hZF) (hω.isOrdinal hZF) (Or.inl rfl) function into
  have ff := rec.1.2
  have read i v (hi : M.mem i ω) (hv : Rd_entry_d i v f) : ∃ g, M.IsRestrictionOf I g f i ∧
      ((M.mem i n ∧ Rd_entry_d i v s) ∨
        (¬ M.mem i n ∧ ((¬ P i ∧ Rd_entry_d g v σ) ∨ (P i ∧ v = a)))) := by
    obtain ⟨g, hg, value⟩ := rec.2 i hi v hv
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp value
    have fi := fn0_of_function_l (ZF.modelsKP hZF) (hg.isSetFunctionFromTo ff (hω.transitive hZF i hi))
    have eq := fk.domain_eq_l hZF.1 fi
    exact ⟨g, hg, eq ▸ hk⟩
  have sub : M.MemberSubset s f := by
    intro p hp
    obtain ⟨i, v, pair⟩ := fs.1.1 p hp
    have his : Rd_entry_d i v s := ⟨p, pair, hp⟩
    have hin := fs.input_mem_of_pairMember his
    obtain ⟨w, _, hiw⟩ := ff.2.2 i (hω.transitive hZF n hn i hin)
    obtain ⟨_, _, ⟨_, hws⟩ | ⟨bad, _⟩⟩ := read i w (hω.transitive hZF n hn i hin) hiw
    · have eq := fs.1.2 i w v hws his
      obtain ⟨q, qp, hq⟩ := eq ▸ hiw
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
    · exact (bad hin).elim
  refine ⟨f, ff, sub, ?_⟩
  intro i hi turn h hr sh v hv
  obtain ⟨g, gr, ⟨hin, hsv⟩ | ⟨_, ⟨_, value⟩ | ⟨bad, _⟩⟩⟩ := read i v hi hv
  · have hhv : Rd_entry_d i v h := hsv.elim fun p hp => ⟨p, hp.1, sh p hp.2⟩
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((hr.2 i v).mp hhv).1).elim
  · exact gr.eq hZF.1 hr ▸ value
  · have hn : ¬ P i := by cases ι <;> simpa [P] using turn
    exact (hn bad).elim

end YesMetaZFC.SetTheory.Descriptive
