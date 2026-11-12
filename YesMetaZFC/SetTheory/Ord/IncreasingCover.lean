import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Card.Omega

/-! # 递增集合列对内部有限参数列的统一覆盖

阶段列是实际集合函数。用它和参数列作分离参数，在模型内部 ω 上归纳，
逐次合并两个阶段界；结论包含外部非标准的有限长度，不使用选择公理。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem increasing_finite_cover_l (hZF : M.Models ZF) {ω V F Z k s : M.Domain}
    (hw : M.IsOmega ω) (stages : Fn0_d ω V F)
    (cover : ∀ x, M.mem x Z → ∃ n, M.mem n ω ∧ ∃ Y, Rd_entry_d n Y F ∧ M.mem x Y)
    (mono : ∀ n m Y T, M.mem n ω → M.mem m ω → M.MemberSubset n m →
      Rd_entry_d n Y F → Rd_entry_d m T F → M.MemberSubset Y T)
    (hk : M.mem k ω) (seq : Fn0_d k Z s) :
    ∃ n, M.mem n ω ∧ ∃ Y, Rd_entry_d n Y F ∧
      ∀ i x, M.mem i k → Rd_entry_d i x s → M.mem x Y := by
  let ρ : Env M 3 := ⟨fun i => [ω,F,s].get i,fun _ => ω⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∃ m ∈ ⌜(.bound 1 : Term 4)⌝ₛ, ∃ Y,
    ⌜rd_entry0_m⌝ₚ(m,Y,⌜(.bound 2 : Term 4)⌝ₛ) ∧ (∀ i ∈ ⌜(.newest : Term 4)⌝ₛ, ∀ x,
      ⌜rd_entry0_m⌝ₚ(i,x,⌜(.bound 3 : Term 4)⌝ₛ) → x ∈ Y)⟫ }
  have sat n : φ.denote ρ n ↔ ∃ m, M.mem m ω ∧ ∃ Y, Rd_entry_d m Y F ∧
      ∀ i x, M.mem i n → Rd_entry_d i x s → M.mem x Y := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff,rd_entry0_sat_l hZF.1,Formula.satisfies_forallMem_iff,
      Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      Definitional.Term.eval_weaken]
    exact ⟨fun ⟨m,hm,Y,my,all⟩ => ⟨m,hm,Y,my,fun i x hi => all i hi x⟩,
      fun ⟨m,hm,Y,my,all⟩ => ⟨m,hm,Y,my,fun i hi x => all i x hi⟩⟩
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hw.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z empty
      obtain ⟨o,_,ho⟩ := hw.1.1
      obtain ⟨Y,_,oy⟩ := stages.2.1 o ho
      exact (sat z).mpr ⟨o,ho,Y,oy,fun i _ hi => (empty i hi).elim⟩
    · intro n hn ih t succ
      obtain ⟨m,hm,Y,my,bound⟩ := (sat n).mp ih
      classical
      by_cases active : M.mem n k
      · obtain ⟨x,hx,nx⟩ := seq.2.1 n active
        obtain ⟨q,hq,T,qt,xt⟩ := cover x hx
        have upper : ∃ a, M.mem a ω ∧ M.MemberSubset m a ∧ M.MemberSubset q a := by
          rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm q hq with eq | mq | qm
          · exact ⟨q,hq,fun v hv => (eq v).mp hv,fun _ h => h⟩
          · exact ⟨q,hq,(hw.members_areOrdinals (ZF.modelsKP hZF) q hq).transitive m mq,fun _ h => h⟩
          · exact ⟨m,hm,fun _ h => h,(hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive q qm⟩
        obtain ⟨a,ha,ma,qa⟩ := upper
        obtain ⟨U,_,au⟩ := stages.2.1 a ha
        have yu := mono m a Y U hm ha ma my au
        have tu := mono q a T U hq ha qa qt au
        refine (sat t).mpr ⟨a,ha,U,au,fun i v hi iv => ?_⟩
        rcases (succ i).mp hi with hi | eq
        · exact yu v (bound i v hi iv)
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          have eq := seq.2.2 n active x hx v (seq.bound_l iv).2 nx iv
          exact eq ▸ tu x xt
      · refine (sat t).mpr ⟨m,hm,Y,my,fun i x hi ix => ?_⟩
        rcases (succ i).mp hi with hi | eq
        · exact bound i x hi ix
        · exact (active (hZF.1.eq_of_same_members i n eq ▸ (seq.bound_l ix).1)).elim
  exact (sat k).mp (all k hk)

end YesMetaZFC.SetTheory
