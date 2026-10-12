import YesMetaZFC.SetTheory.Descriptive.FirstViolation

/-! # 首次违规的唯一性及玩家 II 违规后的吸收

同一对局的两个有限前缀按包含可比较。较长的首次违规证据会把较短的
证据判为合法，故两者必须相同；无需对外部 ω 作良基归纳。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem cg_first_unique_l (hKP : M.Models KP) {ω A S L i j p q f : M.Domain}
    (hω : M.IsOrdinal ω) (hf : M.IsSetFunction (kp_pair_l hKP) f)
    (hp : M.mem p S) (hq : M.mem q S) (pf : M.MemberSubset p f) (qf : M.MemberSubset q f)
    (first : Cg_first_d ω A S L i p) (second : Cg_first_d ω A S L j q) : p = q ∧ i = j := by
  classical
  obtain ⟨m, hm, fm, sm, badp, beforep⟩ := first
  obtain ⟨n, hn, fn, sn, badq, beforeq⟩ := second
  have eq : p = q := by
    rcases ds_prefix_compare_l (kp_pair_l hKP) hKP.1 hω hm hn (fn0_function_l hKP fm)
      (fn0_function_l hKP fn) hf pf qf with pq | qp
    · have qp : M.MemberSubset q p := Classical.byContradiction (fun no => badp (beforeq p hp pq no))
      exact hKP.1.eq_of_same_members p q (fun x => ⟨pq x, qp x⟩)
    · have pq : M.MemberSubset p q := Classical.byContradiction (fun no => badq (beforep q hq qp no))
      exact hKP.1.eq_of_same_members p q (fun x => ⟨pq x, qp x⟩)
  subst q
  have lengths := fm.domain_eq_l hKP.1 fn
  subst n
  exact ⟨rfl, Structure.SuccessorOf.predecessor_eq hKP.1 ((hω.mem hm).mem sm.predecessor_mem) sm sn⟩

theorem Cg_payoff_d.ii_first_l (hKP : M.Models KP) {ω A S L J B W f p i : M.Domain}
    (payoff : Cg_payoff_d (M := M) ω A S L J B W) (hω : M.IsOrdinal ω)
    (hf : M.IsSetFunction (kp_pair_l hKP) f) (hfB : M.mem f B) (hp : M.mem p S)
    (pf : M.MemberSubset p f) (first : Cg_first_d ω A S L i p) (turn : ¬ M.mem i J) : M.mem f W := by
  apply Classical.byContradiction
  intro no
  obtain ⟨q, j, hq, qf, hj, second⟩ := (payoff.read_l hfB).mp no
  exact turn ((cg_first_unique_l hKP hω hf hp hq pf qf first second).2.symm ▸ hj)

end YesMetaZFC.SetTheory.Descriptive
