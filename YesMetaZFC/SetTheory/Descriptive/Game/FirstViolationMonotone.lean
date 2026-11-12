import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # 非法对局总有内部最早违规

在原模型中对失败前缀的长度取最小序数，不把内部 ω 当作外部良基自然数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_first_exists_l {ω A F L f : M.Domain} (hω : M.IsOmega ω) (space : Fseq_space_d I ω A F)
    (hf : M.IsSetFunction I f) (zero : ∀ p, M.mem p F → (∀ x, ¬ M.mem x p) → M.mem p L)
    (bad : ∃ p, M.mem p F ∧ M.MemberSubset p f ∧ ¬ M.mem p L) :
    ∃ i p, M.mem p F ∧ M.MemberSubset p f ∧ Cg_first_d ω A F L i p := by
  classical
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push F).push L).push f
  let φ : UnarySchema 5 := { body := set[6] ⟪⌜(.newest : Term 6)⌝ₛ ∈ ⌜(.bound 5 : Term 6)⌝ₛ ∧
    (∃ p ∈ ⌜(.bound 3 : Term 6)⌝ₛ, ⌜fn0_m⌝ₚ(⌜(.newest : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, p) ∧
      p ⊆ ⌜(.bound 1 : Term 6)⌝ₛ ∧ ¬ (p ∈ ⌜(.bound 2 : Term 6)⌝ₛ))⟫ }
  have sat n : φ.denote ρ n ↔ M.mem n ω ∧ ∃ p, M.mem p F ∧ Fn0_d n A p ∧ M.MemberSubset p f ∧ ¬ M.mem p L := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1, Formula.satisfies_subset_iff,
      Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
    rfl
  obtain ⟨p₀, hp₀, pf₀, fail₀⟩ := bad
  obtain ⟨n₀, hn₀, fn₀⟩ := (space p₀).mp hp₀
  obtain ⟨n, _, hn, least⟩ := ZF.ordinal_min_l hZF φ ρ (hω.members_areOrdinals (ZF.modelsKP hZF) n₀ hn₀)
    ((sat n₀).mpr ⟨hn₀, p₀, hp₀, fn0_of_function_l (ZF.modelsKP hZF) fn₀, pf₀, fail₀⟩)
  obtain ⟨hn, p, hp, fn, pf, fail⟩ := (sat n).mp hn
  have nonempty : ∃ x, M.mem x n := by
    apply Classical.byContradiction
    intro no
    apply fail (zero p hp ?_)
    intro x hx
    obtain ⟨i, hi, _, _, _⟩ := fn.1 x hx
    exact no ⟨i, hi⟩
  obtain ⟨i, _, next⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn nonempty
  refine ⟨i, p, hp, pf, n, hn, fn, next, fail, fun q hq qp pq => ?_⟩
  obtain ⟨m, hm, fq⟩ := (space q).mp hq
  have qf : M.MemberSubset q f := fun x hx => pf x (qp x hx)
  have rp := (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) fn) hf).mpr pf
  have rq := (ds_restrict_iff_l I fq hf).mpr qf
  have mn : M.mem m n := by
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with eq | mn | nm
    · exact (pq (ds_prefix_mono_l I (fn0_function_l (ZF.modelsKP hZF) fn) fq.1 rp rq
        (fun x hx => (eq x).mpr hx))).elim
    · exact mn
    · exact (pq (ds_prefix_mono_l I (fn0_function_l (ZF.modelsKP hZF) fn) fq.1 rp rq
        ((hω.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n nm))).elim
  exact Classical.byContradiction (fun no => least m mn ((sat m).mpr
    ⟨hm, q, hq, fn0_of_function_l (ZF.modelsKP hZF) fq, qf, no⟩))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 只放宽本方合法步时的闭收益单调性

若另一方的违规检查没有改变，原本归本方的对局仍归本方。
证明比较同一对局的真实最早违规，不要求合法节点集合前缀封闭。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Cg_payoff_d.mono_l {ω A F L L' J B W W' f : M.Domain}
    (left : Cg_payoff_d (M := M) ω A F L J B W) (right : Cg_payoff_d (M := M) ω A F L' J B W')
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F) (ff : M.IsSetFunction I f) (hf : M.mem f B)
    (zero : ∀ p, M.mem p F → (∀ x, ¬ M.mem x p) → M.mem p L)
    (sub : M.MemberSubset L L')
    (unchanged : ∀ i j p, M.mem j ω → Fn0_d j A p → M.SuccessorOf j i →
      ¬ M.mem i J → M.mem p L' → M.mem p L) : M.mem f W → M.mem f W' := by
  intro win
  apply Classical.byContradiction
  intro no
  obtain ⟨p,i,hp,pf,hi,first⟩ := (right.read_l hf).mp no
  have bad : ¬ M.mem p L := by
    obtain ⟨_,_,_,_,bad,_⟩ := first
    exact fun h => bad (sub p h)
  obtain ⟨k,q,hq,qf,old⟩ := cg_first_exists_l hZF hw space ff zero ⟨p,hp,pf,bad⟩
  have turn : ¬ M.mem k J := fun hk => ((left.read_l hf).mpr ⟨q,k,hq,qf,hk,old⟩) win
  have old' : Cg_first_d ω A F L' k q := by
    obtain ⟨j,hj,fq,succ,bad,before⟩ := old
    exact ⟨j,hj,fq,succ,(fun h => bad (unchanged k j q hj fq succ turn h)),
      fun s hs sq qs => sub s (before s hs sq qs)⟩
  exact turn ((cg_first_unique_l (ZF.modelsKP hZF) (hw.isOrdinal (ZF.modelsKP hZF)) ff
    hp hq pf qf first old').2 ▸ hi)

end YesMetaZFC.SetTheory.Descriptive
