import YesMetaZFC.SetTheory.Descriptive.FirstViolationRead
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
  obtain ⟨n, _, hn, least⟩ := ZF.ordinal_min_l hZF φ ρ (hω.members_areOrdinals hZF n₀ hn₀)
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
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare m hm n hn with eq | mn | nm
    · exact (pq (ds_prefix_mono_l I (fn0_function_l (ZF.modelsKP hZF) fn) fq.1 rp rq
        (fun x hx => (eq x).mpr hx))).elim
    · exact mn
    · exact (pq (ds_prefix_mono_l I (fn0_function_l (ZF.modelsKP hZF) fn) fq.1 rp rq
        ((hω.members_areOrdinals hZF m hm).transitive n nm))).elim
  exact Classical.byContradiction (fun no => least m mn ((sat m).mpr
    ⟨hm, q, hq, fn0_of_function_l (ZF.modelsKP hZF) fq, qf, no⟩))

end YesMetaZFC.SetTheory.Descriptive
