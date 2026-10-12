import YesMetaZFC.Model.SetTheory.Internal.TransitiveFunctionFormula
import YesMetaZFC.Model.SetTheory.Internal.TransitiveCardinal

/-! # 共尾公式在传递集合中的精确读取

函数与坐标无需额外闭包。原共尾公式唯一额外的存在见证是值域集合；
将其所有权显式列出，便可同时处理任意后继秩层及极限秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
include hKP hX
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l hKP

theorem rt_ordinal_sequence_formula_l {d} (ρ : Env N d) (f n : Term d) :
    Formula.satisfies ρ (Formula.isOrdinalValuedSequence kpair_convention_l f n) ↔
      M.IsOrdinalValuedSequence I (f.eval ρ).val (n.eval ρ).val := by
  simp only [Formula.isOrdinalValuedSequence, Formula.isSequenceOfLength, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP,
    rt_function_formula_l hX nx hKP.1 (KP.exists_pair hKP), rt_domain_formula_l hX nx hKP.1 (KP.exists_pair hKP),
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl ⟨fun h a ha b hab => ?_, fun h a ha b hab => ?_⟩
  · have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
    exact h ⟨a, ab.1⟩ ha ⟨b, ab.2⟩ hab
  · exact h a.val ha b.val hab

theorem rt_increasing_formula_l {d} (ρ : Env N d) (f n : Term d) :
    Formula.satisfies ρ (Formula.isIncreasingOrdinalSequence kpair_convention_l f n) ↔
      M.IsIncreasingOrdinalSequence I (f.eval ρ).val (n.eval ρ).val := by
  simp only [Formula.isIncreasingOrdinalSequence, Formula.satisfies_conj_iff,
    rt_ordinal_sequence_formula_l hKP hX nx, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    rt_entry_formula_l hX nx hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push]
  refine and_congr Iff.rfl ⟨fun h a ha b hb hab x y hx hy => ?_, fun h a ha b hb hab x y hh => ?_⟩
  · have ax := rd_entry_transitive_l hX (f.eval ρ).property hx
    have by' := rd_entry_transitive_l hX (f.eval ρ).property hy
    exact h ⟨a, ax.1⟩ ha ⟨b, by'.1⟩ hb hab ⟨x, ax.2⟩ ⟨y, by'.2⟩ ⟨hx, hy⟩
  · exact h a.val ha b.val hb hab x.val y.val hh.1 hh.2

theorem rt_cofinal_formula_l {d} (ρ : Env N d) (f n k : Term d) :
    Formula.satisfies ρ (Formula.isCofinalOrdinalSequence kpair_convention_l f n k) ↔
      M.IsCofinalOrdinalSequence I (f.eval ρ).val (n.eval ρ).val (k.eval ρ).val ∧
        ∃ R, M.mem R X ∧ M.IsRangeOf I R (f.eval ρ).val := by
  simp only [Formula.isCofinalOrdinalSequence, Formula.isOrdinalSequenceLimit, Formula.satisfies_conj_iff,
    Formula.satisfies_isLimitOrdinal_iff, rt_limit_l hX nx hKP,
    rt_increasing_formula_l hKP hX nx, rt_ordinal_sequence_formula_l hKP hX nx,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP, Formula.satisfies_exists_iff,
    rt_range_formula_l hX nx hKP.1 (KP.exists_pair hKP), Formula.satisfies_isUnion_iff, rt_union_l hX nx,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hKP.1, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · rintro ⟨hk, inc, ⟨ord, vals, R, range, union⟩, bound⟩
    refine ⟨⟨hk, inc, ⟨ord, vals, R.val, range, union⟩, fun a ha b hab => ?_⟩, R.val, R.property, range⟩
    have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
    exact bound ⟨a, ab.1⟩ ha ⟨b, ab.2⟩ hab
  · rintro ⟨h, R, hR, range⟩
    exact ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.1, ⟨R, hR⟩, range,
      (h.range_isCofinalSubset hKP.1 range).2.2⟩, fun a ha b hab => h.2.2.2 a.val ha b.val hab⟩

/-- 基数性向下成立；被子模型量化的任何反例图均可原样读回。 -/
theorem rt_cardinal_formula_l {d} (ρ : Env N d) (k : Term d) (h : M.IsCardinal I (k.eval ρ).val) :
    Formula.satisfies ρ (Formula.isCardinal kpair_convention_l k) := by
  simp only [Formula.isCardinal, Formula.equinumerous, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
    rt_bijection_formula_l hX nx hKP.1 (KP.exists_pair hKP), Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  exact ⟨h.1, fun a ha ⟨f, hf⟩ => h.2 a.val ha ⟨f.val, hf⟩⟩

end YesMetaZFC.SetTheory.Internal
