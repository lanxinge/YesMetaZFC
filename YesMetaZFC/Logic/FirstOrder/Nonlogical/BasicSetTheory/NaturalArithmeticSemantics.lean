import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 自然减法与递归序列的逐步语义

逐对象展开递推公式，固定索引、当前值和下一值的角色。这些定理适用于任意
源模型及任意环境；后续集合存在性证明可以直接消费语义条件。
-/
namespace YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticSemantics
set_option autoImplicit false
universe x
abbrev Obj (ℳ : Structure.{0, 0, 0, x} signature) := ℳ.Carrier SetSort.set

def Mem (ℳ : Structure.{0, 0, 0, x} signature) (element set : Obj ℳ) : Prop :=
  ℳ.relInterp .membership (.cons element (.cons set .nil))
def Apply (ℳ : Structure.{0, 0, 0, x} signature) (graph input : Obj ℳ) : Obj ℳ :=
  ℳ.funcInterp .application (.cons graph (.cons input .nil))
def Succ (ℳ : Structure.{0, 0, 0, x} signature) (input : Obj ℳ) : Obj ℳ :=
  ℳ.funcInterp .successor (.cons input .nil)
def Empty (ℳ : Structure.{0, 0, 0, x} signature) : Obj ℳ := ℳ.funcInterp .emptySet .nil
def Pair (ℳ : Structure.{0, 0, 0, x} signature) (left right : Obj ℳ) : Obj ℳ :=
  ℳ.funcInterp .orderedPair (.cons left (.cons right .nil))
def Domain (ℳ : Structure.{0, 0, 0, x} signature) (graph : Obj ℳ) : Obj ℳ :=
  ℳ.funcInterp .domain (.cons graph .nil)

/-- 已到零时保持零；当前值为后继时，下一值取其前驱。 -/
def DifferenceStep (ℳ : Structure.{0, 0, 0, x} signature) (graph index : Obj ℳ) : Prop :=
  (Apply ℳ graph index = Empty ℳ ∧ Apply ℳ graph (Succ ℳ index) = Empty ℳ) ∨
    ∃ previous, Apply ℳ graph index = Succ ℳ previous ∧ Apply ℳ graph (Succ ℳ index) = previous

theorem difference_step_correct {ℳ : Structure.{0, 0, 0, x} signature} {bound free : SetContext}
    (env : Env ℳ bound free) (graph index : SetTerm bound free) :
    (natural_difference_step_condition graph index).satisfies env ↔
      DifferenceStep ℳ (graph.eval env) (index.eval env) := by
  simp only [natural_difference_step_condition, Formula.satisfies_existsFreeTop,
    Formula.satisfies, function_application_term, successor_term, empty_set_term,
    Term.eval, Arguments.eval, Term.eval_weakenFree]
  rfl

/-- 序列存储索引和值；递归器的输入存储当前值和索引。 -/
def RecursionStep (ℳ : Structure.{0, 0, 0, x} signature)
    (source seed recursion sequence : Obj ℳ) : Prop :=
  Mem ℳ (Pair ℳ (Empty ℳ) seed) sequence ∧
    ∀ index, (Mem ℳ index (Domain ℳ sequence) ∧ Mem ℳ (Succ ℳ index) (Domain ℳ sequence)) →
      ∃ current next, Mem ℳ next source ∧ Mem ℳ current source ∧
        Mem ℳ (Pair ℳ index current) sequence ∧
        Mem ℳ (Pair ℳ (Succ ℳ index) next) sequence ∧
        Mem ℳ (Pair ℳ (Pair ℳ current index) next) recursion

theorem recursion_step_correct {ℳ : Structure.{0, 0, 0, x} signature} {bound free : SetContext}
    (env : Env ℳ bound free) (source seed recursion sequence : SetTerm bound free) :
    (recursive_sequence_step_condition source seed recursion sequence).satisfies env ↔
      RecursionStep ℳ (source.eval env) (seed.eval env) (recursion.eval env) (sequence.eval env) := by
  simp only [recursive_sequence_step_condition, Formula.satisfies_forallFreeTop,
    Formula.satisfies_existsFreeTop, Formula.satisfies, membership_formula,
    ordered_pair_term, successor_term, empty_set_term, domain_term,
    Term.eval, Arguments.eval, Term.eval_weakenFree]
  rfl

end YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticSemantics
