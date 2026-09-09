import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem
import YesMetaZFC.SetTheory.Definitional.Project.Syntax

/-!
# Project 语法的内在 FormalSystem 嵌入

项目语法的 bound 深度与 FormalSystem 的 bound 上下文一一对应。这里仅翻译自由闭合
项目项和公式；自由变量不存在时，目标 free 上下文固定为空，因而 Quine 编码可以
直接得到闭合对象项，不需要旧层的 `Admissible`、名字或 token 序列。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory

open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project

set_option autoImplicit false

/-- Project 深度 `depth` 对应的单排序 FormalSystem bound 上下文。 -/
abbrev project_bound_context (depth : Nat) : SetContext :=
  List.replicate depth SetSort.set

/-- 将 Project 的 `Fin` bound 位置直接转成内在变量；逐步匹配索引，避免归纳型 cases 重复计算。 -/
def project_bound_variable :
    {depth : Nat} → Fin depth →
      Variable (project_bound_context depth) SetSort.set
  | 0, entry => Fin.elim0 entry
  | _depth + 1, ⟨0, _⟩ => Variable.here
  | _depth + 1, ⟨index + 1, hIndex⟩ =>
      Variable.there (project_bound_variable ⟨index, Nat.lt_of_succ_lt_succ hIndex⟩)

@[simp] theorem project_bound_variable_zero {depth : Nat} :
    project_bound_variable (0 : Fin (depth + 1)) = Variable.here := rfl

@[simp] theorem project_bound_variable_succ {depth : Nat} (entry : Fin depth) :
    project_bound_variable entry.succ = Variable.there (project_bound_variable entry) := by
  cases entry
  rfl

/-- 单排序 Project 上下文中的变量排序必为集合排序。 -/
theorem project_bound_variable_sort
    {depth : Nat} {sort : SetSort}
    (entry : Variable (project_bound_context depth) sort) :
    sort = SetSort.set := by
  cases depth with
  | zero => cases entry
  | succ depth =>
      cases entry with
      | here => rfl
      | there previous =>
          exact project_bound_variable_sort previous

/-- 单排序内在变量对应的 Project `Fin` 位置。 -/
def project_bound_index
    {depth : Nat} {sort : SetSort}
    (entry : Variable (project_bound_context depth) sort) : Fin depth :=
  ⟨entry.index, by
    simpa [project_bound_context] using entry.index_lt_length⟩

@[simp] theorem project_bound_index_variable
    {depth : Nat} (entry : Fin depth) :
    project_bound_index (project_bound_variable entry) = entry := by
  apply Fin.ext
  induction depth with
  | zero => exact Fin.elim0 entry
  | succ depth ih =>
      refine Fin.cases ?_ (fun previous => ?_) entry
      · rfl
      · simpa [project_bound_index, project_bound_variable,
          Variable.index] using ih previous

/-- 将 Project 的 `Fin` 重命名提升为内在保排序变量重命名。 -/
def project_bound_renaming
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    VariableRenaming (project_bound_context sourceDepth)
      (project_bound_context targetDepth) := by
  intro sort entry
  have hSort : sort = SetSort.set := project_bound_variable_sort entry
  subst sort
  exact project_bound_variable (indexMap (project_bound_index entry))

@[simp] theorem project_bound_renaming_variable
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (entry : Fin sourceDepth) :
    project_bound_renaming indexMap (project_bound_variable entry) =
      project_bound_variable (indexMap entry) := by
  simp [project_bound_renaming]

/-- Project 重命名穿过一个 binder 时的有限位置映射。 -/
def project_lift_index_map
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    Fin (sourceDepth + 1) → Fin (targetDepth + 1) :=
  Fin.cases 0 fun entry => (indexMap entry).succ

theorem project_lift_substitution_eq
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    _root_.YesMetaZFC.SetTheory.Definitional.Term.liftSubstitution
        (.bound ∘ indexMap) =
      (.bound ∘ project_lift_index_map indexMap) := by
  funext entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · rfl
  · rfl

theorem project_bound_renaming_lift
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    (project_bound_renaming (project_lift_index_map indexMap) :
      VariableRenaming
        (SetSort.set :: project_bound_context sourceDepth)
        (SetSort.set :: project_bound_context targetDepth)) =
      (VariableRenaming.lift (introduced := SetSort.set)
        (project_bound_renaming indexMap) :
        VariableRenaming
          (SetSort.set :: project_bound_context sourceDepth)
          (SetSort.set :: project_bound_context targetDepth)) := by
  funext sort entry
  cases sort
  cases entry with
  | here =>
      simp [project_bound_renaming, project_bound_index,
        project_lift_index_map,
        VariableRenaming.lift, Variable.index]
  | there previous =>
      simp [project_bound_renaming, project_bound_index,
        project_lift_index_map,
        VariableRenaming.lift, Variable.index]

/-- 自由闭合 Project 项的内在翻译。 -/
def project_term {depth : Nat}
    (term : Project.Term depth)
    (hClosed : term.freeSupport = []) :
    SetTerm (project_bound_context depth) [] :=
  match term with
  | .bound entry =>
      .bvar (project_bound_variable entry)
  | .free id => by
      change id :: [] = [] at hClosed
      cases hClosed

theorem project_term_rename
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (term : Project.Term sourceDepth)
    (hClosed : term.freeSupport = []) :
    project_term (Project.Term.rename indexMap term) (by simpa using hClosed) =
      (project_term term hClosed).renameMapped
        (project_bound_renaming indexMap) VariableRenaming.id := by
  cases term with
  | bound entry =>
      change
        (.bvar (project_bound_variable (indexMap entry)) :
          SetTerm (project_bound_context targetDepth) []) =
        .bvar
          (project_bound_renaming indexMap
            (project_bound_variable entry))
      rw [project_bound_renaming_variable]
  | free id =>
      cases hClosed

theorem project_term_bind_bound
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (term : Project.Term sourceDepth)
    (hClosed : term.freeSupport = []) :
    project_term
        (_root_.YesMetaZFC.SetTheory.Definitional.Term.bind
          (.bound ∘ indexMap) term)
          (by
            have hSupport :=
              _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport_bind_of_closed
                (.bound ∘ indexMap)
                (by intro entry; rfl) term
            exact hSupport.trans hClosed) =
      (project_term term hClosed).renameMapped
        (project_bound_renaming indexMap) VariableRenaming.id := by
  change project_term (Project.Term.rename indexMap term) _ = _
  exact project_term_rename indexMap term hClosed

/-- Project 隶属原子的 FormalSystem 版本。 -/
def project_mem {bound : SetContext}
    (left right : SetTerm bound []) : SetFormula bound [] :=
  .rel RelationSymbol.membership
    (.cons left (.cons right .nil))

/-- 自由闭合 Project 公式的内在翻译。 -/
def project_formula :
    {availableStage depth : Nat} →
      (formula : Project.Formula availableStage depth) →
      formula.FreeClosed →
        SetFormula (project_bound_context depth) []
  | _, _, .falsum, _ =>
      .falsum
  | _, _, .truth, _ =>
      .truth
  | _, _, .mem left right, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact project_mem
        (project_term left hClosed.1)
        (project_term right hClosed.2)
  | _, _, .atom .extensionalEq _ arguments, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .equal
        (project_term (arguments 0) (hClosed 0))
        (project_term (arguments 1) (hClosed 1))
  | _, _, .atom .subset _ arguments, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact subset_formula
        (project_term (arguments 0) (hClosed 0))
        (project_term (arguments 1) (hClosed 1))
  | _, _, .neg body, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .neg (project_formula body hClosed)
  | _, _, .conj left right, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .conj
        (project_formula left hClosed.1)
        (project_formula right hClosed.2)
  | _, _, .disj left right, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .disj
        (project_formula left hClosed.1)
        (project_formula right hClosed.2)
  | _, _, .imp left right, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .imp
        (project_formula left hClosed.1)
        (project_formula right hClosed.2)
  | _, _, .iff left right, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .iff
        (project_formula left hClosed.1)
        (project_formula right hClosed.2)
  | _, _, .forallE body, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .forallE SetSort.set (project_formula body hClosed)
  | _, _, .existsE body, hClosed => by
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      exact .existsE SetSort.set (project_formula body hClosed)

theorem project_formula_rename
    {availableStage sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (formula : Project.Formula availableStage sourceDepth)
    (hClosed : formula.FreeClosed) :
    project_formula (formula.rename indexMap) (by simpa using hClosed) =
    (project_formula formula hClosed).renameMapped
        (project_bound_renaming indexMap) VariableRenaming.id := by
  induction formula generalizing targetDepth <;>
    simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
  all_goals simp only [
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
    project_formula, project_mem, Formula.renameMapped]
  case atom symbol hStage arguments hClosed =>
    cases symbol <;>
      have hLeft := project_term_bind_bound indexMap (arguments 0) (hClosed 0) <;>
      have hRight := project_term_bind_bound indexMap (arguments 1) (hClosed 1) <;>
      simp [project_formula,
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
        Formula.renameMapped, Arguments.renameMapped, hLeft, hRight]
  all_goals simp_all [
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
    Arguments.renameMapped, project_term_bind_bound,
    project_lift_substitution_eq, project_bound_renaming_lift]

/-- Project 句子的 FormalSystem 闭句像。 -/
def project_sentence (sentence : Project.Sentence) : SetSentence :=
  project_formula sentence.formula sentence.freeClosed

/-- Project 句子的直接 Quine 结构码。 -/
def project_sentence_code (sentence : Project.Sentence) : Code :=
  fs_quote (project_sentence sentence)

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
