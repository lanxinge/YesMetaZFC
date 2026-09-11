import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.BoundRenaming
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Foundation

/-!
# 结构语法的统一变换与自由出现

本模块在按深度索引的结构码上定义一个公共递归图：

* `substituteFree`：替换指定 free 变量，scope 保持不变；
* `closeFree`：把指定 free 变量关闭为当前 de Bruijn 层，scope 从 `d` 变为 `d+1`；
* `openBound`：打开当前 de Bruijn 层，scope 从 `d+1` 变回 `d`；
* `weakenBound`：在 cutoff 处插入一个 bound 层，scope 从 `d` 变为 `d+1`。
* `abstractFreeTop`：把 free 上下文顶部变量抽象为当前 binder，并同步压缩其余
  free de Bruijn 下标，scope 从 `d` 变为 `d+1`。
* `swapBound`：交换 cutoff 与其后继两个相邻 bound 槽位，scope 保持不变。

term、参数列和公式共享同一关系符号与递归方程。量词分支只把深度加一，因此不再需要
变量新鲜性、捕获规避、字符串位置、binder 扫描或 substitutable 旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 语法递归使用的纯集合成员有界量词参数。 -/
def syntax_set_levy_bound : Formula.LevyBound signature where
  sort := SetSort.set
  relation := RelationSymbol.membership
  domains := by rfl

@[simp] private theorem substituteMapped_boundId_weakenBound
    {bound sourceFree targetFree : SetContext}
    (introduced : SetSort)
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    {sort : SetSort} (term : Term signature bound sourceFree sort) :
    (term.weakenBound introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.weakenBound introduced τ) =
      (term.substituteMapped VariableSubstitution.boundId τ).weakenBound
        introduced := by
  simpa [VariableSubstitution.liftBound] using
    (Term.substituteMapped_weakenBound introduced
      (VariableSubstitution.boundId :
        VariableSubstitution signature bound bound targetFree)
      τ term)

/-! ## 公共标签 -/

inductive SyntaxCodeKind where
  | term
  | termList
  | formula
  deriving DecidableEq, Repr

def syntax_code_kind : SyntaxCodeKind → Nat
  | .term => 0
  | .termList => 1
  | .formula => 2

inductive SyntaxTransformOperation where
  | substituteFree
  | closeFree
  | openBound
  | weakenBound
  | abstractFreeTop
  | swapBound
  deriving DecidableEq, Repr

def syntax_transform_operation : SyntaxTransformOperation → Nat
  | .substituteFree => 0
  | .closeFree => 1
  | .openBound => 2
  | .weakenBound => 3
  | .abstractFreeTop => 4
  | .swapBound => 5

abbrev syntax_code_kind_term {bound free : SetContext}
    (kind : SyntaxCodeKind) : SetTerm bound free :=
  numₘ(syntax_code_kind kind)

abbrev syntax_transform_operation_term {bound free : SetContext}
    (operation : SyntaxTransformOperation) : SetTerm bound free :=
  numₘ(syntax_transform_operation operation)

/-! ## 上下文提升快路径 -/

/-- 一次遍历前的规范四层自由上下文提升，供四元构造分支共享。 -/
def term_weaken_free_four {bound free : SetContext}
    (term : SetTerm bound free) :
    SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
  @Term.weakenFree signature bound
    (SetSort.set :: SetSort.set :: SetSort.set :: free)
    SetSort.set SetSort.set
    (@Term.weakenFree signature bound
      (SetSort.set :: SetSort.set :: free) SetSort.set SetSort.set
      (@Term.weakenFree signature bound
        (SetSort.set :: free) SetSort.set SetSort.set
        (@Term.weakenFree signature bound free
          SetSort.set SetSort.set term)))

/-! ## 变换边界 -/

private def term_transform_scope_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) :
    SetFormula bound free :=
  let substitute :=
    (operation ≐ₘ syntax_transform_operation_term .substituteFree) ∧ₘ
      ((term_code_atₘ(depth, source) ∧ₘ
        term_code_atₘ(depth, target)) ∧ₘ
        term_codeₘ(replacement))
  let close :=
    (operation ≐ₘ syntax_transform_operation_term .closeFree) ∧ₘ
      ((term_code_atₘ(depth, source) ∧ₘ
        term_code_atₘ(Sₘ(depth), target)) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let openCase :=
    (operation ≐ₘ syntax_transform_operation_term .openBound) ∧ₘ
      ((term_code_atₘ(Sₘ(depth), source) ∧ₘ
        term_code_atₘ(depth, target)) ∧ₘ
        term_codeₘ(replacement))
  let weaken :=
    (operation ≐ₘ syntax_transform_operation_term .weakenBound) ∧ₘ
      (((variableIndex ∈ₘ Sₘ(depth)) ∧ₘ
        (term_code_atₘ(depth, source) ∧ₘ
          term_code_atₘ(Sₘ(depth), target))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let abstractTop :=
    (operation ≐ₘ syntax_transform_operation_term .abstractFreeTop) ∧ₘ
      (((term_code_atₘ(depth, source) ∧ₘ
          term_code_atₘ(Sₘ(depth), target)) ∧ₘ
        (variableIndex ≐ₘ numₘ(0))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let swap :=
    (operation ≐ₘ syntax_transform_operation_term .swapBound) ∧ₘ
      ((((variableIndex ∈ₘ depth) ∧ₘ
          (Sₘ(variableIndex) ∈ₘ depth)) ∧ₘ
        (term_code_atₘ(depth, source) ∧ₘ
          term_code_atₘ(depth, target))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  substitute ∨ₘ
    (close ∨ₘ (openCase ∨ₘ ((weaken ∨ₘ swap) ∨ₘ abstractTop)))

private def term_list_transform_scope_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) :
    SetFormula bound free :=
  let operationOne := operation.weakenFree SetSort.set
  let depthOne := depth.weakenFree SetSort.set
  let variableOne := variableIndex.weakenFree SetSort.set
  let replacementOne := replacement.weakenFree SetSort.set
  let sourceOne := source.weakenFree SetSort.set
  let targetOne := target.weakenFree SetSort.set
  let length : SetTerm bound (SetSort.set :: free) := .fvar .here
  let substitute :=
    (operationOne ≐ₘ syntax_transform_operation_term .substituteFree) ∧ₘ
      ((term_list_code_atₘ(depthOne, length, sourceOne) ∧ₘ
        term_list_code_atₘ(depthOne, length, targetOne)) ∧ₘ
        term_codeₘ(replacementOne))
  let close :=
    (operationOne ≐ₘ syntax_transform_operation_term .closeFree) ∧ₘ
      ((term_list_code_atₘ(depthOne, length, sourceOne) ∧ₘ
        term_list_code_atₘ(Sₘ(depthOne), length, targetOne)) ∧ₘ
        (replacementOne ≐ₘ numₘ(0)))
  let openCase :=
    (operationOne ≐ₘ syntax_transform_operation_term .openBound) ∧ₘ
      ((term_list_code_atₘ(Sₘ(depthOne), length, sourceOne) ∧ₘ
        term_list_code_atₘ(depthOne, length, targetOne)) ∧ₘ
        term_codeₘ(replacementOne))
  let weaken :=
    (operationOne ≐ₘ syntax_transform_operation_term .weakenBound) ∧ₘ
      (((variableOne ∈ₘ Sₘ(depthOne)) ∧ₘ
        (term_list_code_atₘ(depthOne, length, sourceOne) ∧ₘ
          term_list_code_atₘ(Sₘ(depthOne), length, targetOne))) ∧ₘ
        (replacementOne ≐ₘ numₘ(0)))
  let abstractTop :=
    (operationOne ≐ₘ syntax_transform_operation_term .abstractFreeTop) ∧ₘ
      (((term_list_code_atₘ(depthOne, length, sourceOne) ∧ₘ
          term_list_code_atₘ(Sₘ(depthOne), length, targetOne)) ∧ₘ
        (variableOne ≐ₘ numₘ(0))) ∧ₘ
        (replacementOne ≐ₘ numₘ(0)))
  let swap :=
    (operationOne ≐ₘ syntax_transform_operation_term .swapBound) ∧ₘ
      ((((variableOne ∈ₘ depthOne) ∧ₘ
          (Sₘ(variableOne) ∈ₘ depthOne)) ∧ₘ
        (term_list_code_atₘ(depthOne, length, sourceOne) ∧ₘ
          term_list_code_atₘ(depthOne, length, targetOne))) ∧ₘ
        (replacementOne ≐ₘ numₘ(0)))
  ((length ∈ₘ ωₘ) ∧ₘ
      (substitute ∨ₘ
        (close ∨ₘ
          (openCase ∨ₘ ((weaken ∨ₘ swap) ∨ₘ abstractTop)))))
    |>.existsFreeTop SetSort.set

private def formula_transform_scope_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) :
    SetFormula bound free :=
  let substitute :=
    (operation ≐ₘ syntax_transform_operation_term .substituteFree) ∧ₘ
      ((formula_code_atₘ(depth, source) ∧ₘ
        formula_code_atₘ(depth, target)) ∧ₘ
        term_codeₘ(replacement))
  let close :=
    (operation ≐ₘ syntax_transform_operation_term .closeFree) ∧ₘ
      ((formula_code_atₘ(depth, source) ∧ₘ
        formula_code_atₘ(Sₘ(depth), target)) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let openCase :=
    (operation ≐ₘ syntax_transform_operation_term .openBound) ∧ₘ
      ((formula_code_atₘ(Sₘ(depth), source) ∧ₘ
        formula_code_atₘ(depth, target)) ∧ₘ
        term_codeₘ(replacement))
  let weaken :=
    (operation ≐ₘ syntax_transform_operation_term .weakenBound) ∧ₘ
      (((variableIndex ∈ₘ Sₘ(depth)) ∧ₘ
        (formula_code_atₘ(depth, source) ∧ₘ
          formula_code_atₘ(Sₘ(depth), target))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let abstractTop :=
    (operation ≐ₘ syntax_transform_operation_term .abstractFreeTop) ∧ₘ
      (((formula_code_atₘ(depth, source) ∧ₘ
          formula_code_atₘ(Sₘ(depth), target)) ∧ₘ
        (variableIndex ≐ₘ numₘ(0))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  let swap :=
    (operation ≐ₘ syntax_transform_operation_term .swapBound) ∧ₘ
      ((((variableIndex ∈ₘ depth) ∧ₘ
          (Sₘ(variableIndex) ∈ₘ depth)) ∧ₘ
        (formula_code_atₘ(depth, source) ∧ₘ
          formula_code_atₘ(depth, target))) ∧ₘ
        (replacement ≐ₘ numₘ(0)))
  substitute ∨ₘ
    (close ∨ₘ (openCase ∨ₘ ((weaken ∨ₘ swap) ∨ₘ abstractTop)))

/-- 统一语法变换关系的码域与 binder 深度条件，供结构正确性证明组合。 -/
def syntax_transform_scope_condition {bound free : SetContext}
    (kind operation depth variableIndex replacement source target :
      SetTerm bound free) :
    SetFormula bound free :=
  ((kind ≐ₘ syntax_code_kind_term .term) ∧ₘ
      term_transform_scope_condition
        operation depth variableIndex replacement source target) ∨ₘ
    (((kind ≐ₘ syntax_code_kind_term .termList) ∧ₘ
      term_list_transform_scope_condition
        operation depth variableIndex replacement source target) ∨ₘ
    ((kind ≐ₘ syntax_code_kind_term .formula) ∧ₘ
      formula_transform_scope_condition
        operation depth variableIndex replacement source target))

/-! ## 项变换分支 -/

private def free_variable_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationOne := operation.weakenFree SetSort.set
  let depthOne := depth.weakenFree SetSort.set
  let variableOne := variableIndex.weakenFree SetSort.set
  let replacementOne := replacement.weakenFree SetSort.set
  let sourceOne := source.weakenFree SetSort.set
  let targetOne := target.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let substitute :=
    (operationOne ≐ₘ syntax_transform_operation_term .substituteFree) ∧ₘ
      (((index ≐ₘ variableOne) ∧ₘ
        (targetOne ≐ₘ replacementOne)) ∨ₘ
      ((index ≠ₘ variableOne) ∧ₘ
        (targetOne ≐ₘ sourceOne)))
  let close :=
    (operationOne ≐ₘ syntax_transform_operation_term .closeFree) ∧ₘ
      (((index ≐ₘ variableOne) ∧ₘ
        (targetOne ≐ₘ bound_var_codeₘ(depthOne))) ∨ₘ
      ((index ≠ₘ variableOne) ∧ₘ
        (targetOne ≐ₘ sourceOne)))
  let openCase :=
    (operationOne ≐ₘ syntax_transform_operation_term .openBound) ∧ₘ
      (targetOne ≐ₘ sourceOne)
  let weaken :=
    (operationOne ≐ₘ syntax_transform_operation_term .weakenBound) ∧ₘ
      (targetOne ≐ₘ sourceOne)
  let swap :=
    (operationOne ≐ₘ syntax_transform_operation_term .swapBound) ∧ₘ
      (targetOne ≐ₘ sourceOne)
  let abstractTop :=
    let previous : SetTerm (SetSort.set :: bound) (SetSort.set :: free) :=
      .bvar .here
    let indexBound := index.weakenBound SetSort.set
    let targetBound := targetOne.weakenBound SetSort.set
    let predecessor :=
      Formula.LevyBound.boundedExists syntax_set_levy_bound index
        ((indexBound ≐ₘ Sₘ(previous)) ∧ₘ
          (targetBound ≐ₘ free_var_codeₘ(previous)))
    (operationOne ≐ₘ syntax_transform_operation_term .abstractFreeTop) ∧ₘ
      (((index ≐ₘ numₘ(0)) ∧ₘ
          (targetOne ≐ₘ bound_var_codeₘ(depthOne))) ∨ₘ
        predecessor)
  ((index ∈ₘ ωₘ) ∧ₘ
    ((sourceOne ≐ₘ free_var_codeₘ(index)) ∧ₘ
      (substitute ∨ₘ
        (close ∨ₘ
          (openCase ∨ₘ ((weaken ∨ₘ swap) ∨ₘ abstractTop))))))
    |>.existsFreeTop SetSort.set

private def bound_variable_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) :
    SetFormula bound free :=
  let operationOne := operation.weakenFree SetSort.set
  let depthOne := depth.weakenFree SetSort.set
  let variableOne := variableIndex.weakenFree SetSort.set
  let replacementOne := replacement.weakenFree SetSort.set
  let sourceOne := source.weakenFree SetSort.set
  let targetOne := target.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let preserve :=
    (((operationOne ≐ₘ syntax_transform_operation_term .substituteFree) ∨ₘ
      ((operationOne ≐ₘ syntax_transform_operation_term .closeFree) ∨ₘ
        (operationOne ≐ₘ
          syntax_transform_operation_term .abstractFreeTop))) ∧ₘ
      ((index ∈ₘ depthOne) ∧ₘ (targetOne ≐ₘ sourceOne)))
  let openCase :=
    (operationOne ≐ₘ syntax_transform_operation_term .openBound) ∧ₘ
      ((index ∈ₘ Sₘ(depthOne)) ∧ₘ
        (((index ≐ₘ depthOne) ∧ₘ
          (targetOne ≐ₘ replacementOne)) ∨ₘ
        ((index ∈ₘ depthOne) ∧ₘ
          (targetOne ≐ₘ sourceOne))))
  let weaken :=
    (operationOne ≐ₘ syntax_transform_operation_term .weakenBound) ∧ₘ
      ((index ∈ₘ depthOne) ∧ₘ
        (((index ∈ₘ variableOne) ∧ₘ
          (targetOne ≐ₘ sourceOne)) ∨ₘ
        ((¬ₘ (index ∈ₘ variableOne)) ∧ₘ
          (targetOne ≐ₘ bound_var_codeₘ(Sₘ(index))))))
  let swap :=
    (operationOne ≐ₘ syntax_transform_operation_term .swapBound) ∧ₘ
      ((index ∈ₘ depthOne) ∧ₘ
        (((index ≐ₘ variableOne) ∧ₘ
          (targetOne ≐ₘ bound_var_codeₘ(Sₘ(variableOne)))) ∨ₘ
        (((index ≐ₘ Sₘ(variableOne)) ∧ₘ
          (targetOne ≐ₘ bound_var_codeₘ(variableOne))) ∨ₘ
        (((index ≠ₘ variableOne) ∧ₘ
          (index ≠ₘ Sₘ(variableOne))) ∧ₘ
          (targetOne ≐ₘ sourceOne)))))
  ((sourceOne ≐ₘ bound_var_codeₘ(index)) ∧ₘ
    (preserve ∨ₘ (openCase ∨ₘ (weaken ∨ₘ swap))))
    |>.existsFreeTop SetSort.set

private def constant_transform_condition {bound free : SetContext}
    (source target : SetTerm bound free) : SetFormula bound free :=
  let sourceOne := source.weakenFree SetSort.set
  let targetOne := target.weakenFree SetSort.set
  let symbol : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((symbol ∈ₘ ωₘ) ∧ₘ
    ((sourceOne ≐ₘ const_codeₘ(symbol)) ∧ₘ
      (targetOne ≐ₘ sourceOne)))
    |>.existsFreeTop SetSort.set

private def application_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationFour := term_weaken_free_four operation
  let depthFour := term_weaken_free_four depth
  let variableFour := term_weaken_free_four variableIndex
  let replacementFour := term_weaken_free_four replacement
  let sourceFour := term_weaken_free_four source
  let targetFour := term_weaken_free_four target
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let sourceArguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetArguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
    (((sourceFour ≐ₘ app_codeₘ(arity, symbol, sourceArguments)) ∧ₘ
      (targetFour ≐ₘ app_codeₘ(arity, symbol, targetArguments))) ∧ₘ
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        operationFour, depthFour, variableFour, replacementFour,
        sourceArguments, targetArguments)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def term_transform_shape_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  free_variable_transform_condition
      operation depth variableIndex replacement source target ∨ₘ
    (bound_variable_transform_condition
      operation depth variableIndex replacement source target ∨ₘ
    (constant_transform_condition source target ∨ₘ
      application_transform_condition
        operation depth variableIndex replacement source target))

/-! ## 参数列变换分支 -/

private def term_list_cons_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationFour := term_weaken_free_four operation
  let depthFour := term_weaken_free_four depth
  let variableFour := term_weaken_free_four variableIndex
  let replacementFour := term_weaken_free_four replacement
  let sourceFour := term_weaken_free_four source
  let targetFour := term_weaken_free_four target
  let sourceHead : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let sourceTail : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let targetHead : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetTail : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  (((sourceFour ≐ₘ code_consₘ(sourceHead, sourceTail)) ∧ₘ
      (targetFour ≐ₘ code_consₘ(targetHead, targetTail))) ∧ₘ
    (syntax_transformₘ(
      syntax_code_kind_term .term,
      operationFour, depthFour, variableFour, replacementFour,
      sourceHead, targetHead) ∧ₘ
    syntax_transformₘ(
      syntax_code_kind_term .termList,
      operationFour, depthFour, variableFour, replacementFour,
      sourceTail, targetTail)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def term_list_transform_shape_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  ((source ≐ₘ code_nilₘ) ∧ₘ (target ≐ₘ code_nilₘ)) ∨ₘ
    term_list_cons_transform_condition
      operation depth variableIndex replacement source target

/-! ## 公式变换分支 -/

/-- 二元原子公式节点的统一变换条件。 -/
def binary_formula_transform_condition {bound free : SetContext}
    (tag : StructuralCodeTag)
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationFour := term_weaken_free_four operation
  let depthFour := term_weaken_free_four depth
  let variableFour := term_weaken_free_four variableIndex
  let replacementFour := term_weaken_free_four replacement
  let sourceFour := term_weaken_free_four source
  let targetFour := term_weaken_free_four target
  let sourceLeft : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let sourceRight : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let targetLeft : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetRight : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  (((sourceFour ≐ₘ
      structural_node_code_term tag [sourceLeft, sourceRight]) ∧ₘ
    (targetFour ≐ₘ
      structural_node_code_term tag [targetLeft, targetRight])) ∧ₘ
    (syntax_transformₘ(
      syntax_code_kind_term .term,
      operationFour, depthFour, variableFour, replacementFour,
      sourceLeft, targetLeft) ∧ₘ
    syntax_transformₘ(
      syntax_code_kind_term .term,
      operationFour, depthFour, variableFour, replacementFour,
      sourceRight, targetRight)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 谓词公式节点的统一变换条件。 -/
def predicate_formula_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationFour := term_weaken_free_four operation
  let depthFour := term_weaken_free_four depth
  let variableFour := term_weaken_free_four variableIndex
  let replacementFour := term_weaken_free_four replacement
  let sourceFour := term_weaken_free_four source
  let targetFour := term_weaken_free_four target
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let sourceArguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetArguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
    (((sourceFour ≐ₘ
      pred_codeₘ(arity, symbol, sourceArguments)) ∧ₘ
      (targetFour ≐ₘ
      pred_codeₘ(arity, symbol, targetArguments))) ∧ₘ
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        operationFour, depthFour, variableFour, replacementFour,
        sourceArguments, targetArguments)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 否定公式节点的统一变换条件。 -/
def negation_formula_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationTwo := term_weaken_free_two operation
  let depthTwo := term_weaken_free_two depth
  let variableTwo := term_weaken_free_two variableIndex
  let replacementTwo := term_weaken_free_two replacement
  let sourceTwo := term_weaken_free_two source
  let targetTwo := term_weaken_free_two target
  let sourceBody : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetBody : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((sourceTwo ≐ₘ neg_codeₘ(sourceBody)) ∧ₘ
    (targetTwo ≐ₘ neg_codeₘ(targetBody))) ∧ₘ
    syntax_transformₘ(
      syntax_code_kind_term .formula,
      operationTwo, depthTwo, variableTwo, replacementTwo,
      sourceBody, targetBody))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 蕴含公式节点的统一变换条件。 -/
def implication_formula_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationFour := term_weaken_free_four operation
  let depthFour := term_weaken_free_four depth
  let variableFour := term_weaken_free_four variableIndex
  let replacementFour := term_weaken_free_four replacement
  let sourceFour := term_weaken_free_four source
  let targetFour := term_weaken_free_four target
  let sourceLeft : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there (.there .here)))
  let sourceRight : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let targetLeft : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetRight : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar .here
  (((sourceFour ≐ₘ imp_codeₘ(sourceLeft, sourceRight)) ∧ₘ
    (targetFour ≐ₘ imp_codeₘ(targetLeft, targetRight))) ∧ₘ
    (syntax_transformₘ(
      syntax_code_kind_term .formula,
      operationFour, depthFour, variableFour, replacementFour,
      sourceLeft, targetLeft) ∧ₘ
    syntax_transformₘ(
      syntax_code_kind_term .formula,
      operationFour, depthFour, variableFour, replacementFour,
      sourceRight, targetRight)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 全称公式节点的统一变换条件。 -/
def universal_formula_transform_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  let operationTwo := term_weaken_free_two operation
  let depthTwo := term_weaken_free_two depth
  let variableTwo := term_weaken_free_two variableIndex
  let replacementTwo := term_weaken_free_two replacement
  let sourceTwo := term_weaken_free_two source
  let targetTwo := term_weaken_free_two target
  let sourceBody : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let targetBody : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  let preserveVariable :=
    (operationTwo ≐ₘ syntax_transform_operation_term .substituteFree) ∨ₘ
      ((operationTwo ≐ₘ syntax_transform_operation_term .closeFree) ∨ₘ
      ((operationTwo ≐ₘ syntax_transform_operation_term .openBound) ∨ₘ
        (operationTwo ≐ₘ syntax_transform_operation_term .abstractFreeTop)))
  let shiftVariable :=
    (operationTwo ≐ₘ syntax_transform_operation_term .weakenBound) ∨ₘ
      (operationTwo ≐ₘ syntax_transform_operation_term .swapBound)
  (((sourceTwo ≐ₘ all_codeₘ(sourceBody)) ∧ₘ
    (targetTwo ≐ₘ all_codeₘ(targetBody))) ∧ₘ
    ((shiftVariable ∧ₘ
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        operationTwo, Sₘ(depthTwo), Sₘ(variableTwo), replacementTwo,
        sourceBody, targetBody)) ∨ₘ
    (preserveVariable ∧ₘ
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        operationTwo, Sₘ(depthTwo), variableTwo, replacementTwo,
        sourceBody, targetBody))))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

/-- 公式六种结构节点的统一变换析取。 -/
def formula_transform_shape_condition {bound free : SetContext}
    (operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  binary_formula_transform_condition .equality
      operation depth variableIndex replacement source target ∨ₘ
    (binary_formula_transform_condition .membership
      operation depth variableIndex replacement source target ∨ₘ
    (predicate_formula_transform_condition
      operation depth variableIndex replacement source target ∨ₘ
    (negation_formula_transform_condition
      operation depth variableIndex replacement source target ∨ₘ
    (implication_formula_transform_condition
      operation depth variableIndex replacement source target ∨ₘ
      universal_formula_transform_condition
        operation depth variableIndex replacement source target))))

/-! ## 统一变换递归方程 -/

/-- 统一语法变换关系的构造形状递归条件，供各语法构造子的正确性证明组合。 -/
def syntax_transform_shape_condition {bound free : SetContext}
    (kind operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  ((kind ≐ₘ syntax_code_kind_term .term) ∧ₘ
      term_transform_shape_condition
        operation depth variableIndex replacement source target) ∨ₘ
    (((kind ≐ₘ syntax_code_kind_term .termList) ∧ₘ
      term_list_transform_shape_condition
        operation depth variableIndex replacement source target) ∨ₘ
    ((kind ≐ₘ syntax_code_kind_term .formula) ∧ₘ
      formula_transform_shape_condition
        operation depth variableIndex replacement source target))

def syntax_transform_condition {bound free : SetContext}
    (kind operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  (((((kind ∈ₘ ωₘ) ∧ₘ (operation ∈ₘ ωₘ)) ∧ₘ
      ((depth ∈ₘ ωₘ) ∧ₘ (variableIndex ∈ₘ ωₘ))) ∧ₘ
      ((replacement ∈ₘ ωₘ) ∧ₘ
        ((source ∈ₘ ωₘ) ∧ₘ (target ∈ₘ ωₘ)))) ∧ₘ
    syntax_transform_scope_condition
      kind operation depth variableIndex replacement source target) ∧ₘ
    syntax_transform_shape_condition
      kind operation depth variableIndex replacement source target

def syntax_transform_definition_instance {bound free : SetContext}
    (kind operation depth variableIndex replacement source target :
      SetTerm bound free) : SetFormula bound free :=
  syntax_transformₘ(
    kind, operation, depth, variableIndex, replacement, source, target) ↔ₘ
    syntax_transform_condition
      kind operation depth variableIndex replacement source target

/-! ## 自由变量出现递归方程 -/

private def term_free_variable_occurs_condition {bound free : SetContext}
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let codeOne := code.weakenFree SetSort.set
  let index : SetTerm bound (SetSort.set :: free) := .fvar .here
  let variableLeaf :=
    ((index ∈ₘ ωₘ) ∧ₘ
      ((codeOne ≐ₘ free_var_codeₘ(index)) ∧ₘ
        (index ≐ₘ variableIndex.weakenFree SetSort.set)))
      |>.existsFreeTop SetSort.set
  let codeThree := term_weaken_free_three code
  let variableThree := term_weaken_free_three variableIndex
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  let application :=
    (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
      ((codeThree ≐ₘ app_codeₘ(arity, symbol, arguments)) ∧ₘ
        free_var_occursₘ(
          syntax_code_kind_term .termList, variableThree, arguments)))
      |>.existsFreeTop SetSort.set
      |>.existsFreeTop SetSort.set
      |>.existsFreeTop SetSort.set
  variableLeaf ∨ₘ application

private def term_list_free_variable_occurs_condition
    {bound free : SetContext}
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let variableTwo := term_weaken_free_two variableIndex
  let codeTwo := term_weaken_free_two code
  let head : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let tail : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((codeTwo ≐ₘ code_consₘ(head, tail)) ∧ₘ
    (free_var_occursₘ(
      syntax_code_kind_term .term, variableTwo, head) ∨ₘ
    free_var_occursₘ(
      syntax_code_kind_term .termList, variableTwo, tail)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def binary_formula_free_variable_occurs_condition
    {bound free : SetContext}
    (tag : StructuralCodeTag)
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let variableTwo := term_weaken_free_two variableIndex
  let codeTwo := term_weaken_free_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((codeTwo ≐ₘ structural_node_code_term tag [left, right]) ∧ₘ
    (free_var_occursₘ(
      syntax_code_kind_term .term, variableTwo, left) ∨ₘ
    free_var_occursₘ(
      syntax_code_kind_term .term, variableTwo, right)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def predicate_formula_free_variable_occurs_condition
    {bound free : SetContext}
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let variableThree := term_weaken_free_three variableIndex
  let codeThree := term_weaken_free_three code
  let arity : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there (.there .here))
  let symbol : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let arguments : SetTerm bound
      ([SetSort.set, SetSort.set, SetSort.set] ++ free) := .fvar .here
  (((arity ∈ₘ ωₘ) ∧ₘ (symbol ∈ₘ ωₘ)) ∧ₘ
    ((codeThree ≐ₘ pred_codeₘ(arity, symbol, arguments)) ∧ₘ
      free_var_occursₘ(
        syntax_code_kind_term .termList, variableThree, arguments)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def unary_formula_free_variable_occurs_condition
    {bound free : SetContext}
    (tag : StructuralCodeTag)
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let variableOne := variableIndex.weakenFree SetSort.set
  let codeOne := code.weakenFree SetSort.set
  let body : SetTerm bound (SetSort.set :: free) := .fvar .here
  ((codeOne ≐ₘ structural_node_code_term tag [body]) ∧ₘ
    free_var_occursₘ(
      syntax_code_kind_term .formula, variableOne, body))
    |>.existsFreeTop SetSort.set

private def implication_free_variable_occurs_condition
    {bound free : SetContext}
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  let variableTwo := term_weaken_free_two variableIndex
  let codeTwo := term_weaken_free_two code
  let left : SetTerm bound ([SetSort.set, SetSort.set] ++ free) :=
    .fvar (.there .here)
  let right : SetTerm bound ([SetSort.set, SetSort.set] ++ free) := .fvar .here
  ((codeTwo ≐ₘ imp_codeₘ(left, right)) ∧ₘ
    (free_var_occursₘ(
      syntax_code_kind_term .formula, variableTwo, left) ∨ₘ
    free_var_occursₘ(
      syntax_code_kind_term .formula, variableTwo, right)))
    |>.existsFreeTop SetSort.set
    |>.existsFreeTop SetSort.set

private def formula_free_variable_occurs_condition
    {bound free : SetContext}
    (variableIndex code : SetTerm bound free) : SetFormula bound free :=
  binary_formula_free_variable_occurs_condition
      .equality variableIndex code ∨ₘ
    (binary_formula_free_variable_occurs_condition
      .membership variableIndex code ∨ₘ
    (predicate_formula_free_variable_occurs_condition
      variableIndex code ∨ₘ
    (unary_formula_free_variable_occurs_condition
      .negation variableIndex code ∨ₘ
    (implication_free_variable_occurs_condition
      variableIndex code ∨ₘ
      unary_formula_free_variable_occurs_condition
        .universal variableIndex code))))

def free_variable_occurs_condition {bound free : SetContext}
    (kind variableIndex code : SetTerm bound free) : SetFormula bound free :=
  (((kind ∈ₘ ωₘ) ∧ₘ (variableIndex ∈ₘ ωₘ)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
    (((kind ≐ₘ syntax_code_kind_term .term) ∧ₘ
      term_free_variable_occurs_condition variableIndex code) ∨ₘ
    (((kind ≐ₘ syntax_code_kind_term .termList) ∧ₘ
      term_list_free_variable_occurs_condition variableIndex code) ∨ₘ
    ((kind ≐ₘ syntax_code_kind_term .formula) ∧ₘ
      formula_free_variable_occurs_condition variableIndex code)))

def free_variable_occurs_definition_instance {bound free : SetContext}
    (kind variableIndex code : SetTerm bound free) : SetFormula bound free :=
  free_var_occursₘ(kind, variableIndex, code) ↔ₘ
    free_variable_occurs_condition kind variableIndex code

/-! ## 替换自然性快路径 -/

@[simp] theorem syntax_transform_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (kind operation depth variableIndex replacement source target :
      SetTerm bound sourceFree) :
    (syntax_transform_definition_instance
      kind operation depth variableIndex replacement source target).substituteFree τ =
      syntax_transform_definition_instance
        (kind.substituteFree τ) (operation.substituteFree τ)
        (depth.substituteFree τ) (variableIndex.substituteFree τ)
        (replacement.substituteFree τ) (source.substituteFree τ)
        (target.substituteFree τ) := by
  simp [syntax_transform_definition_instance, syntax_transform_condition,
    syntax_transform_scope_condition, term_transform_scope_condition,
    term_list_transform_scope_condition, formula_transform_scope_condition,
    syntax_transform_shape_condition, term_transform_shape_condition,
    free_variable_transform_condition, bound_variable_transform_condition,
    constant_transform_condition, application_transform_condition,
    term_list_transform_shape_condition,
    term_list_cons_transform_condition,
    formula_transform_shape_condition,
    binary_formula_transform_condition,
    predicate_formula_transform_condition,
    negation_formula_transform_condition,
    implication_formula_transform_condition,
    universal_formula_transform_condition,
    syntax_set_levy_bound, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership_substituteMapped,
    substituteMapped_boundId_weakenBound,
    term_weaken_free_two, term_weaken_free_four,
    structural_list_code_term, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteFree,
    Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree]
  repeat' constructor

@[simp] theorem free_variable_occurs_definition_instance_substituteFree
    {bound sourceFree targetFree : SetContext}
    (τ : VariableSubstitution signature sourceFree bound targetFree)
    (kind variableIndex code : SetTerm bound sourceFree) :
    (free_variable_occurs_definition_instance
      kind variableIndex code).substituteFree τ =
      free_variable_occurs_definition_instance
        (kind.substituteFree τ) (variableIndex.substituteFree τ)
        (code.substituteFree τ) := by
  simp [free_variable_occurs_definition_instance,
    free_variable_occurs_condition,
    term_free_variable_occurs_condition,
    term_list_free_variable_occurs_condition,
    formula_free_variable_occurs_condition,
    binary_formula_free_variable_occurs_condition,
    predicate_formula_free_variable_occurs_condition,
    unary_formula_free_variable_occurs_condition,
    implication_free_variable_occurs_condition,
    term_weaken_free_two, term_weaken_free_three, structural_list_code_term,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree]
  repeat' constructor

/-! ## 面向逻辑层的规范入口 -/

def formula_free_substitution_condition {bound free : SetContext}
    (variableIndex replacement source target : SetTerm bound free) :
    SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .substituteFree,
    numₘ(0), variableIndex, replacement, source, target)

def formula_close_free_condition {bound free : SetContext}
    (variableIndex source target : SetTerm bound free) :
    SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .closeFree,
    numₘ(0), variableIndex, numₘ(0), source, target)

def formula_open_bound_condition {bound free : SetContext}
    (replacement source target : SetTerm bound free) :
    SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .openBound,
    numₘ(0), numₘ(0), replacement, source, target)

/-- 打开 bound 层的公共图谓词与任意类型化替换交换。 -/
@[simp] theorem formula_open_bound_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (replacement source target : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (formula_open_bound_condition replacement source target) =
      formula_open_bound_condition
        (replacement.substituteMapped
          boundSubstitution freeSubstitution)
        (source.substituteMapped boundSubstitution freeSubstitution)
        (target.substituteMapped boundSubstitution freeSubstitution) := by
  simp [formula_open_bound_condition, Formula.substituteMapped, Arguments.substituteMapped]

def formula_weaken_bound_condition {bound free : SetContext}
    (depth cutoff source target : SetTerm bound free) :
    SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .weakenBound,
    depth, cutoff, numₘ(0), source, target)

def formula_swap_bound_condition {bound free : SetContext}
    (depth cutoff source target : SetTerm bound free) :
    SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .swapBound,
    depth, cutoff, numₘ(0), source, target)

@[simp] theorem formula_weaken_bound_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (depth cutoff source target : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (formula_weaken_bound_condition depth cutoff source target) =
      formula_weaken_bound_condition
        (depth.substituteMapped boundSubstitution freeSubstitution)
        (cutoff.substituteMapped boundSubstitution freeSubstitution)
        (source.substituteMapped boundSubstitution freeSubstitution)
        (target.substituteMapped boundSubstitution freeSubstitution) := by
  simp [formula_weaken_bound_condition, Formula.substituteMapped,
    Arguments.substituteMapped]

@[simp] theorem formula_swap_bound_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (depth cutoff source target : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (formula_swap_bound_condition depth cutoff source target) =
      formula_swap_bound_condition
        (depth.substituteMapped boundSubstitution freeSubstitution)
        (cutoff.substituteMapped boundSubstitution freeSubstitution)
        (source.substituteMapped boundSubstitution freeSubstitution)
        (target.substituteMapped boundSubstitution freeSubstitution) := by
  simp [formula_swap_bound_condition, Formula.substituteMapped,
    Arguments.substituteMapped]

/-- 把 free 上下文顶部变量抽象为当前最外层 binder。 -/
def formula_abstract_free_top_condition {bound free : SetContext}
    (source target : SetTerm bound free) : SetFormula bound free :=
  syntax_transformₘ(
    syntax_code_kind_term .formula,
    syntax_transform_operation_term .abstractFreeTop,
    numₘ(0), numₘ(0), numₘ(0), source, target)

def formula_free_variable_occurs {bound free : SetContext}
    (variableIndex formula : SetTerm bound free) : SetFormula bound free :=
  free_var_occursₘ(
    syntax_code_kind_term .formula, variableIndex, formula)

/-! ## 定义公理与理论 -/

def syntax_transform_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (syntax_transform_definition_instance
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there (.there (.there (.there .here))))) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there (.there (.there .here)))) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there (.there .here))) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there (.there .here)) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
            SetSort.set, SetSort.set, SetSort.set]))

def free_variable_occurs_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (free_variable_occurs_definition_instance
      (.fvar (.there (.there .here)) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set, SetSort.set]))

def expression_encoding_theory : SetTheory :=
  Theory.union membership_irreflexive_theory
    (Theory.union
      (Theory.insert free_variable_occurs_definition_axiom
        (Theory.insert syntax_transform_definition_axiom
          formal_language_encoding_theory))
      empty_set_symbol_theory)

derive_theory_subset membership_irreflexive_theory ⊆ expression_encoding_theory

derive_theory_subset formal_language_encoding_theory ⊆ expression_encoding_theory

derive_theory_subset empty_set_symbol_theory ⊆ expression_encoding_theory

/-- 表达式编码理论直接包含配数核心公理。 -/
derive_theory_subset godel_pairing_core_theory ⊆ expression_encoding_theory

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
