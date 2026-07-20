import YesMetaZFC.Automation.HostProp

/-!
# 单排序宿主一阶公式到 checked 自动化主线

本模块给普通 Lean 命题中的同一对象域量词、等式、函数与谓词提供一个固定 `Type 0`
语法。模型解释可以落在任意 `Type u`；搜索、预处理、DAG 与证书 payload 仍保持
`Type 0`。

这里不负责猜测 Lean 表达式的对象域。元层重化器只需构造 `CheckedInput`；本模块统一
承担 core/search 翻译、反模型桥与最终语义回放。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder

universe u x

open CoreSyntax
open CoreSyntax.NormalForm

/-- 单排序宿主项；零参数应用同时表示宿主常量。 -/
inductive Term where
  | bvar (index : Nat)
  | app (symbol : Nat) (arguments : List Term)
  deriving Repr, Inhabited

deriving instance BEq for Term
deriving instance Lean.ToExpr for Term

/-- 单排序宿主一阶公式。 -/
inductive Formula where
  | atom (symbol : Nat) (arguments : List Term)
  | equal (left right : Term)
  | falsum
  | truth
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  | forallE (body : Formula)
  | existsE (body : Formula)
  deriving Repr, Inhabited

deriving instance BEq for Formula
deriving instance Lean.ToExpr for Formula

/-- 宿主对象域上的函数与谓词解释。 -/
structure Interpretation (α : Type u) where
  default : α
  function : Nat → List α → α
  predicate : Nat → List α → Prop

namespace Term

/-- 宿主函数符号进入公共 core 语法。 -/
def functionSymbol (id arity : Nat) : CoreSyntax.FunctionSymbol := {
  id := id
  arity := arity
  role := .parameter
  inputSorts := List.replicate arity CoreSort.object
  outputSort := CoreSort.object
}

@[simp]
theorem searchFunctionDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcDomain
        (FirstOrderProjection.functionSymbol (functionSymbol id arity)) =
      List.replicate arity CoreSort.object := by
  cases arity <;> rfl

@[simp]
theorem searchFunctionCodomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcCodomain
        (FirstOrderProjection.functionSymbol (functionSymbol id arity)) =
      CoreSort.object :=
  rfl

mutual
  /-- 单排序项的直接宿主解释。 -/
  @[reducible] def eval {α : Type u} (interpretation : Interpretation α)
      (bound : Nat → α) : Term → α
    | .bvar index => bound index
    | .app symbol arguments =>
        interpretation.function symbol
          (evalList interpretation bound arguments)

  /-- 单排序参数列表的直接宿主解释。 -/
  @[reducible] def evalList {α : Type u} (interpretation : Interpretation α)
      (bound : Nat → α) : List Term → List α
    | [] => []
    | head :: tail =>
        eval interpretation bound head ::
          evalList interpretation bound tail
end

/-
单排序项与参数列表同步进入 preprocessing core。

显式列表递归让 concrete reification 保持普通构造子归约，避免嵌套 `List.map`
把定义编译成不适合作为 kernel replay 引用的 well-founded recursion。
-/
mutual
  /-- 单排序项进入 preprocessing core。 -/
  def toCore : Term → CoreSyntax.Term
    | .bvar index => .bvar CoreSort.object index
    | .app symbol arguments =>
        .app (functionSymbol symbol arguments.length) (toCoreList arguments)

  /-- 单排序参数列表进入 preprocessing core。 -/
  def toCoreList : List Term → List CoreSyntax.Term
    | [] => []
    | head :: tail => toCore head :: toCoreList tail
end

/-- 显式列表递归与原有 `List.map` 视图一致。 -/
@[simp] theorem toCoreList_eq_map :
    ∀ terms : List Term, toCoreList terms = terms.map toCore
  | [] => rfl
  | head :: tail =>
      congrArg (fun rest => toCore head :: rest) (toCoreList_eq_map tail)

/-- 单排序项进入 canonical DAG 搜索签名。 -/
def toSearch : Term →
    Logic.FirstOrder.Term SearchMaterialization.SearchSignature
  | .bvar index => .var (.bvar CoreSort.object index)
  | .app symbol arguments =>
      .app
        (FirstOrderProjection.functionSymbol
          (functionSymbol symbol arguments.length))
        (arguments.map toSearch)

mutual
  /-- 每个单排序项都在搜索签名中具有对象 sort。 -/
  theorem toSearch_wellSorted :
      ∀ term : Term,
        Logic.FirstOrder.TermWellSorted term.toSearch CoreSort.object
    | .bvar index =>
        by
          simpa only [Term.toSearch] using
            (Logic.FirstOrder.TermWellSorted.bvar
              (σ := SearchMaterialization.SearchSignature)
              CoreSort.object index)
    | .app symbol arguments => by
        let function :=
          FirstOrderProjection.functionSymbol
            (functionSymbol symbol arguments.length)
        have hArguments :
            Logic.FirstOrder.ArgsWellSorted
              (arguments.map toSearch)
              (SearchMaterialization.SearchSignature.funcDomain function) := by
          simpa [function] using toSearchList_wellSorted arguments
        simpa only [Term.toSearch, searchFunctionCodomain] using
          Logic.FirstOrder.TermWellSorted.app
            (σ := SearchMaterialization.SearchSignature)
            function hArguments

  /-- 单排序参数列表逐项匹配函数或谓词的对象 sort 列表。 -/
  theorem toSearchList_wellSorted :
      ∀ terms : List Term,
        Logic.FirstOrder.ArgsWellSorted
          (terms.map toSearch)
          (List.replicate terms.length CoreSort.object)
    | [] => .nil
    | head :: tail => by
        simpa using Logic.FirstOrder.ArgsWellSorted.cons
          (toSearch_wellSorted head)
          (toSearchList_wellSorted tail)
end

end Term

namespace Formula

/-- 宿主谓词符号进入公共 core 语法。 -/
def predicateSymbol (id arity : Nat) : CoreSyntax.PredicateSymbol := {
  id := id
  arity := arity
  role := .relation
  inputSorts := List.replicate arity CoreSort.object
}

@[simp]
theorem searchPredicateDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.relDomain
        (SearchMaterialization.RelSymbol.predicate
          (predicateSymbol id arity)) =
      List.replicate arity CoreSort.object := by
  cases arity <;> rfl

/-- 单排序公式的直接宿主解释。 -/
@[reducible] def eval {α : Type u} (interpretation : Interpretation α)
    (bound : Nat → α) : Formula → Prop
  | .atom symbol arguments =>
      interpretation.predicate symbol
        (Term.evalList interpretation bound arguments)
  | .equal left right =>
      Term.eval interpretation bound left =
        Term.eval interpretation bound right
  | .falsum => False
  | .truth => True
  | .neg body => ¬ eval interpretation bound body
  | .conj left right =>
      eval interpretation bound left ∧ eval interpretation bound right
  | .disj left right =>
      eval interpretation bound left ∨ eval interpretation bound right
  | .imp left right =>
      eval interpretation bound left → eval interpretation bound right
  | .iff left right =>
      eval interpretation bound left ↔ eval interpretation bound right
  | .forallE body =>
      ∀ value, eval interpretation
        (fun
          | 0 => value
          | index + 1 => bound index)
        body
  | .existsE body =>
      ∃ value, eval interpretation
        (fun
          | 0 => value
          | index + 1 => bound index)
        body

  /-- 单排序公式进入 preprocessing core。 -/
  def toCore : Formula → CoreSyntax.Formula
  | .atom symbol arguments =>
      .atom (predicateSymbol symbol arguments.length)
        (Term.toCoreList arguments)
  | .equal left right =>
      .equal CoreSort.object left.toCore right.toCore
  | .falsum => .falseE
  | .truth => .trueE
  | .neg body => .neg body.toCore
  | .conj left right => .conj left.toCore right.toCore
  | .disj left right => .disj left.toCore right.toCore
  | .imp left right => .imp left.toCore right.toCore
  | .iff left right => .iffE left.toCore right.toCore
  | .forallE body => .forallE CoreSort.object body.toCore
  | .existsE body => .existsE CoreSort.object body.toCore

/-- 单排序公式进入 canonical DAG 搜索签名。 -/
def toSearch : Formula →
    Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
  | .atom symbol arguments =>
      .rel
        (SearchMaterialization.RelSymbol.predicate
          (predicateSymbol symbol arguments.length))
        (arguments.map Term.toSearch)
  | .equal left right => .equal left.toSearch right.toSearch
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch
  | .conj left right => .conj left.toSearch right.toSearch
  | .disj left right => .disj left.toSearch right.toSearch
  | .imp left right => .imp left.toSearch right.toSearch
  | .iff left right => .iff left.toSearch right.toSearch
  | .forallE body => .forallE CoreSort.object body.toSearch
  | .existsE body => .existsE CoreSort.object body.toSearch

/-- 单排序公式的搜索翻译始终 sort 正确。 -/
theorem toSearch_wellFormed :
    ∀ formula : Formula,
      Logic.FirstOrder.FormulaWellFormed formula.toSearch
  | .atom symbol arguments => by
      let relation :=
        SearchMaterialization.RelSymbol.predicate
          (predicateSymbol symbol arguments.length)
      have hArguments :
          Logic.FirstOrder.ArgsWellSorted
            (arguments.map Term.toSearch)
            (SearchMaterialization.SearchSignature.relDomain relation) := by
        simpa [relation] using Term.toSearchList_wellSorted arguments
      simpa only [Formula.toSearch] using
        Logic.FirstOrder.FormulaWellFormed.rel
          (σ := SearchMaterialization.SearchSignature)
          relation hArguments
  | .equal left right =>
      .equal left.toSearch_wellSorted right.toSearch_wellSorted
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch_wellFormed
  | .conj left right =>
      .conj left.toSearch_wellFormed right.toSearch_wellFormed
  | .disj left right =>
      .disj left.toSearch_wellFormed right.toSearch_wellFormed
  | .imp left right =>
      .imp left.toSearch_wellFormed right.toSearch_wellFormed
  | .iff left right =>
      .iff left.toSearch_wellFormed right.toSearch_wellFormed
  | .forallE body =>
      by
        simpa [Formula.toSearch] using
          Logic.FirstOrder.FormulaWellFormed.forallE
            (σ := SearchMaterialization.SearchSignature)
            CoreSort.object body.toSearch_wellFormed
  | .existsE body =>
      by
        simpa [Formula.toSearch] using
          Logic.FirstOrder.FormulaWellFormed.existsE
            (σ := SearchMaterialization.SearchSignature)
            CoreSort.object body.toSearch_wellFormed

end Formula

abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature

abbrev SearchEnvAt (M : SearchStructureAt.{x}) :=
  LogicSoundness.SetLevel.EnvAt.{x} M

namespace SearchSemantics

/-- 任意搜索模型中的单排序项解释仍落在对象 sort。 -/
theorem termSort {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M)
    (term : Term) :
    M.sortInterp CoreSort.object
      (Logic.FirstOrder.Term.eval env term.toSearch) :=
  Logic.FirstOrder.Term.eval_sort_of_wellSorted term.toSearch_wellSorted

/-- 搜索环境压入对象值后，对应的 core 环境正好压入同一个值。 -/
theorem coreEnv_push {M : SearchStructureAt.{x}}
    (env : SearchEnvAt.{x} M) (value : M.Domain)
    (hValue : M.sortInterp CoreSort.object value) :
    HostProp.CheckedInput.coreEnvOfSearch
        (env.pushBound CoreSort.object value hValue) =
      (HostProp.CheckedInput.coreEnvOfSearch env).push value :=
  rfl

mutual
  /-- 单排序项的 core/search 翻译在任意搜索模型中语义一致。 -/
  theorem termCoreSearch {M : SearchStructureAt.{x}}
      (env : SearchEnvAt.{x} M) :
      ∀ term : Term,
        Semantics.Term.eval
            (HostProp.CheckedInput.coreEnvOfSearch env) term.toCore =
          Logic.FirstOrder.Term.eval env term.toSearch
    | .bvar index => by
        simp [Term.toCore, Term.toSearch, Semantics.Term.eval,
          Logic.FirstOrder.Term.eval, HostProp.CheckedInput.coreEnvOfSearch]
    | .app symbol arguments => by
        let coreSymbol := Term.functionSymbol symbol arguments.length
        let searchSymbol := FirstOrderProjection.functionSymbol coreSymbol
        have hArguments :
            Logic.FirstOrder.ArgsSatisfy M.sortInterp
              (arguments.map
                (Logic.FirstOrder.Term.eval env ∘ Term.toSearch))
              (SearchMaterialization.SearchSignature.funcDomain
                searchSymbol) := by
          simpa [searchSymbol, coreSymbol, Function.comp_def] using
            Logic.FirstOrder.args_satisfy_of_wellSorted
              (M := M) (env := env)
              (Term.toSearchList_wellSorted arguments)
        simp only [Term.toCore, Term.toSearch, Semantics.Term.eval,
          Logic.FirstOrder.Term.eval]
        rw [Term.toCoreList_eq_map]
        rw [List.map_map, List.map_map]
        have hValues := termListCoreSearch env arguments
        rw [hValues]
        rw [dif_pos hArguments]

  /-- 单排序项列表的 core/search 解释逐项一致。 -/
  theorem termListCoreSearch {M : SearchStructureAt.{x}}
      (env : SearchEnvAt.{x} M) :
      ∀ terms : List Term,
        terms.map (Semantics.Term.eval
          (HostProp.CheckedInput.coreEnvOfSearch env) ∘ Term.toCore) =
        terms.map (Logic.FirstOrder.Term.eval env ∘ Term.toSearch)
    | [] => rfl
    | head :: tail => by
        simp only [List.map_cons, Function.comp_apply]
        rw [termCoreSearch env head, termListCoreSearch env tail]
end

/-- 单排序公式的 core/search 翻译在任意搜索模型中语义一致。 -/
theorem formulaCoreSearch {M : SearchStructureAt.{x}}
    (env : SearchEnvAt.{x} M) :
    ∀ formula : Formula,
      Semantics.Formula.Satisfies
          (HostProp.CheckedInput.coreEnvOfSearch env) formula.toCore ↔
        Logic.FirstOrder.Formula.satisfies env formula.toSearch
  | .atom symbol arguments => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies,
        HostProp.CheckedInput.coreModelOfSearch]
      rw [Term.toCoreList_eq_map]
      rw [List.map_map, List.map_map]
      exact iff_of_eq <| congrArg
        (M.relInterp
          (.predicate (Formula.predicateSymbol symbol arguments.length)))
        (termListCoreSearch env arguments)
  | .equal left right => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      rw [termCoreSearch env left, termCoreSearch env right]
  | .falsum => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          not_congr (formulaCoreSearch env body)
  | .conj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          and_congr
            (formulaCoreSearch env left)
            (formulaCoreSearch env right)
  | .disj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          or_congr
            (formulaCoreSearch env left)
            (formulaCoreSearch env right)
  | .imp left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          imp_congr
            (formulaCoreSearch env left)
            (formulaCoreSearch env right)
  | .iff left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          iff_congr
            (formulaCoreSearch env left)
            (formulaCoreSearch env right)
  | .forallE body => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor <;> intro h value hValue
      · have hCore := h value hValue
        rw [← coreEnv_push env value hValue] at hCore
        exact (formulaCoreSearch (env.pushBound .object value hValue) body).mp
          hCore
      · have hCore :=
          (formulaCoreSearch (env.pushBound .object value hValue) body).mpr
            (h value hValue)
        rw [coreEnv_push env value hValue] at hCore
        exact hCore
  | .existsE body => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        rw [← coreEnv_push env value hValue] at hBody
        exact
          (formulaCoreSearch (env.pushBound .object value hValue) body).mp hBody
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        have hCore :=
          (formulaCoreSearch (env.pushBound .object value hValue) body).mpr hBody
        rw [coreEnv_push env value hValue] at hCore
        exact hCore

end SearchSemantics

namespace Interpretation

/-- 宿主解释直接给出 SearchSignature 的任意 universe 模型。 -/
def searchStructure (interpretation : Interpretation α) :
    SearchStructureAt.{u} where
  Domain := α
  nonempty := ⟨interpretation.default⟩
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨interpretation.default, trivial⟩
  funcInterp := fun symbol arguments =>
    interpretation.function symbol.id arguments
  funcSort := by
    intro symbol arguments hArguments
    trivial
  relInterp := fun relation arguments =>
    match relation with
    | .predicate symbol =>
        interpretation.predicate symbol.id arguments
    | _ => False

/-- 指定单排序 bound 栈的 canonical 宿主环境。 -/
def searchEnv (interpretation : Interpretation α) (bound : Nat → α) :
    SearchEnvAt.{u} interpretation.searchStructure where
  boundVal := fun sort index =>
    if sort = CoreSort.object then bound index else interpretation.default
  freeVal := fun _ _ => interpretation.default
  boundSort := by
    intro sort index
    trivial
  freeSort := by
    intro sort id
    trivial

@[simp]
theorem searchEnv_object (interpretation : Interpretation α)
    (bound : Nat → α) (index : Nat) :
    (interpretation.searchEnv bound).boundVal .object index = bound index := by
  simp [searchEnv]

mutual
  /-- 只要对象 bound 栈一致，单排序项的直接解释与搜索模型解释就一致。 -/
  theorem termSearchOfBound (interpretation : Interpretation α)
      (bound : Nat → α)
      (env : SearchEnvAt.{u} interpretation.searchStructure)
      (hBound :
        ∀ index, env.boundVal CoreSort.object index = bound index) :
      ∀ term : Term,
        Logic.FirstOrder.Term.eval env term.toSearch =
          term.eval interpretation bound
    | .bvar index => by
        simpa [Term.toSearch, Logic.FirstOrder.Term.eval, Term.eval] using
          hBound index
    | .app symbol arguments => by
        simp only [Term.toSearch, Logic.FirstOrder.Term.eval,
          searchStructure, Term.eval, List.map_map]
        exact congrArg (interpretation.function symbol)
          (termListSearchOfBound interpretation bound env hBound arguments)

  /-- 对象 bound 栈一致时，单排序项列表的两种解释逐项一致。 -/
  theorem termListSearchOfBound (interpretation : Interpretation α)
      (bound : Nat → α)
      (env : SearchEnvAt.{u} interpretation.searchStructure)
      (hBound :
        ∀ index, env.boundVal CoreSort.object index = bound index) :
      ∀ terms : List Term,
        terms.map
            (Logic.FirstOrder.Term.eval env ∘ Term.toSearch) =
          Term.evalList interpretation bound terms
    | [] => rfl
    | head :: tail => by
        simp only [List.map_cons, Function.comp_apply, Term.evalList]
        rw [termSearchOfBound interpretation bound env hBound head,
          termListSearchOfBound interpretation bound env hBound tail]
        rfl
end

/-- 只要对象 bound 栈一致，单排序公式的直接解释与搜索模型解释就一致。 -/
theorem formulaSearchOfBound (interpretation : Interpretation α)
    (bound : Nat → α)
    (env : SearchEnvAt.{u} interpretation.searchStructure)
    (hBound :
      ∀ index, env.boundVal CoreSort.object index = bound index) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies env formula.toSearch ↔
        formula.eval interpretation bound
  | .atom symbol arguments => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        searchStructure, Formula.eval, List.map_map]
      exact iff_of_eq <| congrArg (interpretation.predicate symbol)
        (termListSearchOfBound interpretation bound env hBound arguments)
  | .equal left right => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
      rw [termSearchOfBound interpretation bound env hBound left,
        termSearchOfBound interpretation bound env hBound right]
      exact Iff.rfl
  | .falsum => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .truth => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .neg body => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          not_congr
            (formulaSearchOfBound interpretation bound env hBound body)
  | .conj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          and_congr
            (formulaSearchOfBound interpretation bound env hBound left)
            (formulaSearchOfBound interpretation bound env hBound right)
  | .disj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          or_congr
            (formulaSearchOfBound interpretation bound env hBound left)
            (formulaSearchOfBound interpretation bound env hBound right)
  | .imp left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          imp_congr
            (formulaSearchOfBound interpretation bound env hBound left)
            (formulaSearchOfBound interpretation bound env hBound right)
  | .iff left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          iff_congr
            (formulaSearchOfBound interpretation bound env hBound left)
            (formulaSearchOfBound interpretation bound env hBound right)
  | .forallE body => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval, searchStructure]
      constructor
      · intro h value
        exact
          (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value trivial) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mp
            (h value trivial)
      · intro h value hValue
        exact
          (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value hValue) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mpr
            (h value)
  | .existsE body => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval, searchStructure]
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, ?_⟩
        exact
          (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value hValue) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mp hBody
      · rintro ⟨value, hBody⟩
        refine ⟨value, trivial, ?_⟩
        exact
          (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value trivial) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mpr hBody

/-- canonical 宿主环境中的单排序公式解释与直接 Lean 解释一致。 -/
theorem formulaSearch (interpretation : Interpretation α)
    (bound : Nat → α) (formula : Formula) :
    Logic.FirstOrder.Formula.satisfies
        (interpretation.searchEnv bound) formula.toSearch ↔
      formula.eval interpretation bound :=
  formulaSearchOfBound interpretation bound (interpretation.searchEnv bound)
    (interpretation.searchEnv_object bound) formula

end Interpretation

/-- 元层重化的 proof-carrying 单排序一阶输入。 -/
structure CheckedInput (goal : Prop) where
  Domain : Type u
  interpretation : Interpretation Domain
  facts : HostProp.Facts
  premises : List Formula
  target : Formula
  premisesAligned :
    premises.map (Formula.eval interpretation fun _ => interpretation.default) =
      facts.propositions
  targetAligned :
    Formula.eval interpretation (fun _ => interpretation.default) target = goal

namespace CheckedInput

/-- 对齐后的每个一阶前提都有对应的 Lean proof。 -/
theorem premiseHolds {goal : Prop} (input : CheckedInput.{u} goal)
    {formula : Formula} (hFormula : formula ∈ input.premises) :
    Formula.eval input.interpretation
      (fun _ => input.interpretation.default) formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩

/-- 对齐后的目标解释可以回到原 Lean 目标。 -/
theorem goalOfTarget {goal : Prop} (input : CheckedInput.{u} goal)
    (hTarget :
      Formula.eval input.interpretation
        (fun _ => input.interpretation.default) input.target) :
    goal := by
  rw [← input.targetAligned]
  exact hTarget

/-- 一组单排序语法进入整问题 preprocessing source。 -/
def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}

/-- 一组单排序语法进入 SearchSignature 深问题。 -/
def deepProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := target.toSearch
}

/-- 单排序输入进入整问题 preprocessing source。 -/
def sourceProblem {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target

/-- 单排序输入进入 SearchSignature 深问题。 -/
def deepProblem {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.DeepProblem :=
  deepProblemOfSyntax input.premises input.target

/-- 单排序 source/deep 问题之间任意模型 universe 的纯一阶反模型桥。 -/
def firstOrderBridgeAt {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.FirstOrderProblemBridgeAt.{x}
      input.sourceProblem input.deepProblem := by
  constructor
  intro M env hModels hTarget
  refine ⟨{
    model := HostProp.CheckedInput.coreModelOfSearch M
    functionSort := HostProp.CheckedInput.coreModel_functionSort M
    env := HostProp.CheckedInput.coreEnvOfSearch env
    respectsFree := HostProp.CheckedInput.coreEnv_respectsFree env
    satisfies := ?_
  }⟩
  unfold sourceProblem SourcePreprocessing.Problem.refutationSource
  apply HostProp.CheckedInput.coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with
      ⟨source, hSource, rfl⟩
    exact
      (SearchSemantics.formulaCoreSearch env source).mpr <|
        hModels source.toSearch <|
          List.mem_map.mpr ⟨source, hSource, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies
          (HostProp.CheckedInput.coreEnvOfSearch env) input.target.toCore := by
      intro hCore
      exact hTarget <|
        (SearchSemantics.formulaCoreSearch env input.target).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget

/-- 语义蕴涵经 canonical 宿主解释回到原 Lean 目标。 -/
theorem soundOfSearch {goal : Prop} (input : CheckedInput.{u} goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        input.deepProblem.theory input.deepProblem.target) :
    goal := by
  let bound : Nat → input.Domain := fun _ => input.interpretation.default
  have hTarget :
      Logic.FirstOrder.Formula.satisfies
        (input.interpretation.searchEnv bound) input.target.toSearch :=
    hSearch (input.interpretation.searchEnv bound) (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨source, hSource, rfl⟩
      exact
        (input.interpretation.formulaSearch bound source).mpr
          (input.premiseHolds hSource))
  exact input.goalOfTarget <|
    (input.interpretation.formulaSearch bound input.target).mp hTarget

/-- 单排序输入与纯语法快照运行公共纯一阶 checked 主线。 -/
def goalAttemptFromProblems {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "native host first-order") :
    ProveAutoRequest.GoalAttempt goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{u}
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridgeAt
  let attempt :=
    SourcePreprocessing.runFirstOrderProviderAt
      sourceProblem problem bridge settings avatarConfig label
  exact {
    closed :=
      SourcePreprocessing.runFirstOrderProviderClosedAt
        sourceProblem problem settings avatarConfig label
    summary :=
      SourcePreprocessing.runFirstOrderProviderSummary
        sourceProblem problem settings avatarConfig label
    sound := by
      intro hClosed
      have hAttemptClosed :
          LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true := by
        dsimp [attempt]
        exact
          (SourcePreprocessing.runFirstOrderProviderAt_closed
            sourceProblem problem bridge settings avatarConfig label).trans hClosed
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosedAt
          problem attempt hAttemptClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearch hInputSearch
  }

/-- 单排序输入运行公共纯一阶 preprocessing、AVATAR 与 checked DAG。 -/
def goalAttempt {goal : Prop} (input : CheckedInput.{u} goal)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "native host first-order") :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input input.sourceProblem input.deepProblem
    rfl rfl settings avatarConfig label

/-- 元层 provider 使用纯语法快照与默认纯一阶配置的稳定入口。 -/
@[reducible] def defaultGoalAttemptFromProblems {goal : Prop}
    (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input sourceProblem problem hSource hProblem

/-- 元层搜索只引用纯数据 payload/DAG，并保留宿主模型 universe。 -/
def goalAttemptFromReplay {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "native host first-order")) :
    ProveAutoRequest.GoalAttempt goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{u}
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridgeAt
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  let attempt :
      LogicSoundness.SetLevel.BackendAttemptAt.{u} problem :=
    .success (data.backendSuccessAt (replay.refutationBridgeAt bridge))
  exact {
    closed := true
    summary := "DAG reflection/DAG check: closed"
    sound := by
      intro _
      have hAttemptClosed :
          LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true := rfl
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosedAt
          problem attempt hAttemptClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearch hInputSearch
  }

/-- 默认单域一阶 provider 的 proof-carrying replay 稳定入口。 -/
@[reducible] def defaultGoalAttemptFromReplay
    {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "native host first-order")) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromReplay
    input sourceProblem problem hSource hProblem payload search hReplay data

end CheckedInput

/-! ## Lean 元层单域一阶重化 -/

open Lean Meta

initialize registerTraceClass `YesMetaZFC.proveAuto.hostFirstOrder

private structure FunctionEntry where
  head : Expr
  arity : Nat

private structure PredicateEntry where
  head : Expr
  arity : Nat

private structure NativeReifyState where
  domain : Expr
  functions : Array FunctionEntry := #[]
  predicates : Array PredicateEntry := #[]
  bound : Array FVarId := #[]

private abbrev NativeReifyM := StateRefT NativeReifyState MetaM

private def withObjectBinder {β : Type} (binderName : Name)
    (domain : Expr) (action : Expr → NativeReifyM β) : NativeReifyM β := do
  let state ← get
  let (result, nextState) ←
    withLocalDeclD binderName domain fun binder =>
      (action binder).run {
        state with
        bound := state.bound.push binder.fvarId!
      }
  set { nextState with bound := state.bound }
  return result

private def rememberDomain (candidate : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  if ← isProp candidate then
    throwError "proposition binders are not first-order object domains"
  match ← get with
  | none =>
      set (some candidate)
  | some domain =>
      unless ← withTransparency .reducible <| isDefEq domain candidate do
        throwError
          "native host first-order reification found heterogeneous domains \
          {domain} and {candidate}"

private partial def discoverDomain (expression : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isAppOfArity ``Not 1 then
    return ← discoverDomain expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      discoverDomain argument
    return
  if expression.isAppOfArity ``Eq 3 then
    rememberDomain expression.getAppArgs[0]!
    return
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.getAppArgs[0]!
    rememberDomain domain
    let predicate ← whnf expression.getAppArgs[1]!
    match predicate with
    | .lam _ binderDomain body _ =>
        rememberDomain binderDomain
        discoverDomain body
    | _ =>
        return
    return
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        discoverDomain domain
        discoverDomain body
      else
        rememberDomain domain
        discoverDomain body
  | .letE _ _ value body _ =>
      discoverDomain (body.instantiate1 value)
  | _ =>
      return

private def discoverSharedDomain? (expressions : Array Expr) :
    MetaM (Option Expr) := do
  let (_, domain?) ← (expressions.forM discoverDomain).run none
  return domain?

private def objectSuffix (domain expression : Expr) :
    MetaM (Expr × Array Expr) := do
  let arguments := expression.getAppArgs
  let mut split := arguments.size
  while split > 0 do
    let argumentType ← instantiateMVars (← inferType arguments[split - 1]!)
    if ← withTransparency .reducible <| isDefEq argumentType domain then
      split := split - 1
    else
      break
  let mut head := expression.getAppFn
  for index in [0 : split] do
    head := mkApp head arguments[index]!
  if head.hasLooseBVars then
    throwError
      "native host first-order symbols cannot capture object bound variables"
  return (head, arguments.extract split arguments.size)

private def capturesObjectBound (expression : Expr) : NativeReifyM Bool := do
  let state ← get
  let (_, freeVariables) ← expression.collectFVars.run {}
  return state.bound.any fun bound =>
    freeVariables.fvarIds.contains bound

private def internFunction (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.functions.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.functions.size
  set { state with functions := state.functions.push { head, arity } }
  return id

private def internPredicate (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.predicates.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.predicates.size
  set { state with predicates := state.predicates.push { head, arity } }
  return id

private partial def reifyTerm (expression : Expr) : NativeReifyM Term := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  match expression with
  | .bvar _ =>
      throwError "unexpected loose object binder during native reification"
  | .fvar id =>
      let state ← get
      if let some position := state.bound.findIdx? fun bound => bound == id then
        return .bvar (state.bound.size - position - 1)
      let domain := state.domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let functionId ← internFunction expression 0
      return .app functionId []
  | .letE _ _ value body _ =>
      reifyTerm (body.instantiate1 value)
  | _ =>
      let domain := (← get).domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order function symbol captures an object binder"
      let id ← internFunction head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .app id arguments

private partial def reifyFormula (expression : Expr) : NativeReifyM Formula := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Eq 3 then
    let domain := (← get).domain
    let equalityDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq equalityDomain domain do
      throwError "native host first-order equality is outside the object domain"
    return .equal
      (← reifyTerm expression.getAppArgs[1]!)
      (← reifyTerm expression.getAppArgs[2]!)
  if expression.isAppOfArity ``Exists 2 then
    let domain := (← get).domain
    let existentialDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq existentialDomain domain do
      throwError "native host first-order existential is outside the object domain"
    let predicate := expression.getAppArgs[1]!
    let reduced ← whnf predicate
    let body ←
      match reduced with
      | .lam _ binderDomain body _ => do
          unless ← withTransparency .reducible <| isDefEq binderDomain domain do
            throwError "native host first-order existential binder changed domain"
          withObjectBinder `witness binderDomain fun binder =>
            reifyFormula (body.instantiate1 binder)
      | _ =>
          withObjectBinder `witness domain fun binder =>
            reifyFormula (mkApp predicate binder)
    return .existsE body
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        return .imp (← reifyFormula domain) (← reifyFormula body)
      let objectDomain := (← get).domain
      unless ← withTransparency .reducible <| isDefEq domain objectDomain do
        throwError "native host first-order universal changed object domain"
      return .forallE <|
        ← withObjectBinder `object domain fun binder =>
          reifyFormula (body.instantiate1 binder)
  | .letE _ _ value body _ =>
      reifyFormula (body.instantiate1 value)
  | _ =>
      unless ← isProp expression do
        throwError "native host first-order formula expected a proposition"
      let domain := (← get).domain
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order predicate symbol captures an object binder"
      let id ← internPredicate head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .atom id arguments

private def domainLevel (domain : Expr) : MetaM Level := do
  match ← whnf (← inferType domain) with
  | .sort (.succ level) =>
      return level
  | type =>
      throwError "native host first-order domain is not a type: {type}"

private def objectDefault? (domain : Expr) : MetaM (Option Expr) := do
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let localType ← instantiateMVars localDecl.type
    if ← withTransparency .reducible <| isDefEq localType domain then
      return some localDecl.toExpr
  let level ← domainLevel domain
  let sortLevel := Level.succ level
  let nonemptyType := mkApp (mkConst ``Nonempty [sortLevel]) domain
  try
    let nonempty ← synthInstance nonemptyType
    return some <|
      mkApp2 (mkConst ``Classical.choice [sortLevel]) domain nonempty
  catch _ =>
    return none

private partial def applyFromList (domain resultType fallback head : Expr)
    (remaining : Nat) (arguments : Expr) (values : Array Expr := #[]) :
    MetaM Expr := do
  if remaining = 0 then
    let result := mkAppN head values
    let actualType ← instantiateMVars (← inferType result)
    unless ← withTransparency .reducible <| isDefEq actualType resultType do
      throwError
        "native host symbol {head} does not return {resultType}"
    return result
  let domainUniverse ← domainLevel domain
  let .sort resultUniverse ← whnf (← inferType resultType)
    | throwError "native host symbol result is not a type"
  let listDomain := mkApp (mkConst ``List [domainUniverse]) domain
  let motive ←
    withLocalDeclD `items listDomain fun items =>
      mkLambdaFVars #[items] resultType
  let consBranch ←
    withLocalDeclD `head domain fun value =>
      withLocalDeclD `tail listDomain fun tail => do
        let body ← applyFromList domain resultType fallback head
          (remaining - 1) tail (values.push value)
        mkLambdaFVars #[value, tail] body
  return mkAppN
    (mkConst ``List.casesOn [resultUniverse, domainUniverse])
    #[domain, motive, arguments, fallback, consBranch]

private def functionTableExpr (domain default : Expr)
    (entries : Array FunctionEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := default
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native function table index escaped bounds"
        let branch ←
          applyFromList domain domain default entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ level])
          domain condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body

private def predicateTableExpr (domain : Expr)
    (entries : Array PredicateEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := mkConst ``False
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native predicate table index escaped bounds"
        let branch ←
          applyFromList domain (mkSort Level.zero) (mkConst ``False)
            entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ Level.zero])
          (mkSort Level.zero)
          condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body

private def defaultBoundExpr (default : Expr) : MetaM Expr := do
  withLocalDeclD `index (mkConst ``Nat) fun index =>
    mkLambdaFVars #[index] default

private structure CheckedInputExpr where
  expression : Expr
  sourceProblem : SourcePreprocessing.Problem

private def checkedInputExpr?
    (goal : Expr) (proofs factTypes : Array Expr) :
    MetaM (Option CheckedInputExpr) := do
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "start native request: proofs={proofs.size}"
  let expressions := factTypes.push goal
  let some domain ←
      try
        discoverSharedDomain? expressions
      catch error =>
        trace[YesMetaZFC.proveAuto.hostFirstOrder]
          "domain discovery rejected request: {error.toMessageData}"
        pure none
    | return none
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "discovered domain: {domain}"
  let some default ← objectDefault? domain
    | trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "native domain has no local value or Nonempty instance: {domain}"
      return none
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "selected domain default"
  let reified? ←
    try
      let ((premises, target), state) ←
        (do
          let premises ← factTypes.toList.mapM reifyFormula
          let target ← reifyFormula goal
          pure (premises, target)).run { domain := domain }
      pure <| some (premises, target, state)
    catch error =>
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "native reification rejected request: {error.toMessageData}"
      pure none
  let some (premises, target, state) := reified?
    | return none
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "reified syntax: functions={state.functions.size}; \
    predicates={state.predicates.size}; premises={premises.length}"
  let functionTable ← functionTableExpr domain default state.functions
  let predicateTable ← predicateTableExpr domain state.predicates
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "built host interpretation tables"
  let level ← domainLevel domain
  let interpretation :=
    mkAppN (mkConst ``Interpretation.mk [level])
      #[domain, default, functionTable, predicateTable]
  let facts ← HostProp.proofFactsExprWithTypes proofs factTypes
  let premiseList ←
    mkListLit (mkConst ``Formula) (premises.map toExpr)
  let targetFormula := toExpr target
  let bound ← defaultBoundExpr default
  let evalFunction :=
    mkApp3 (mkConst ``Formula.eval [level]) domain interpretation bound
  let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
  let factPropositions ← mkAppM ``HostProp.Facts.propositions #[facts]
  let targetEval :=
    mkApp4 (mkConst ``Formula.eval [level])
      domain interpretation bound targetFormula
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "checking host semantic alignment"
  let hPremises ← mkEqRefl premiseEvals
  unless ← withTransparency .all <| isDefEq (← inferType hPremises)
      (← mkEq premiseEvals factPropositions) do
    throwError "internal HostFirstOrder premise alignment is not definitional"
  let hTarget ← mkEqRefl targetEval
  unless ← withTransparency .all <|
      isDefEq (← inferType hTarget) (← mkEq targetEval goal) do
    throwError
      "internal HostFirstOrder target alignment is not definitional:\n\
      eval={indentExpr targetEval}\ngoal={indentExpr goal}"
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "domain={domain}; functions={state.functions.size}; \
    predicates={state.predicates.size}; premises={premises.length}"
  return some {
    expression := mkAppN (mkConst ``CheckedInput.mk [level])
      #[goal, domain, interpretation, facts, premiseList, targetFormula,
        hPremises, hTarget]
    sourceProblem := CheckedInput.sourceProblemOfSyntax premises target
  }

private def buildAttempt? (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) := do
  unless ← isProp request.goal do
    return none
  let proofs := request.facts
  let factTypes := request.terminal.factPropositions
  let some reified ← checkedInputExpr? request.goal proofs factTypes
    | return none
  let input := reified.expression
  let premiseList ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.premises #[input])
  let targetFormula ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.target #[input])
  let sourceProblem ←
    mkAppM ``CheckedInput.sourceProblemOfSyntax #[premiseList, targetFormula]
  let problem ←
    mkAppM ``CheckedInput.deepProblemOfSyntax #[premiseList, targetFormula]
  let expectedSource ← mkAppM ``CheckedInput.sourceProblem #[input]
  let expectedProblem ← mkAppM ``CheckedInput.deepProblem #[input]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal HostFirstOrder source snapshot lost syntax alignment"
  unless ← isDefEq problem expectedProblem do
    throwError "internal HostFirstOrder deep snapshot lost syntax alignment"
  let hSource ← mkEqRefl sourceProblem
  let hProblem ← mkEqRefl problem
  let attempt ←
    match SourcePreprocessing.runFirstOrder reified.sourceProblem with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr request.goal error.label
    | Except.ok firstOrder =>
        match firstOrder.result.runAvatar? with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr request.goal error.label
        | Except.ok artifact =>
            let settingsExpr :=
              toExpr (({} : SourcePreprocessing.FirstOrderSettings).toSettings)
            let replay ←
              KernelReplay.firstOrderReplayExprs sourceProblem problem
                settingsExpr firstOrder.result.checked.payload artifact
                "native host first-order"
            mkAppM ``CheckedInput.defaultGoalAttemptFromReplay
              #[input, sourceProblem, problem, hSource, hProblem,
                replay.payload, replay.search, replay.checked, replay.data]
  let attempt ← instantiateMVars attempt
  let (_, freeVariables) ← attempt.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HostFirstOrder request leaked a temporary free variable: \
        {freeVariable.name}"
  return some attempt

/-- 单域一阶宿主公式优先于纯命题 atom 骨架进入 checked provider。 -/
def contextProvider : ProveAutoRequest.ContextProvider where
  priority := 100
  requirement := .hostObjectSyntax
  build? := buildAttempt?

register_prove_auto_context_provider contextProvider

end HostFirstOrder
end Automation
end YesMetaZFC
