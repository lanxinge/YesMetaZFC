import YesMetaZFC.Automation.CoreNormalForm.AntiPrenexSoundness

/-!
# Core normal form definitional CNF

本模块建立新语义主线使用的可检查定义性 CNF 数据层。它只处理已经处在 NNF
中的量词自由矩阵，通过 Tseitin 定义避免析取/合取分配爆炸；等词原子始终作为
`Atom.equal` 字面量出现在输出子句中，不会被定义谓词遮蔽。开放矩阵中的 typed
自由变量会显式成为定义谓词参数，定义不会退化成与环境无关的零元命题。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm

namespace DefinitionalCnf

/-- 定义性 CNF 的执行配置。 -/
structure Config where
  maxDefinitions : Nat := 4096
  maxClauses : Nat := 16384
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 公式引用：常量或已经可见的 NNF 字面量。 -/
inductive Ref where
  | truth (value : Bool)
  | lit (literal : Literal)
  deriving Repr, Inhabited, Lean.ToExpr

/-- 字面量是否是等词原子。 -/
def literalIsEquality (literal : Literal) : Bool :=
  match literal.atom with
  | Atom.equal .. => true
  | _ => false

/-- 字面量数组的透明结构相等。 -/
def literalArrayEq (left right : Array Literal) : Bool :=
  SyntaxEq.literalListEq left.toList right.toList

namespace Ref

/-- 引用的透明结构相等。 -/
def eq : Ref → Ref → Bool
  | truth left, truth right => left == right
  | lit left, lit right => SyntaxEq.literalEq left right
  | _, _ => false

/-- 翻转公式引用极性。 -/
def negate : Ref → Ref
  | truth value => truth (!value)
  | lit literal => lit literal.negate

/-- 引用是否是等词字面量。 -/
def isEquality : Ref → Bool
  | truth _ => false
  | lit literal => literalIsEquality literal

end Ref

/-- 定义谓词显式依赖的 typed 自由变量。 -/
structure FreeVarParam where
  sort : CoreSort
  varId : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace FreeVarParam

/-- 自由变量参数对应的核心项。 -/
def term (parameter : FreeVarParam) : Term :=
  Term.fvar parameter.sort parameter.varId

/-- 在保持首次出现顺序的前提下插入自由变量参数。 -/
def insert (parameter : FreeVarParam) (parameters : List FreeVarParam) :
    List FreeVarParam :=
  if parameters.contains parameter then parameters else parameters ++ [parameter]

/-- 合并两个自由变量参数表，保持首次出现顺序并去重。 -/
def merge (left right : List FreeVarParam) : List FreeVarParam :=
  right.foldl (fun parameters parameter => insert parameter parameters) left

/-- 自由变量参数表是否无重复。 -/
def distinct (parameters : List FreeVarParam) : Bool :=
  parameters.Pairwise fun left right => left != right

/-- 参数对应的谓词输入 sort。 -/
def sorts (parameters : List FreeVarParam) : List CoreSort :=
  parameters.map (fun parameter => parameter.sort)

/-- 参数对应的谓词实参。 -/
def terms (parameters : List FreeVarParam) : List Term :=
  parameters.map term

end FreeVarParam

mutual
  /-- 核心项中自由变量的首次出现有序表。 -/
  def Term.freeVarParams : Term → List FreeVarParam
    | Term.bvar .. => []
    | Term.fvar sort varId => [{ sort := sort, varId := varId }]
    | Term.app _ args => Term.freeVarParamsList args
    | Term.apply fn arg =>
        FreeVarParam.merge (Term.freeVarParams fn) (Term.freeVarParams arg)
    | Term.bool _ => []
    | Term.notE body => Term.freeVarParams body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
    | Term.quote formula => Formula.freeVarParams formula
    | Term.lam _ _ body => Term.freeVarParams body
    | Term.ite _ condition thenTerm elseTerm =>
        FreeVarParam.merge (Formula.freeVarParams condition)
          (FreeVarParam.merge (Term.freeVarParams thenTerm)
            (Term.freeVarParams elseTerm))

  /-- 核心公式中自由变量的首次出现有序表。 -/
  def Formula.freeVarParams : Formula → List FreeVarParam
    | Formula.trueE => []
    | Formula.falseE => []
    | Formula.atom _ args => Term.freeVarParamsList args
    | Formula.equal _ left right =>
        FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
    | Formula.boolTerm term => Term.freeVarParams term
    | Formula.neg body => Formula.freeVarParams body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        FreeVarParam.merge (Formula.freeVarParams left) (Formula.freeVarParams right)
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Formula.freeVarParams body

  /-- 核心项列表中自由变量的首次出现有序表。 -/
  def Term.freeVarParamsList : List Term → List FreeVarParam
    | [] => []
    | term :: rest =>
        FreeVarParam.merge (Term.freeVarParams term) (Term.freeVarParamsList rest)
end

/-- NNF 原子中的自由变量参数。 -/
def atomFreeVarParams : Atom → List FreeVarParam
  | Atom.predicate _ args => Term.freeVarParamsList args
  | Atom.equal _ left right =>
      FreeVarParam.merge (Term.freeVarParams left) (Term.freeVarParams right)
  | Atom.boolTerm term => Term.freeVarParams term

/-- NNF 字面量中的自由变量参数。 -/
def literalFreeVarParams (literal : Literal) : List FreeVarParam :=
  atomFreeVarParams literal.atom

/-- NNF 中自由变量的首次出现有序表。 -/
def nnfFreeVarParams : Nnf → List FreeVarParam
  | Nnf.trueE => []
  | Nnf.falseE => []
  | Nnf.lit literal => literalFreeVarParams literal
  | Nnf.conj left right
  | Nnf.disj left right =>
      FreeVarParam.merge (nnfFreeVarParams left) (nnfFreeVarParams right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body =>
      nnfFreeVarParams body

/-- 定义谓词元数据。 -/
structure Definition where
  index : Nat
  predicate : PredicateSymbol
  contextSorts : List CoreSort
  freeVarParams : List FreeVarParam
  body : Nnf
  deriving Repr, Lean.ToExpr

namespace Definition

/-- 定义谓词的完整输入 sort：局部绑定上下文在前，自由变量参数在后。 -/
def inputSorts (definition : Definition) : List CoreSort :=
  definition.contextSorts ++ FreeVarParam.sorts definition.freeVarParams

/-- 定义谓词的完整实参：局部无名参数在前，typed 自由变量参数在后。 -/
def arguments (definition : Definition) : List Term :=
  FirstOrderProjection.contextArgs definition.contextSorts ++
    FreeVarParam.terms definition.freeVarParams

/-- 定义谓词在当前上下文中的正字面量。 -/
def literal (definition : Definition) (positive : Bool := true) : Literal :=
  {
    positive := positive
    atom := Atom.predicate definition.predicate definition.arguments
  }

/-- 定义谓词对应的 NNF 原子。 -/
def atomNnf (definition : Definition) : Nnf :=
  Nnf.lit (definition.literal true)

/-- 定义公式：只闭合局部上下文，typed 自由变量继续作为谓词参数依赖。 -/
def formula (definition : Definition) : Formula :=
  FirstOrderProjection.closeForall definition.contextSorts
    (Formula.iffE (definition.literal true).toFormula definition.body.toFormula)

/-- 当前定义是否直接遮蔽了一个等词字面量。 -/
def hidesEqualityLiteral (definition : Definition) : Bool :=
  match definition.body with
  | Nnf.lit literal => literalIsEquality literal
  | _ => false

/-- 定义元数据的可计算检查。 -/
def check (definition : Definition) : Bool :=
  definition.predicate.role == PredicateRole.definition &&
    definition.freeVarParams == nnfFreeVarParams definition.body &&
      FreeVarParam.distinct definition.freeVarParams &&
        definition.predicate.arity == definition.inputSorts.length &&
          definition.predicate.inputSorts == definition.inputSorts &&
            definition.body.quantifierFree &&
              !definition.hidesEqualityLiteral &&
                Formula.checkWith definition.contextSorts definition.body.toFormula &&
                  Formula.checkWith definition.contextSorts
                    (definition.literal true).toFormula &&
                    definition.formula.check?

/-- 定义元数据透明结构相等。 -/
def eq (left right : Definition) : Bool :=
  left.index == right.index &&
    left.predicate == right.predicate &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.nnfEq left.body right.body

/-- 定义列表透明结构相等。 -/
def listEq : List Definition → List Definition → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false

/-- 定义数组透明结构相等。 -/
def arrayEq (left right : Array Definition) : Bool :=
  listEq left.toList right.toList

end Definition

mutual
  /-- 项中出现的最大谓词编号后继。 -/
  def Term.maxPredicateIdSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar .. => 0
    | Term.app _ args => Term.maxPredicateListIdSucc args
    | Term.apply fn arg =>
        Nat.max (Term.maxPredicateIdSucc fn) (Term.maxPredicateIdSucc arg)
    | Term.bool _ => 0
    | Term.notE body => Term.maxPredicateIdSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
    | Term.quote formula => Formula.maxPredicateIdSucc formula
    | Term.lam _ _ body => Term.maxPredicateIdSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (Formula.maxPredicateIdSucc condition)
          (Nat.max (Term.maxPredicateIdSucc thenTerm)
            (Term.maxPredicateIdSucc elseTerm))

  /-- 公式中出现的最大谓词编号后继。 -/
  def Formula.maxPredicateIdSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom predicate args =>
        Nat.max (predicate.id + 1) (Term.maxPredicateListIdSucc args)
    | Formula.equal _ left right =>
        Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
    | Formula.boolTerm term => Term.maxPredicateIdSucc term
    | Formula.neg body => Formula.maxPredicateIdSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Nat.max (Formula.maxPredicateIdSucc left) (Formula.maxPredicateIdSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Formula.maxPredicateIdSucc body

  /-- 项列表中出现的最大谓词编号后继。 -/
  def Term.maxPredicateListIdSucc : List Term → Nat
    | [] => 0
    | term :: rest =>
        Nat.max (Term.maxPredicateIdSucc term) (Term.maxPredicateListIdSucc rest)
end

/-- 原子中出现的最大谓词编号后继。 -/
def atomMaxPredicateIdSucc : Atom → Nat
  | Atom.predicate predicate args =>
      Nat.max (predicate.id + 1) (Term.maxPredicateListIdSucc args)
  | Atom.equal _ left right =>
      Nat.max (Term.maxPredicateIdSucc left) (Term.maxPredicateIdSucc right)
  | Atom.boolTerm term => Term.maxPredicateIdSucc term

/-- 字面量中出现的最大谓词编号后继。 -/
def literalMaxPredicateIdSucc (literal : Literal) : Nat :=
  atomMaxPredicateIdSucc literal.atom

/-- NNF 中出现的最大谓词编号后继。 -/
def nnfMaxPredicateIdSucc : Nnf → Nat
  | Nnf.trueE => 0
  | Nnf.falseE => 0
  | Nnf.lit literal => literalMaxPredicateIdSucc literal
  | Nnf.conj left right
  | Nnf.disj left right =>
      Nat.max (nnfMaxPredicateIdSucc left) (nnfMaxPredicateIdSucc right)
  | Nnf.forallE _ body
  | Nnf.existsE _ body =>
      nnfMaxPredicateIdSucc body

/-- 从一组引用生成一个子句；返回 `none` 表示该子句被 `true` 化简掉。 -/
def clauseOfRefsAux (acc : List Literal) : List Ref → Option Clause
  | [] => some acc.reverse.toArray
  | Ref.truth true :: _ => none
  | Ref.truth false :: rest => clauseOfRefsAux acc rest
  | Ref.lit literal :: rest => clauseOfRefsAux (literal :: acc) rest

/-- 从一组引用生成一个子句；返回 `none` 表示该子句被 `true` 化简掉。 -/
def clauseOfRefs (refs : List Ref) : Option Clause :=
  clauseOfRefsAux [] refs

/-- 从一组引用生成零个或一个子句。 -/
def clausesOfRefs (refs : List Ref) : ClauseSet :=
  match clauseOfRefs refs with
  | some clause => #[clause]
  | none => #[]

/-- 定义性 CNF 构造状态。 -/
structure BuildState where
  nextPredicate : Nat
  definitions : Array Definition := #[]
  deriving Repr, Lean.ToExpr

abbrev BuildM := StateM BuildState

/-- 引入一个新的定义谓词。 -/
def freshDefinition (contextSorts : List CoreSort) (body : Nnf) : BuildM Literal := do
  let state ← get
  let freeVarParams := nnfFreeVarParams body
  let inputSorts := contextSorts ++ FreeVarParam.sorts freeVarParams
  let predicate : PredicateSymbol := {
    id := state.nextPredicate
    arity := inputSorts.length
    role := PredicateRole.definition
    inputSorts := inputSorts
  }
  let definition : Definition := {
    index := state.definitions.size
    predicate := predicate
    contextSorts := contextSorts
    freeVarParams := freeVarParams
    body := body
  }
  set ({
    nextPredicate := state.nextPredicate + 1
    definitions := state.definitions.push definition
  } : BuildState)
  pure (definition.literal true)

/-- 单个子公式构造结果。 -/
structure BuildCore where
  ref : Ref
  clauses : ClauseSet
  deriving Repr, Inhabited, Lean.ToExpr

/-- 构造 `d ↔ (left ∧ right)` 的定义子句。 -/
def conjDefinitionClauses (defLit : Literal) (left right : Ref) : ClauseSet :=
  clausesOfRefs [Ref.lit defLit.negate, left] ++
    clausesOfRefs [Ref.lit defLit.negate, right] ++
      clausesOfRefs [Ref.lit defLit, left.negate, right.negate]

/-- 构造 `d ↔ (left ∨ right)` 的定义子句。 -/
def disjDefinitionClauses (defLit : Literal) (left right : Ref) : ClauseSet :=
  clausesOfRefs [Ref.lit defLit, left.negate] ++
    clausesOfRefs [Ref.lit defLit, right.negate] ++
      clausesOfRefs [Ref.lit defLit.negate, left, right]

/-- 递归构造定义性 CNF 的内部引用。 -/
def buildCore (contextSorts : List CoreSort) : Nnf → BuildM BuildCore
  | Nnf.trueE => pure { ref := Ref.truth true, clauses := #[] }
  | Nnf.falseE => pure { ref := Ref.truth false, clauses := #[] }
  | Nnf.lit literal => pure { ref := Ref.lit literal, clauses := #[] }
  | Nnf.conj left right => do
      let leftResult ← buildCore contextSorts left
      let rightResult ← buildCore contextSorts right
      let defLit ← freshDefinition contextSorts (Nnf.conj left right)
      let definitionClauses :=
        conjDefinitionClauses defLit leftResult.ref rightResult.ref
      pure {
        ref := Ref.lit defLit
        clauses := leftResult.clauses ++ rightResult.clauses ++ definitionClauses
      }
  | Nnf.disj left right => do
      let leftResult ← buildCore contextSorts left
      let rightResult ← buildCore contextSorts right
      let defLit ← freshDefinition contextSorts (Nnf.disj left right)
      let definitionClauses :=
        disjDefinitionClauses defLit leftResult.ref rightResult.ref
      pure {
        ref := Ref.lit defLit
        clauses := leftResult.clauses ++ rightResult.clauses ++ definitionClauses
      }
  | Nnf.forallE .. => pure { ref := Ref.truth false, clauses := #[#[]] }
  | Nnf.existsE .. => pure { ref := Ref.truth false, clauses := #[#[]] }

/-- 定义性 CNF 的原始构造输出。 -/
structure CoreResult where
  root : Ref
  clauses : ClauseSet
  definitions : Array Definition
  deriving Repr, Lean.ToExpr

/-- 运行内部构造器。 -/
def buildCoreResult (contextSorts : List CoreSort) (source : Nnf) : CoreResult :=
  let initial : BuildState := {
    nextPredicate := nnfMaxPredicateIdSucc source
  }
  let (core, state) := (buildCore contextSorts source).run initial
  {
    root := core.ref
    clauses := core.clauses ++ clausesOfRefs [core.ref]
    definitions := state.definitions
  }

/-- 从 NNF 收集源等词字面量。 -/
partial def sourceEqualityLiterals : Nnf → Array Literal
  | Nnf.trueE => #[]
  | Nnf.falseE => #[]
  | Nnf.lit literal => if literalIsEquality literal then #[literal] else #[]
  | Nnf.conj left right
  | Nnf.disj left right =>
      sourceEqualityLiterals left ++ sourceEqualityLiterals right
  | Nnf.forallE _ body
  | Nnf.existsE _ body =>
      sourceEqualityLiterals body

/-- 从字句集中收集可见等词字面量。 -/
def visibleEqualityLiterals (clauses : ClauseSet) : Array Literal :=
  Id.run do
    let mut out := #[]
    for clause in clauses do
      for literal in clause do
        if literalIsEquality literal then
          out := out.push literal
    return out

/-- 字面量是否出现在数组中。 -/
def literalMem (literal : Literal) (literals : Array Literal) : Bool :=
  literals.toList.any (fun candidate => SyntaxEq.literalEq literal candidate)

/-- 源中的每个等词字面量是否仍在输出 CNF 中可见。 -/
def equalityVisibilityOk (source : Nnf) (clauses : ClauseSet) : Bool :=
  let visible := visibleEqualityLiterals clauses
  (sourceEqualityLiterals source).toList.all (fun literal => literalMem literal visible)

/-- 判断定义预算和子句预算是否满足。 -/
def budgetOk (config : Config) (definitions : Array Definition) (clauses : ClauseSet) : Bool :=
  definitions.size <= config.maxDefinitions &&
    clauses.size <= config.maxClauses

/-- 逐字段比较公共 stats。 -/
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel

/-- 构造定义性 CNF 的摘要。 -/
def statsOf (config : Config) (source : Nnf) (clauses : ClauseSet)
    (definitions : Array Definition) : Certificate.Stats :=
  {
    steps := definitions.size
    clauses := clauses.size
    literals := clauses.literalCount
    generated := source.size
    retained := clauses.size
    verified := visibleEqualityLiterals clauses |>.size
    residuals := if budgetOk config definitions clauses then 0 else 1
    fuel := config.maxDefinitions
  }

end DefinitionalCnf

/-- 定义性 CNF 的可检查 payload。 -/
structure DefinitionalCnfPayload where
  config : DefinitionalCnf.Config
  contextSorts : List CoreSort
  source : Nnf
  sourceFreeVarParams : List DefinitionalCnf.FreeVarParam
  root : DefinitionalCnf.Ref
  clauses : ClauseSet
  definitions : Array DefinitionalCnf.Definition
  sourceEqualityLiterals : Array Literal
  visibleEqualityLiterals : Array Literal
  sourceSize : Nat
  definitionCount : Nat
  clauseCount : Nat
  literalCount : Nat
  equalityVisible : Bool
  budgetSatisfied : Bool
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr

namespace DefinitionalCnfPayload

/-- 从量词自由 NNF 构造定义性 CNF payload。 -/
def build (config : DefinitionalCnf.Config) (contextSorts : List CoreSort)
    (source : Nnf) : DefinitionalCnfPayload :=
  let core := DefinitionalCnf.buildCoreResult contextSorts source
  let sourceEquality := DefinitionalCnf.sourceEqualityLiterals source
  let visibleEquality := DefinitionalCnf.visibleEqualityLiterals core.clauses
  let equalityVisible := DefinitionalCnf.equalityVisibilityOk source core.clauses
  let budgetSatisfied := DefinitionalCnf.budgetOk config core.definitions core.clauses
  {
    config := config
    contextSorts := contextSorts
    source := source
    sourceFreeVarParams := DefinitionalCnf.nnfFreeVarParams source
    root := core.root
    clauses := core.clauses
    definitions := core.definitions
    sourceEqualityLiterals := sourceEquality
    visibleEqualityLiterals := visibleEquality
    sourceSize := source.size
    definitionCount := core.definitions.size
    clauseCount := core.clauses.size
    literalCount := core.clauses.literalCount
    equalityVisible := equalityVisible
    budgetSatisfied := budgetSatisfied
    stats := DefinitionalCnf.statsOf config source core.clauses core.definitions
  }

/-- 定义性 CNF payload 的透明结构相等。 -/
def eq (left right : DefinitionalCnfPayload) : Bool :=
  left.config == right.config &&
    left.contextSorts == right.contextSorts &&
      SyntaxEq.nnfEq left.source right.source &&
        left.sourceFreeVarParams == right.sourceFreeVarParams &&
          DefinitionalCnf.Ref.eq left.root right.root &&
            ClauseSet.eq left.clauses right.clauses &&
              DefinitionalCnf.Definition.arrayEq left.definitions right.definitions &&
                DefinitionalCnf.literalArrayEq left.sourceEqualityLiterals
                  right.sourceEqualityLiterals &&
                  DefinitionalCnf.literalArrayEq left.visibleEqualityLiterals
                    right.visibleEqualityLiterals &&
                    left.sourceSize == right.sourceSize &&
                      left.definitionCount == right.definitionCount &&
                        left.clauseCount == right.clauseCount &&
                          left.literalCount == right.literalCount &&
                            left.equalityVisible == right.equalityVisible &&
                              left.budgetSatisfied == right.budgetSatisfied &&
                                DefinitionalCnf.statsEq left.stats right.stats

/--
定义性 CNF payload 中被语义证明实际消费的结构相等。

其余字段只服务构造审计，不进入 kernel-facing soundness 边界。
-/
def semanticEq (left right : DefinitionalCnfPayload) : Bool :=
  DefinitionalCnf.Ref.eq left.root right.root &&
    (ClauseSet.eq left.clauses right.clauses &&
      DefinitionalCnf.Definition.arrayEq left.definitions right.definitions)

/-- 定义性 CNF payload 的 kernel-facing 语义 checker。 -/
def check (payload : DefinitionalCnfPayload) : Bool :=
  let expected := build payload.config payload.contextSorts payload.source
  payload.source.quantifierFree &&
    (Formula.checkWith payload.contextSorts payload.source.toFormula &&
      (payload.definitions.toList.all DefinitionalCnf.Definition.check &&
        semanticEq payload expected))

/--
定义性 CNF payload 的完整构造审计。

这里保留自由变量摘要、字句语法、等词可见性、预算、统计与全部字段复算；这些审计
不参与语义 soundness，因此可以继续消费只在元层高效执行的收集器。
-/
def auditCheck (payload : DefinitionalCnfPayload) : Bool :=
  let expected := build payload.config payload.contextSorts payload.source
  check payload &&
    (payload.equalityVisible &&
      (payload.budgetSatisfied &&
        (payload.sourceFreeVarParams == DefinitionalCnf.nnfFreeVarParams payload.source &&
          (DefinitionalCnf.FreeVarParam.distinct payload.sourceFreeVarParams &&
            (Formula.checkWith payload.contextSorts payload.clauses.toFormula &&
              (DefinitionalCnf.equalityVisibilityOk payload.source payload.clauses &&
                eq payload expected))))))

/-- 构造已通过 checker 的定义性 CNF payload。 -/
def mk? (config : DefinitionalCnf.Config) (contextSorts : List CoreSort)
    (source : Nnf) :
    Option (Certificate.Checked DefinitionalCnfPayload DefinitionalCnfPayload.check) :=
  Certificate.Checked.mk? (check := DefinitionalCnfPayload.check)
    (build config contextSorts source)

end DefinitionalCnfPayload

/-- 定义性 CNF 的总结果。 -/
structure DefinitionalCnfResult where
  payload : DefinitionalCnfPayload
  checked? : Option (Certificate.Checked DefinitionalCnfPayload DefinitionalCnfPayload.check)

namespace DefinitionalCnfResult

/-- 从量词自由 NNF 构造定义性 CNF 结果。 -/
def build (config : DefinitionalCnf.Config) (contextSorts : List CoreSort)
    (source : Nnf) : DefinitionalCnfResult :=
  let payload := DefinitionalCnfPayload.build config contextSorts source
  {
    payload := payload
    checked? := Certificate.Checked.mk? (check := DefinitionalCnfPayload.check) payload
  }

/-- 定义性 CNF 结果中的子句集。 -/
def clauses (result : DefinitionalCnfResult) : ClauseSet :=
  result.payload.clauses

/-- 定义性 CNF 结果中的定义表。 -/
def definitions (result : DefinitionalCnfResult) :
    Array DefinitionalCnf.Definition :=
  result.payload.definitions

/-- 定义性 CNF 结果是否携带 checked payload。 -/
def isChecked (result : DefinitionalCnfResult) : Bool :=
  result.checked?.isSome

/-- 检查 result 的 payload 与 checked witness 是否一致。 -/
def check (result : DefinitionalCnfResult) : Bool :=
  DefinitionalCnfPayload.auditCheck result.payload &&
    match result.checked? with
    | some checked => DefinitionalCnfPayload.eq result.payload checked.payload
    | none => false

end DefinitionalCnfResult

/-- 默认配置下的定义性 CNF 入口。 -/
def definitionalCnf (source : Nnf) : DefinitionalCnfResult :=
  DefinitionalCnfResult.build {} [] source

/-- 指定上下文和配置的定义性 CNF 入口。 -/
def definitionalCnfWith (config : DefinitionalCnf.Config)
    (contextSorts : List CoreSort) (source : Nnf) : DefinitionalCnfResult :=
  DefinitionalCnfResult.build config contextSorts source

end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
