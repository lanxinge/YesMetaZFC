import Lean

/-!
# MF1 自动化：超消元核心语法层

本模块是后端共享的纯语法内核，不依赖 MF1 章节对象语言。它分成两层：

* `CoreSyntax.Term` / `CoreSyntax.Formula` 是面向 FOOL 与 lambda 扩展的统一 AST；
* `CoreSyntax.Search` 是当前子句化、合一、叠加演算消费的 clause/search 子语法。

Skolem 记录和算法使用这里统一维护的项、文字、字句等语法事实。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax

/-- 后端内部变量编号。 -/
abbrev VarId := Nat

/-- 函数、谓词等符号编号。 -/
abbrev SymbolId := Nat

/-- 核心语法的简单 sort。`prop` 用于对象命题，`bool` 用于 FOOL 的布尔项。 -/
inductive CoreSort where
  | object
  | bool
  | prop
  | named (id : Nat)
  | arrow (domain codomain : CoreSort)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace CoreSort

/-- 多元函数 sort 的右结合箭头编码。 -/
def arrowFrom : List CoreSort → CoreSort → CoreSort
  | [], result => result
  | arg :: rest, result => CoreSort.arrow arg (arrowFrom rest result)

/-- 若 sort 是函数 sort，取出定义域和值域。 -/
def arrow? : CoreSort → Option (CoreSort × CoreSort)
  | CoreSort.arrow domain codomain => some (domain, codomain)
  | _ => none

end CoreSort

/-- 核心函数符号的来源角色。 -/
inductive FunctionRole where
  | parameter
  | skolem
  | definition
  | choice
  | builtin
  | extensionalWitness
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

/-- 核心谓词符号的来源角色。 -/
inductive PredicateRole where
  | relation
  | equalityProxy
  | membership
  | definition
  | builtin
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

/-- 核心函数符号。`inputSorts = []` 表示旧的一阶无类型后端暂未携带 sort 信息。 -/
structure FunctionSymbol where
  id : SymbolId
  arity : Nat
  role : FunctionRole
  inputSorts : List CoreSort := []
  outputSort : CoreSort := CoreSort.object
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace FunctionSymbol

/-- 函数符号的 sort 摘要。 -/
def sort (symbol : FunctionSymbol) : CoreSort :=
  CoreSort.arrowFrom symbol.inputSorts symbol.outputSort

/-- 元数与输入 sort 列表一致，或者该符号尚处在旧无类型搜索层。 -/
def arityOk (symbol : FunctionSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity

end FunctionSymbol

/-- 核心谓词符号。`inputSorts = []` 表示旧的一阶无类型后端暂未携带 sort 信息。 -/
structure PredicateSymbol where
  id : SymbolId
  arity : Nat
  role : PredicateRole
  inputSorts : List CoreSort := []
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace PredicateSymbol

/-- 元数与输入 sort 列表一致，或者该谓词尚处在旧无类型搜索层。 -/
def arityOk (symbol : PredicateSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity

end PredicateSymbol

/-- 绑定器种类。 -/
inductive BinderKind where
  | forallE
  | existsE
  | lambda
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

mutual
  /--
  核心项语法。

  `quote` 是 FOOL 的公式作布尔项入口；`boolTerm` 在 `Formula` 侧提供反向入口。
  FOOL 布尔连接词在项层直接作为一等构造保存，避免后端通过 builtin symbol 猜测语义。
  lambda 采用 de Bruijn 风格，`body` 中最近绑定变量为 `bvar domain 0`。
  -/
  inductive Term where
    | bvar (sort : CoreSort) (index : Nat)
    | fvar (sort : CoreSort) (id : VarId)
    | app (symbol : FunctionSymbol) (args : List Term)
    | apply (fn arg : Term)
    | bool (value : Bool)
    | notE (body : Term)
    | andE (left right : Term)
    | orE (left right : Term)
    | impE (left right : Term)
    | iffE (left right : Term)
    | quote (formula : Formula)
    | lam (domain codomain : CoreSort) (body : Term)
    | ite (sort : CoreSort) (condition : Formula) (thenTerm elseTerm : Term)
    deriving Repr, Inhabited, Lean.ToExpr

  /--
  核心公式语法。

  `boolTerm` 是 FOOL 的布尔项作公式入口。量词同样采用 de Bruijn 风格。
  -/
  inductive Formula where
    | trueE
    | falseE
    | atom (predicate : PredicateSymbol) (args : List Term)
    | equal (sort : CoreSort) (left right : Term)
    | boolTerm (term : Term)
    | neg (body : Formula)
    | imp (left right : Formula)
    | conj (left right : Formula)
    | disj (left right : Formula)
    | iffE (left right : Formula)
    | forallE (sort : CoreSort) (body : Formula)
    | existsE (sort : CoreSort) (body : Formula)
    deriving Repr, Inhabited, Lean.ToExpr
end

mutual
  /-- 核心项的粗略节点数。 -/
  partial def Term.size : Term → Nat
    | Term.bvar .. => 1
    | Term.fvar .. => 1
    | Term.app _ args => args.foldl (fun acc term => acc + Term.size term) 1
    | Term.apply fn arg => Term.size fn + Term.size arg + 1
    | Term.bool _ => 1
    | Term.notE body => Term.size body + 1
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Term.size left + Term.size right + 1
    | Term.quote formula => Formula.size formula + 1
    | Term.lam _ _ body => Term.size body + 1
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.size condition + Term.size thenTerm + Term.size elseTerm + 1

  /-- 核心公式的粗略节点数。 -/
  partial def Formula.size : Formula → Nat
    | Formula.trueE => 1
    | Formula.falseE => 1
    | Formula.atom _ args => args.foldl (fun acc term => acc + Term.size term) 1
    | Formula.equal _ left right => Term.size left + Term.size right + 1
    | Formula.boolTerm term => Term.size term + 1
    | Formula.neg body => Formula.size body + 1
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Formula.size left + Formula.size right + 1
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.size body + 1
end

namespace TypeCheck

/-- 本地绑定上下文查找；上下文按 De Bruijn 索引从近到远排列。 -/
def lookupBound? : List CoreSort → Nat → Option CoreSort
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookupBound? rest index

/-- sort 列表的透明相等。 -/
def sortListEq (left right : List CoreSort) : Bool :=
  decide (left = right)

/-- 检查实参 sort 是否匹配显式声明；空声明表示旧无类型符号只检查元数。 -/
def inputSortsOk (declared actual : List CoreSort) : Bool :=
  declared.isEmpty || sortListEq declared actual

end TypeCheck

mutual
  /-- 在给定本地绑定上下文下推断核心项 sort；失败表示 sort 或局部索引不合法。 -/
  def Term.inferSortWith (bound : List CoreSort) : Term → Option CoreSort
    | Term.bvar sort index => do
        let expected ← TypeCheck.lookupBound? bound index
        if expected == sort then
          some sort
        else
          none
    | Term.fvar sort _ => some sort
    | Term.app symbol args => do
        if !symbol.arityOk || args.length != symbol.arity then
          none
        else
          let argSorts ← Term.inferSortListWith bound args
          if TypeCheck.inputSortsOk symbol.inputSorts argSorts then
            some symbol.outputSort
          else
            none
    | Term.apply fn arg => do
        let fnSort ← Term.inferSortWith bound fn
        let argSort ← Term.inferSortWith bound arg
        match fnSort.arrow? with
        | some (domain, codomain) =>
            if argSort == domain then some codomain else none
        | none => none
    | Term.bool _ => some CoreSort.bool
    | Term.notE body => do
        let sort ← Term.inferSortWith bound body
        if sort == CoreSort.bool then some CoreSort.bool else none
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => do
        let leftSort ← Term.inferSortWith bound left
        let rightSort ← Term.inferSortWith bound right
        if leftSort == CoreSort.bool && rightSort == CoreSort.bool then
          some CoreSort.bool
        else
          none
    | Term.quote formula =>
        if Formula.checkWith bound formula then some CoreSort.bool else none
    | Term.lam domain codomain body => do
        let bodySort ← Term.inferSortWith (domain :: bound) body
        if bodySort == codomain then
          some (CoreSort.arrow domain codomain)
        else
          none
    | Term.ite sort condition thenTerm elseTerm => do
        if !Formula.checkWith bound condition then
          none
        else
          let thenSort ← Term.inferSortWith bound thenTerm
          let elseSort ← Term.inferSortWith bound elseTerm
          if thenSort == sort && elseSort == sort then some sort else none

  /-- 在给定本地绑定上下文下检查核心公式是否合法。 -/
  def Formula.checkWith (bound : List CoreSort) : Formula → Bool
    | Formula.trueE => true
    | Formula.falseE => true
    | Formula.atom predicate args =>
        if !predicate.arityOk || args.length != predicate.arity then
          false
        else
          match Term.inferSortListWith bound args with
          | some argSorts => TypeCheck.inputSortsOk predicate.inputSorts argSorts
          | none => false
    | Formula.equal sort left right =>
        match Term.inferSortWith bound left, Term.inferSortWith bound right with
        | some leftSort, some rightSort => leftSort == sort && rightSort == sort
        | _, _ => false
    | Formula.boolTerm term =>
        match Term.inferSortWith bound term with
        | some sort => sort == CoreSort.bool
        | none => false
    | Formula.neg body => Formula.checkWith bound body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Formula.checkWith bound left && Formula.checkWith bound right
    | Formula.forallE sort body
    | Formula.existsE sort body =>
        Formula.checkWith (sort :: bound) body

  /-- 在给定本地绑定上下文下推断项列表的 sort。 -/
  def Term.inferSortListWith (bound : List CoreSort) :
      List Term → Option (List CoreSort)
    | [] => some []
    | term :: rest => do
        let sort ← Term.inferSortWith bound term
        let sorts ← Term.inferSortListWith bound rest
        some (sort :: sorts)
end

mutual
  /-- 只检查局部无名索引是否被绑定且 sort 标注匹配，不强制项整体 sort 正确。 -/
  def Term.wellScopedWith (bound : List CoreSort) : Term → Bool
    | Term.bvar sort index =>
        match TypeCheck.lookupBound? bound index with
        | some expected => expected == sort
        | none => false
    | Term.fvar .. => true
    | Term.app symbol args => symbol.arityOk && args.length == symbol.arity &&
        Term.wellScopedListWith bound args
    | Term.apply fn arg => Term.wellScopedWith bound fn && Term.wellScopedWith bound arg
    | Term.bool _ => true
    | Term.notE body => Term.wellScopedWith bound body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        Term.wellScopedWith bound left && Term.wellScopedWith bound right
    | Term.quote formula => Formula.wellScopedWith bound formula
    | Term.lam domain _ body => Term.wellScopedWith (domain :: bound) body
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.wellScopedWith bound condition &&
          Term.wellScopedWith bound thenTerm &&
            Term.wellScopedWith bound elseTerm

  /-- 检查公式中的局部无名索引是否被绑定且 sort 标注匹配。 -/
  def Formula.wellScopedWith (bound : List CoreSort) : Formula → Bool
    | Formula.trueE => true
    | Formula.falseE => true
    | Formula.atom predicate args =>
        predicate.arityOk && args.length == predicate.arity && Term.wellScopedListWith bound args
    | Formula.equal _ left right =>
        Term.wellScopedWith bound left && Term.wellScopedWith bound right
    | Formula.boolTerm term => Term.wellScopedWith bound term
    | Formula.neg body => Formula.wellScopedWith bound body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Formula.wellScopedWith bound left && Formula.wellScopedWith bound right
    | Formula.forallE sort body
    | Formula.existsE sort body =>
        Formula.wellScopedWith (sort :: bound) body

  /-- 检查项列表中的局部无名索引是否被绑定且 sort 标注匹配。 -/
  def Term.wellScopedListWith (bound : List CoreSort) : List Term → Bool
    | [] => true
    | term :: rest => Term.wellScopedWith bound term && Term.wellScopedListWith bound rest
end

namespace Term

/-- 在空本地上下文下推断核心项 sort。 -/
def inferSort? (term : Term) : Option CoreSort :=
  Term.inferSortWith [] term

/-- 在空本地上下文下检查项是否 locally nameless well-scoped。 -/
def wellScoped? (term : Term) : Bool :=
  Term.wellScopedWith [] term

end Term

namespace Formula

/-- 在空本地上下文下检查核心公式是否 sort 正确且 locally nameless well-scoped。 -/
def check? (formula : Formula) : Bool :=
  Formula.checkWith [] formula

/-- 在空本地上下文下检查公式是否 locally nameless well-scoped。 -/
def wellScoped? (formula : Formula) : Bool :=
  Formula.wellScopedWith [] formula

end Formula

namespace Formula

/-- 右结合析取链；空字句解释为假。 -/
def disjunctionList : List Formula → Formula
  | [] => falseE
  | [formula] => formula
  | formula :: rest => disj formula (disjunctionList rest)

/-- 右结合有限合取；空列表解释为真，单元素列表保持原公式。 -/
def conjunctionList : List Formula → Formula
  | [] => trueE
  | [formula] => formula
  | formula :: rest => conj formula (conjunctionList rest)

end Formula

namespace Search

/-- 自动化搜索层使用的函数符号种类。 -/
inductive SymbolKind where
  | parameter
  | skolem
  | definition
  | choice
  | builtin
  | extensionalWitness
  | tuple
  deriving Repr, DecidableEq, Lean.ToExpr

/-- 符号种类的布尔等词直接复用 Lean 等式。 -/
instance instBEqSymbolKind : BEq SymbolKind where
  beq left right := decide (left = right)

namespace SymbolKind

/-- 搜索层符号种类投影到核心函数角色。 -/
def toCoreRole : SymbolKind → FunctionRole
  | parameter => FunctionRole.parameter
  | skolem => FunctionRole.skolem
  | definition => FunctionRole.definition
  | choice => FunctionRole.choice
  | builtin => FunctionRole.builtin
  | extensionalWitness => FunctionRole.extensionalWitness
  | tuple => FunctionRole.builtin

end SymbolKind

/-- 自动化搜索层函数符号。`inputSorts = []` 表示旧无类型搜索层暂未携带 sort 信息。 -/
structure FunctionSymbol where
  id : SymbolId
  arity : Nat
  kind : SymbolKind
  inputSorts : List CoreSort := []
  outputSort : CoreSort := CoreSort.object
  deriving Repr, DecidableEq, Lean.ToExpr

/-- 函数符号的布尔等词直接复用 Lean 等式。 -/
instance instBEqFunctionSymbol : BEq FunctionSymbol where
  beq left right := decide (left = right)

namespace FunctionSymbol

/-- 搜索层函数符号投影到核心函数符号。 -/
def toCore (symbol : FunctionSymbol) : CoreSyntax.FunctionSymbol :=
  {
    id := symbol.id
    arity := symbol.arity
    role := symbol.kind.toCoreRole
    inputSorts := symbol.inputSorts
    outputSort := symbol.outputSort
  }

/-- 搜索层函数符号的 sort 摘要。 -/
def sort (symbol : FunctionSymbol) : CoreSort :=
  CoreSort.arrowFrom symbol.inputSorts symbol.outputSort

/-- 元数与输入 sort 列表一致，或者该符号尚处在旧无类型搜索层。 -/
def arityOk (symbol : FunctionSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity

end FunctionSymbol

/-- 高阶 pattern 合一中可以被绑定的 typed 自由变量 sort。 -/
def isFlexibleSort (sort : CoreSort) : Bool :=
  match sort.arrow? with
  | some _ => true
  | none => false

/-- 叠加演算搜索层项语言。保留旧 `var`，同时原生支持 typed locally nameless λ 项。 -/
inductive Term where
  | var (id : VarId)
  | bvar (sort : CoreSort) (index : Nat)
  | fvar (sort : CoreSort) (id : VarId)
  | app (symbol : FunctionSymbol) (args : List Term)
  | apply (fn arg : Term)
  | lam (domain codomain : CoreSort) (body : Term)
  deriving Repr, Lean.ToExpr

namespace Term

/-- 搜索层项投影到核心项。 -/
partial def toCore : Term → CoreSyntax.Term
  | var id => CoreSyntax.Term.fvar CoreSort.object id
  | bvar sort index => CoreSyntax.Term.bvar sort index
  | fvar sort id => CoreSyntax.Term.fvar sort id
  | app symbol args => CoreSyntax.Term.app symbol.toCore (args.map toCore)
  | apply fn arg => CoreSyntax.Term.apply fn.toCore arg.toCore
  | lam domain codomain body => CoreSyntax.Term.lam domain codomain body.toCore

/-- 内部项的粗略尺寸，用于限制搜索和选择化展开。 -/
partial def size : Term → Nat
  | var _ => 1
  | bvar .. => 1
  | fvar .. => 1
  | app _ args => args.foldl (fun acc term => acc + size term) 1
  | apply fn arg => size fn + size arg + 1
  | lam _ _ body => size body + 1

/-- 内部项深度；变量深度为 0，函数应用深度为参数最大深度加 1。 -/
partial def depth : Term → Nat
  | var _ => 0
  | bvar .. => 0
  | fvar .. => 0
  | app _ args => args.foldl (fun acc term => Nat.max acc (depth term)) 0 + 1
  | apply fn arg => Nat.max fn.depth arg.depth + 1
  | lam _ _ body => body.depth + 1

/-- 搜索层 sort 上下文查找；上下文按 De Bruijn 索引从近到远排列。 -/
def lookupBound? : List CoreSort → Nat → Option CoreSort
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookupBound? rest index

/-- 检查每个函数应用的实参数量是否等于符号元数。 -/
partial def arityOk : Term → Bool
  | var _ => true
  | bvar .. => true
  | fvar .. => true
  | app symbol args =>
      symbol.arityOk && args.length == symbol.arity && args.all (fun term => arityOk term)
  | apply fn arg => fn.arityOk && arg.arityOk
  | lam _ _ body => body.arityOk

/-- 项是否是变量。 -/
def isVar : Term → Bool
  | var _ => true
  | fvar .. => true
  | _ => false

/-- 项中出现的最大变量编号加一；空变量项贡献 `0`。 -/
partial def maxVarSucc : Term → Nat
  | var x => x + 1
  | bvar .. => 0
  | fvar _ x => x + 1
  | app _ args => args.foldl (fun acc term => Nat.max acc (maxVarSucc term)) 0
  | apply fn arg => Nat.max fn.maxVarSucc arg.maxVarSucc
  | lam _ _ body => body.maxVarSucc

/-- 项是否是 Skolem 函数应用。 -/
def isSkolemApp : Term → Bool
  | var _ => false
  | bvar .. => false
  | fvar .. => false
  | app symbol _ => symbol.kind == SymbolKind.skolem
  | apply .. => false
  | lam .. => false

/-- 内部项是否为 ground 项。 -/
partial def isGround : Term → Bool
  | var _ => false
  | bvar .. => true
  | fvar .. => false
  | app _ args => args.all (fun arg => isGround arg)
  | apply fn arg => fn.isGround && arg.isGround
  | lam _ _ body => body.isGround

end Term

mutual
  /-- 在给定本地上下文下推断搜索层项 sort。 -/
  partial def Term.inferSortWith (bound : List CoreSort) : Term → Option CoreSort
    | Term.var _ => some CoreSort.object
    | Term.bvar sort index => do
        let expected ← Term.lookupBound? bound index
        if sort == expected then some sort else none
    | Term.fvar sort _ => some sort
    | Term.app symbol args => do
        if !symbol.arityOk || args.length != symbol.arity then
          none
        else
          let argSorts ← Term.inferSortListWith bound args
          if TypeCheck.inputSortsOk symbol.inputSorts argSorts then
            some symbol.outputSort
          else
            none
    | Term.apply fn arg => do
        let fnSort ← Term.inferSortWith bound fn
        let argSort ← Term.inferSortWith bound arg
        match fnSort.arrow? with
        | some (domain, codomain) =>
            if argSort == domain then some codomain else none
        | none => none
    | Term.lam domain codomain body => do
        let bodySort ← Term.inferSortWith (domain :: bound) body
        if bodySort == codomain then some (CoreSort.arrow domain codomain) else none

  /-- 在给定本地上下文下推断搜索层项列表 sort。 -/
  partial def Term.inferSortListWith (bound : List CoreSort) : List Term → Option (List CoreSort)
    | [] => some []
    | term :: rest => do
        let sort ← Term.inferSortWith bound term
        let sorts ← Term.inferSortListWith bound rest
        some (sort :: sorts)
end

namespace Term

/-- 在空上下文下推断搜索层项 sort。 -/
def inferSort? (term : Term) : Option CoreSort :=
  Term.inferSortWith [] term

/-- 搜索层项是否 sort 正确。 -/
def check? (term : Term) : Bool :=
  (term.inferSort?).isSome

end Term

mutual
  /-- 把项中的每个变量编号整体平移。用于二元推理前的 standardize-apart。 -/
  def Term.renameVars (offset : Nat) : Term → Term
    | Term.var x => Term.var (x + offset)
    | Term.bvar sort index => Term.bvar sort index
    | Term.fvar sort x => Term.fvar sort (x + offset)
    | Term.app symbol args => Term.app symbol (Term.renameVarsList offset args)
    | Term.apply fn arg => Term.apply (fn.renameVars offset) (arg.renameVars offset)
    | Term.lam domain codomain body => Term.lam domain codomain (body.renameVars offset)

  /-- 把项列表中的每个变量编号整体平移。 -/
  def Term.renameVarsList (offset : Nat) : List Term → List Term
    | [] => []
    | term :: rest => term.renameVars offset :: Term.renameVarsList offset rest
end

mutual
  /-- 证书 checker 使用的透明内部项相等判断。 -/
  def termEq : Term → Term → Bool
    | Term.var left, Term.var right => decide (left = right)
    | Term.bvar leftSort leftIndex, Term.bvar rightSort rightIndex =>
        decide (leftSort = rightSort) && decide (leftIndex = rightIndex)
    | Term.fvar leftSort leftId, Term.fvar rightSort rightId =>
        decide (leftSort = rightSort) && decide (leftId = rightId)
    | Term.app leftSymbol leftArgs, Term.app rightSymbol rightArgs =>
        decide (leftSymbol = rightSymbol) && termListEq leftArgs rightArgs
    | Term.apply leftFn leftArg, Term.apply rightFn rightArg =>
        termEq leftFn rightFn && termEq leftArg rightArg
    | Term.lam leftDomain leftCodomain leftBody, Term.lam rightDomain rightCodomain rightBody =>
        decide (leftDomain = rightDomain) &&
          decide (leftCodomain = rightCodomain) &&
            termEq leftBody rightBody
    | _, _ => false

  /-- 证书 checker 使用的透明内部项列表相等判断。 -/
  def termListEq : List Term → List Term → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        termEq left right && termListEq leftRest rightRest
    | _, _ => false
end

mutual
  /-- 透明内部项相等判断与 Lean 等式一致。 -/
  @[simp]
  theorem termEq_eq_true {left right : Term} :
      termEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [termEq, termEq_eq_true, termListEq_eq_true, and_assoc]

  /-- 透明内部项列表相等判断与 Lean 等式一致。 -/
  @[simp]
  theorem termListEq_eq_true {left right : List Term} :
      termListEq left right = true ↔ left = right := by
    cases left <;> cases right <;> simp [termListEq, termEq_eq_true, termListEq_eq_true]
end

/-- 内部项的 `BEq` 实例复用透明 checker 等词。 -/
instance instBEqTerm : BEq Term where
  beq := termEq

/-- 内部项的可判定等式，复用 checker 透明相等判断的正确性。 -/
instance termDecidableEq : DecidableEq Term := fun left right =>
  if h : termEq left right = true then
    isTrue (termEq_eq_true.mp h)
  else
    isFalse (fun hEq => h (termEq_eq_true.mpr hEq))

mutual
  /-- 把大于等于 `cutoff` 的局部无名索引整体上移。 -/
  partial def Term.shiftAbove (amount cutoff : Nat) : Term → Term
    | Term.var id => Term.var id
    | Term.bvar sort index =>
        if index < cutoff then Term.bvar sort index else Term.bvar sort (index + amount)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.shiftListAbove amount cutoff args)
    | Term.apply fn arg => Term.apply (fn.shiftAbove amount cutoff) (arg.shiftAbove amount cutoff)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (body.shiftAbove amount (cutoff + 1))

  /-- 对项列表执行 De Bruijn lift。 -/
  partial def Term.shiftListAbove (amount cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => term.shiftAbove amount cutoff :: Term.shiftListAbove amount cutoff rest
end

/-- 对搜索项中所有自由于当前上下文的 De Bruijn 索引执行 lift。 -/
def Term.shift (amount : Nat) (term : Term) : Term :=
  term.shiftAbove amount 0

mutual
  /-- 用 `replacement` 替换深度 `depth` 处的局部无名索引。 -/
  partial def Term.instantiateAt (depth : Nat) (replacement : Term) : Term → Term
    | Term.var id => Term.var id
    | Term.bvar sort index =>
        if index == depth then replacement.shift depth else Term.bvar sort index
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.instantiateListAt depth replacement args)
    | Term.apply fn arg =>
        Term.apply (Term.instantiateAt depth replacement fn)
          (Term.instantiateAt depth replacement arg)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (Term.instantiateAt (depth + 1) replacement body)

  /-- 对项列表执行局部无名替换。 -/
  partial def Term.instantiateListAt (depth : Nat) (replacement : Term) : List Term → List Term
    | [] => []
    | term :: rest =>
        Term.instantiateAt depth replacement term :: Term.instantiateListAt depth replacement rest
end

/-- 替换最外层 lambda 绑定变量。 -/
def Term.instantiate (replacement body : Term) : Term :=
  Term.instantiateAt 0 replacement body

namespace BetaEta

mutual
  /-- 搜索项中是否出现给定 De Bruijn 索引。 -/
  partial def Term.occursBVarAt (depth : Nat) : Term → Bool
    | Term.var .. => false
    | Term.bvar _ index => index == depth
    | Term.fvar .. => false
    | Term.app _ args => Term.occursBVarListAt depth args
    | Term.apply fn arg => Term.occursBVarAt depth fn || Term.occursBVarAt depth arg
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body

  /-- 搜索项列表中是否出现给定 De Bruijn 索引。 -/
  partial def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end

mutual
  /-- 删除一个绑定器时对大于 cutoff 的索引下移。 -/
  partial def Term.lowerAbove (cutoff : Nat) : Term → Term
    | Term.var id => Term.var id
    | Term.bvar sort index =>
        if index < cutoff then
          Term.bvar sort index
        else if index == cutoff then
          Term.bvar sort index
        else
          Term.bvar sort (index - 1)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.lowerListAbove cutoff args)
    | Term.apply fn arg => Term.apply (Term.lowerAbove cutoff fn) (Term.lowerAbove cutoff arg)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.lowerAbove (cutoff + 1) body)

  /-- 对项列表执行 De Bruijn 下移。 -/
  partial def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end

/-- 尝试执行 η 收缩：`λx. f x ↦ f`，要求 `x` 不在 `f` 中自由出现。 -/
def etaContract? (domain : CoreSort) : Term → Option Term
  | Term.apply fn (Term.bvar argSort 0) =>
      if argSort == domain && !Term.occursBVarAt 0 fn then
        some (Term.lowerAbove 0 fn)
      else
        none
  | _ => none

end BetaEta

mutual
  /-- 搜索项 βη-normal form。 -/
  partial def normalizeBetaEtaWith : Nat → Term → Term
    | 0, term => term
    | _fuel + 1, Term.var id => Term.var id
    | _fuel + 1, Term.bvar sort index => Term.bvar sort index
    | _fuel + 1, Term.fvar sort id => Term.fvar sort id
    | fuel + 1, Term.app symbol args =>
        Term.app symbol (normalizeBetaEtaListWith fuel args)
    | fuel + 1, Term.apply fn arg =>
        let fn' := normalizeBetaEtaWith fuel fn
        let arg' := normalizeBetaEtaWith fuel arg
        match fn' with
        | Term.lam _ _ body => normalizeBetaEtaWith fuel (Term.instantiate arg' body)
        | _ => Term.apply fn' arg'
    | fuel + 1, Term.lam domain codomain body =>
        let body' := normalizeBetaEtaWith fuel body
        match BetaEta.etaContract? domain body' with
        | some contracted => normalizeBetaEtaWith fuel contracted
        | none => Term.lam domain codomain body'

  /-- 搜索项列表 βη-normal form。 -/
  partial def normalizeBetaEtaListWith : Nat → List Term → List Term
    | 0, terms => terms
    | _fuel + 1, [] => []
    | fuel + 1, term :: rest =>
        normalizeBetaEtaWith fuel term :: normalizeBetaEtaListWith fuel rest
end

/-- 搜索项 βη-normal form，fuel 由项大小给出。 -/
def normalizeBetaEta (term : Term) : Term :=
  normalizeBetaEtaWith (term.size * 4 + 16) term

/-- βη-normalized 搜索项比较。 -/
def termEqBetaEta (left right : Term) : Bool :=
  termEq (normalizeBetaEta left) (normalizeBetaEta right)

/-- 一次 Skolem 引入记录。 -/
structure Intro where
  symbol : FunctionSymbol
  universalArgs : List Term
  term : Term
  contextDepth : Nat
  deriving Repr, BEq, Lean.ToExpr

namespace Intro

/-- 单条 Skolem 引入记录的可计算检查。 -/
def check (intro : Intro) : Bool :=
  intro.symbol.kind == SymbolKind.skolem &&
    intro.symbol.arity == intro.universalArgs.length &&
    intro.contextDepth == intro.universalArgs.length &&
    termEq intro.term (Term.app intro.symbol intro.universalArgs) &&
    intro.term.arityOk &&
    intro.universalArgs.all Term.isVar

/-- 检查一组 Skolem 引入记录。 -/
def traceCheck (trace : Array Intro) : Bool :=
  trace.all check

end Intro

/-- 对象层特化回放中的一个实例化步骤。 -/
structure SpecializationStep where
  binder : VarId
  term : Term
  proxy : VarId
  deriving Repr, BEq, Lean.ToExpr

namespace SpecializationStep

/-- 该特化是否是对象语言可直接表达的变量特化。 -/
def directVariableOk (step : SpecializationStep) : Bool :=
  step.term == Term.var step.proxy

/-- 特化实例的内部项是否满足函数元数检查。 -/
def check (step : SpecializationStep) : Bool :=
  step.term.arityOk

end SpecializationStep

/-- 一条替换链对应的特化回放计划。 -/
abbrev SpecializationTrace := Array SpecializationStep

namespace SpecializationTrace

/-- 检查特化回放计划中的内部项。 -/
def check (trace : SpecializationTrace) : Bool :=
  trace.all SpecializationStep.check

end SpecializationTrace

/-- 自动化搜索层的一阶谓词种类。 -/
inductive PredicateKind where
  | equal
  | member
  | boolHolds
  | definition (id arity : Nat)
  | predicate (symbol : CoreSyntax.PredicateSymbol)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace PredicateKind

/-- 搜索层谓词种类投影到核心谓词符号。 -/
def toCoreSymbol : PredicateKind → CoreSyntax.PredicateSymbol
  | equal =>
      { id := 0, arity := 2, role := PredicateRole.equalityProxy }
  | member =>
      { id := 1, arity := 2, role := PredicateRole.membership }
  | boolHolds =>
      { id := 2, arity := 1, role := PredicateRole.builtin,
        inputSorts := [CoreSort.bool] }
  | definition id arity =>
      { id := id, arity := arity, role := PredicateRole.definition }
  | predicate symbol => symbol

end PredicateKind

/-- 叠加演算搜索层文字。`positive = false` 表示否定文字。 -/
structure Literal where
  positive : Bool
  predicate : PredicateKind
  left : Term
  right : Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace Literal

/-- 搜索层 literal 的原子部分投影到核心公式。 -/
def toCoreAtom (literal : Literal) : CoreSyntax.Formula :=
  match literal.predicate with
  | PredicateKind.equal =>
      CoreSyntax.Formula.equal CoreSort.object literal.left.toCore literal.right.toCore
  | PredicateKind.member =>
      CoreSyntax.Formula.atom literal.predicate.toCoreSymbol [literal.left.toCore, literal.right.toCore]
  | PredicateKind.boolHolds =>
      CoreSyntax.Formula.boolTerm literal.left.toCore
  | PredicateKind.definition _ _ =>
      CoreSyntax.Formula.atom literal.predicate.toCoreSymbol [literal.left.toCore]
  | PredicateKind.predicate symbol =>
      match literal.left with
      | Term.app tuple args =>
          if tuple.kind = SymbolKind.tuple then
            CoreSyntax.Formula.atom symbol (args.map Term.toCore)
          else
            CoreSyntax.Formula.atom symbol [literal.left.toCore]
      | _ =>
          CoreSyntax.Formula.atom symbol [literal.left.toCore]

/-- 搜索层 literal 投影到带极性的核心公式。 -/
def toCoreFormula (literal : Literal) : CoreSyntax.Formula :=
  if literal.positive then literal.toCoreAtom else CoreSyntax.Formula.neg literal.toCoreAtom

/-- 文字中出现的最大变量编号加一。 -/
def maxVarSucc (literal : Literal) : Nat :=
  Nat.max literal.left.maxVarSucc literal.right.maxVarSucc

/-- 文字中出现的最大项深度。 -/
def maxDepth (literal : Literal) : Nat :=
  Nat.max literal.left.depth literal.right.depth

/-- 内部文字是否为 ground 文字。 -/
def isGround (literal : Literal) : Bool :=
  literal.left.isGround && literal.right.isGround

/-- 把文字中的每个变量编号整体平移。 -/
def renameVars (offset : Nat) (literal : Literal) : Literal :=
  {
    literal with
    left := literal.left.renameVars offset
    right := literal.right.renameVars offset
  }

end Literal

/-- 叠加演算搜索层字句。 -/
abbrev Clause := Array Literal

/-- 证书 checker 使用的透明内部文字相等判断。 -/
def literalEq (left right : Literal) : Bool :=
  decide (left.positive = right.positive) &&
    decide (left.predicate = right.predicate) &&
    termEq left.left right.left &&
    termEq left.right right.right

/-- 透明内部文字相等判断与 Lean 等式一致。 -/
@[simp]
theorem literalEq_eq_true {left right : Literal} :
    literalEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [literalEq]
  constructor
  · intro h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-- 内部文字的可判定等式，复用 checker 透明相等判断的正确性。 -/
instance literalDecidableEq : DecidableEq Literal := fun left right =>
  if h : literalEq left right = true then
    isTrue (literalEq_eq_true.mp h)
  else
    isFalse (fun hEq => h (literalEq_eq_true.mpr hEq))

/-- 证书 checker 使用的透明内部文字列表相等判断。 -/
def literalListEq : List Literal → List Literal → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      literalEq left right && literalListEq leftRest rightRest
  | _, _ => false

/-- 透明内部文字列表相等判断与 Lean 等式一致。 -/
@[simp]
theorem literalListEq_eq_true {left right : List Literal} :
    literalListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [literalListEq]
  | cons head tail ih =>
      cases right <;> simp [literalListEq, ih]

/-- 证书 checker 使用的透明内部字句相等判断。 -/
def clauseEq (left right : Clause) : Bool :=
  literalListEq left.toList right.toList

/-- 透明内部字句相等判断与 Lean 等式一致。 -/
@[simp]
theorem clauseEq_eq_true {left right : Clause} :
    clauseEq left right = true ↔ left = right := by
  unfold clauseEq
  constructor
  · intro h
    exact Array.toList_inj.mp (literalListEq_eq_true.mp h)
  · intro h
    subst h
    simp

/-- 证书 checker 使用的透明内部字句列表相等判断。 -/
def clauseListEq : List Clause → List Clause → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      clauseEq left right && clauseListEq leftRest rightRest
  | _, _ => false

/-- 透明内部字句列表相等判断与 Lean 等式一致。 -/
@[simp]
theorem clauseListEq_eq_true {left right : List Clause} :
    clauseListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [clauseListEq]
  | cons head tail ih =>
      cases right <;> simp [clauseListEq, ih]

/-- 证书 checker 使用的透明内部字句数组相等判断。 -/
def clauseArrayEq (left right : Array Clause) : Bool :=
  clauseListEq left.toList right.toList

/-- 透明内部字句数组相等判断与 Lean 等式一致。 -/
@[simp]
theorem clauseArrayEq_eq_true {left right : Array Clause} :
    clauseArrayEq left right = true ↔ left = right := by
  unfold clauseArrayEq
  constructor
  · intro h
    exact Array.toList_inj.mp (clauseListEq_eq_true.mp h)
  · intro h
    subst h
    simp

namespace Clause

/-- 搜索层字句投影到核心析取公式。 -/
def toCoreFormula (clause : Clause) : CoreSyntax.Formula :=
  CoreSyntax.Formula.disjunctionList (clause.toList.map Literal.toCoreFormula)

/-- 内部字句是否为 ground 字句。 -/
def isGround (clause : Clause) : Bool :=
  clause.all Literal.isGround

/-- 字句中出现的最大变量编号加一。 -/
def maxVarSucc (clause : Clause) : Nat :=
  Id.run do
    let mut maxVar := 0
    for literal in clause do
      maxVar := Nat.max maxVar literal.maxVarSucc
    return maxVar

/-- 字句中出现的最大项深度。 -/
def maxDepth (clause : Clause) : Nat :=
  Id.run do
    let mut depth := 0
    for literal in clause do
      depth := Nat.max depth literal.maxDepth
    return depth

/-- 把字句中的每个变量编号整体平移。 -/
def renameVars (offset : Nat) (clause : Clause) : Clause :=
  clause.map (fun literal => literal.renameVars offset)

end Clause

/-!
## 搜索层替换、匹配与合一

搜索变量使用 `(sort, id)` 作为唯一身份。旧 `.var id` 只是对象 sort 自由变量的紧凑
表面；`.fvar sort id` 与它进入 substitution、standardize-apart 和索引前共享同一变量键。
-/

/-- 搜索变量的 typed 身份。 -/
structure Variable where
  sort : CoreSort
  id : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace Variable

/-- 旧 `.var` 对应的对象变量键。 -/
def object (id : VarId) : Variable := {
  sort := CoreSort.object
  id := id
}

/-- 变量键的 canonical typed 项表示。 -/
def toTerm (key : Variable) : Term :=
  Term.fvar key.sort key.id

/-- 一个搜索项是否表示当前变量；对象 `.var` 与对象 `.fvar` 在这里等价。 -/
def matchesTerm (key : Variable) : Term → Bool
  | Term.var id => key.sort == CoreSort.object && key.id == id
  | Term.fvar sort id => key.sort == sort && key.id == id
  | _ => false

end Variable

namespace Term

/-- 从搜索项读取变量键；bound variable 与刚性应用没有 substitution 身份。 -/
def variable? : Term → Option Variable
  | Term.var id => some (Variable.object id)
  | Term.fvar sort id => some { sort := sort, id := id }
  | _ => none

mutual
  /-- 项中出现的 typed 搜索变量。保留重复出现，便于审计原始形状。 -/
  def variables : Term → List Variable
    | Term.var id => [Variable.object id]
    | Term.bvar .. => []
    | Term.fvar sort id => [{ sort := sort, id := id }]
    | Term.app _ args => variablesList args
    | Term.apply fn arg => variables fn ++ variables arg
    | Term.lam _ _ body => variables body

  /-- 项列表中出现的 typed 搜索变量。 -/
  def variablesList : List Term → List Variable
    | [] => []
    | term :: rest => variables term ++ variablesList rest
end

/-- typed 变量是否出现在项中。 -/
partial def occursVariable (key : Variable) : Term → Bool
  | Term.var id => key.matchesTerm (Term.var id)
  | Term.bvar .. => false
  | Term.fvar sort id => key.matchesTerm (Term.fvar sort id)
  | Term.app _ args => args.any (occursVariable key)
  | Term.apply fn arg => occursVariable key fn || occursVariable key arg
  | Term.lam _ _ body => occursVariable key body

end Term

/-- 一条自带 sort 的 substitution binding。 -/
structure SubstitutionBinding where
  key : Variable
  replacement : Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

/-- 靠前 binding 优先的有限 typed substitution。 -/
abbrev Substitution := List SubstitutionBinding

namespace Substitution

/-- 空替换。 -/
def empty : Substitution := []

/-- 单条 typed binding。 -/
def singleton (key : Variable) (replacement : Term) : Substitution :=
  [{ key := key, replacement := replacement }]

/-- 查找 typed 变量绑定。 -/
def lookup (subst : Substitution) (key : Variable) : Option Term :=
  match subst with
  | [] => none
  | binding :: rest =>
      if binding.key = key then
        some binding.replacement
      else
        lookup rest key

end Substitution

/-
父字句 soundness 需要替换复合，所以这里把替换作用定义成 Lean 可以展开的互递归定义，
而不是 `partial` fuel 函数。

变量命中 binding 时直接返回右侧项；`bind?` 会同步规范化已有 binding，保持搜索得到的
MGU 处于可复合形态。
-/

mutual
  /-- 将 typed substitution 作用到项上。 -/
  def Substitution.applyTerm (subst : Substitution) : Term → Term
    | Term.var id =>
        match Substitution.lookup subst (Variable.object id) with
        | some term => term
        | none => Term.var id
    | Term.bvar sort index => Term.bvar sort index
    | Term.fvar sort id =>
        match Substitution.lookup subst { sort := sort, id := id } with
        | some term => term
        | none => Term.fvar sort id
    | Term.app symbol args =>
        Term.app symbol (Substitution.applyTerms subst args)
    | Term.apply fn arg =>
        Term.apply (Substitution.applyTerm subst fn) (Substitution.applyTerm subst arg)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (Substitution.applyTerm subst body)

  /-- 将 typed substitution 作用到项列表上。 -/
  def Substitution.applyTerms (subst : Substitution) : List Term → List Term
    | [] => []
    | term :: rest => Substitution.applyTerm subst term :: Substitution.applyTerms subst rest
end

namespace Substitution

/-- 将替换作用到文字上。 -/
def applyLiteral (subst : Substitution) (literal : Literal) : Literal :=
  {
    literal with
    left := applyTerm subst literal.left
    right := applyTerm subst literal.right
  }

/-- 将替换作用到字句上。 -/
def applyClause (subst : Substitution) (clause : Clause) : Clause :=
  clause.map (fun literal => applyLiteral subst literal)

/-- 替换复合：先执行 `first`，再执行 `second`。 -/
def compose (first second : Substitution) : Substitution :=
  first.map (fun binding =>
    { binding with replacement := applyTerm second binding.replacement }) ++ second

/-- 用一个新 binding 规范化已有 binding 的右侧项。 -/
def rewriteBinding (key : Variable) (term : Term)
    (binding : SubstitutionBinding) : SubstitutionBinding :=
  {
    binding with
    replacement := applyTerm (singleton key term) binding.replacement
  }

/-- 绑定 typed 变量；同时检查 sort、occurs condition，并规范化已有 binding。 -/
def bind? (key : Variable) (term : Term)
    (subst : Substitution) : Option Substitution :=
  let term := applyTerm subst term
  if key.matchesTerm term then
    some subst
  else if term.inferSort? != some key.sort then
    none
  else if Term.occursVariable key term then
    none
  else
    some ({
      key := key
      replacement := term
    } :: subst.map (rewriteBinding key term))

theorem lookup_append (subst rest : Substitution) (key : Variable) :
    lookup (subst ++ rest) key =
      match lookup subst key with
      | some term => some term
      | none => lookup rest key := by
  induction subst with
  | nil =>
      rfl
  | cons binding tail ih =>
      by_cases hKey : binding.key = key
      · simp [lookup, hKey]
      · simp [lookup, hKey, ih]

@[simp]
theorem lookup_append_left {subst rest : Substitution}
    {key : Variable} {term : Term}
    (hLookup : lookup subst key = some term) :
    lookup (subst ++ rest) key = some term := by
  rw [lookup_append, hLookup]

@[simp]
theorem lookup_append_right {subst rest : Substitution}
    {key : Variable} (hLookup : lookup subst key = none) :
    lookup (subst ++ rest) key = lookup rest key := by
  rw [lookup_append, hLookup]

theorem lookup_map_replacements (subst : Substitution)
    (second : Substitution) (key : Variable) :
    lookup
        (subst.map fun binding =>
          { binding with replacement := applyTerm second binding.replacement })
        key =
      (lookup subst key).map (applyTerm second) := by
  induction subst with
  | nil =>
      rfl
  | cons binding tail ih =>
      by_cases hKey : binding.key = key
      · simp [lookup, hKey]
      · simp [lookup, hKey, ih]

@[simp]
theorem lookup_compose (first second : Substitution) (key : Variable) :
    lookup (compose first second) key =
      match lookup first key with
      | some term => some (applyTerm second term)
      | none => lookup second key := by
  rw [compose, lookup_append, lookup_map_replacements]
  cases lookup first key <;> rfl

end Substitution

mutual
  @[simp]
  theorem Substitution.applyTerm_compose (first second : Substitution) :
      ∀ term : Term,
        Substitution.applyTerm second (Substitution.applyTerm first term) =
          Substitution.applyTerm (Substitution.compose first second) term
    | Term.var id => by
        cases hFirst : Substitution.lookup first (Variable.object id) with
        | none =>
            cases hSecond : Substitution.lookup second (Variable.object id) <;>
              simp [Substitution.applyTerm, hFirst, hSecond]
        | some term =>
            simp [Substitution.applyTerm, hFirst]
    | Term.bvar sort index => by
        simp [Substitution.applyTerm]
    | Term.fvar sort id => by
        let key : Variable := { sort := sort, id := id }
        cases hFirst : Substitution.lookup first key with
        | none =>
            cases hSecond : Substitution.lookup second key <;>
              simp [Substitution.applyTerm, key, hFirst, hSecond]
        | some term =>
            simp [Substitution.applyTerm, key, hFirst]
    | Term.app symbol args => by
        simp [Substitution.applyTerm, Substitution.applyTermList_compose first second args]
    | Term.apply fn arg => by
        simp [Substitution.applyTerm, Substitution.applyTerm_compose first second fn,
          Substitution.applyTerm_compose first second arg]
    | Term.lam domain codomain body => by
        simp [Substitution.applyTerm, Substitution.applyTerm_compose first second body]

  @[simp]
  theorem Substitution.applyTermList_compose (first second : Substitution) :
      ∀ terms : List Term,
        Substitution.applyTerms second (Substitution.applyTerms first terms) =
          Substitution.applyTerms (Substitution.compose first second) terms
    | [] => by
        simp [Substitution.applyTerms]
    | term :: rest => by
        simp [Substitution.applyTerms, Substitution.applyTerm_compose,
          Substitution.applyTermList_compose]
end

namespace Substitution

@[simp]
theorem applyLiteral_compose (first second : Substitution) (literal : Literal) :
    applyLiteral second (applyLiteral first literal) =
      applyLiteral (compose first second) literal := by
  cases literal
  simp [applyLiteral, applyTerm_compose]

@[simp]
theorem applyClause_compose (first second : Substitution) (clause : Clause) :
    applyClause second (applyClause first clause) =
      applyClause (compose first second) clause := by
  simp [applyClause, Array.map_map]

end Substitution

/-- 合并两个等长参数表为合一约束。 -/
def zipTermPairs? : List Term → List Term → Option (List (Term × Term))
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match zipTermPairs? leftRest rightRest with
      | some rest => some ((left, right) :: rest)
      | none => none
  | _, _ => none

/-- 一阶项 Robinson 合一主循环，返回一个最一般合一者的计算表示。 -/
partial def unifyLoop : Substitution → List (Term × Term) → Option Substitution
  | subst, [] => some subst
  | subst, (left, right) :: rest =>
      let left := Substitution.applyTerm subst left
      let right := Substitution.applyTerm subst right
      if left == right then
        unifyLoop subst rest
      else
        match left, right with
        | Term.var x, term =>
            match Substitution.bind? (Variable.object x) term subst with
            | some subst => unifyLoop subst rest
            | none => none
        | term, Term.var x =>
            match Substitution.bind? (Variable.object x) term subst with
            | some subst => unifyLoop subst rest
            | none => none
        | Term.fvar sort x, term =>
            match Substitution.bind? { sort := sort, id := x } term subst with
            | some subst => unifyLoop subst rest
            | none => none
        | term, Term.fvar sort x =>
            match Substitution.bind? { sort := sort, id := x } term subst with
            | some subst => unifyLoop subst rest
            | none => none
        | Term.app leftSymbol leftArgs, Term.app rightSymbol rightArgs =>
            if leftSymbol == rightSymbol then
              match zipTermPairs? leftArgs rightArgs with
              | some pairs => unifyLoop subst (pairs ++ rest)
              | none => none
            else
              none
        | Term.apply leftFn leftArg, Term.apply rightFn rightArg =>
            unifyLoop subst ((leftFn, rightFn) :: (leftArg, rightArg) :: rest)
        | Term.lam leftDomain leftCodomain leftBody, Term.lam rightDomain rightCodomain rightBody =>
            if leftDomain == rightDomain && leftCodomain == rightCodomain then
              unifyLoop subst ((leftBody, rightBody) :: rest)
            else
              none
        | Term.bvar leftSort leftIndex, Term.bvar rightSort rightIndex =>
            if leftSort == rightSort && leftIndex == rightIndex then
              unifyLoop subst rest
            else
              none
        | _, _ => none

/-- 两个项的一阶/刚性结构合一替换。 -/
def unifyFO? (left right : Term) : Option Substitution :=
  unifyLoop [] [(left, right)]

/-- Miller pattern fragment 的替换表示；当前复用搜索层有限替换。 -/
abbrev PatternSubstitution := Substitution

namespace PatternSubstitution

/-- 空 pattern 替换。 -/
def empty : PatternSubstitution := Substitution.empty

/-- Pattern substitution 与普通合一共享 typed substitution 作用。 -/
abbrev applyTerm := Substitution.applyTerm

/-- Pattern binding 与普通合一共享 sort/occurs 检查。 -/
abbrev bind? := Substitution.bind?

end PatternSubstitution

namespace HOUnification

/-- 高阶合一调度结果。 -/
inductive Result where
  | solved (subst : PatternSubstitution)
  | residual (constraints : List (Term × Term))
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace Result

/-- 把完全解决的结果投影成旧搜索层替换。 -/
def toOption : Result → Option Substitution
  | solved subst => some subst
  | residual _ => none

/-- 结果是否是 residual。 -/
def hasResidual : Result → Bool
  | solved _ => false
  | residual _ => true

end Result

/-- pattern 实参必须是互异变量形状。 -/
inductive PatternArg where
  | mvar (id : VarId)
  | free (sort : CoreSort) (id : VarId)
  | bound (sort : CoreSort) (index : Nat)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace PatternArg

/-- pattern 实参的 sort。旧 `var` 只代表对象 sort。 -/
def sort : PatternArg → CoreSort
  | mvar _ => CoreSort.object
  | free sort _ => sort
  | bound sort _ => sort

/-- pattern 实参的透明项编码。 -/
def toTerm : PatternArg → Term
  | mvar id => Term.var id
  | free sort id => Term.fvar sort id
  | bound sort index => Term.bvar sort index

/-- 在额外局部绑定器深度下的 pattern 实参编码。 -/
def toTermAtDepth (depth : Nat) : PatternArg → Term
  | mvar id => Term.var id
  | free sort id => Term.fvar sort id
  | bound sort index => Term.bvar sort (index + depth)

/-- pattern 实参是否与另一个实参相同。 -/
def eq (left right : PatternArg) : Bool :=
  left == right

/-- 实参是否已经出现在列表里。 -/
def mem (arg : PatternArg) : List PatternArg → Bool
  | [] => false
  | head :: rest => eq arg head || mem arg rest

end PatternArg

/-- 把项拆成 head 与 spine。 -/
partial def collectSpine : Term → Term × List Term
  | Term.apply fn arg =>
      let (head, args) := collectSpine fn
      (head, args ++ [arg])
  | term => (term, [])

/-- 尝试识别一个 pattern 实参。 -/
def patternArg? : Term → Option PatternArg
  | Term.var id => some (PatternArg.mvar id)
  | Term.fvar sort id => some (PatternArg.free sort id)
  | Term.bvar sort index => some (PatternArg.bound sort index)
  | _ => none

/-- 识别互异 pattern 实参列表。 -/
def distinctPatternArgs? : List Term → Option (List PatternArg) :=
  let rec go (seen : List PatternArg) : List Term → Option (List PatternArg)
    | [] => some seen.reverse
    | term :: rest => do
        let arg ← patternArg? term
        if PatternArg.mem arg seen then
          none
        else
          go (arg :: seen) rest
  go []

/-- pattern 抽象体不能包含将被绑定的 typed 高阶变量。 -/
def abstractionBodyOk (key : Variable) (body : Term) : Bool :=
  !Term.occursVariable key body

/-- 在当前深度下寻找目标项是否正好是某个 pattern 实参。 -/
def patternArgMatch? (depth : Nat) (target : Term) (args : List PatternArg) :
    Option (Nat × PatternArg) :=
  let rec go (index : Nat) : List PatternArg → Option (Nat × PatternArg)
    | [] => none
    | arg :: rest =>
        if termEq (arg.toTermAtDepth depth) target then
          some (index, arg)
        else
          go (index + 1) rest
  go 0 args

/-- 新 lambda 实参在当前深度下对应的 De Bruijn 索引。 -/
def abstractionIndex (args : List PatternArg) (position depth : Nat) : Nat :=
  depth + (args.length - position - 1)

mutual
  /-- 把目标项里出现的 pattern 实参抽象成即将引入的 lambda 绑定变量。 -/
  partial def abstractPatternArgsWith (args : List PatternArg) (depth : Nat) : Term → Term
    | term =>
        match patternArgMatch? depth term args with
        | some (position, arg) => Term.bvar arg.sort (abstractionIndex args position depth)
        | none =>
            match term with
            | Term.var id => Term.var id
            | Term.bvar sort index => Term.bvar sort index
            | Term.fvar sort id => Term.fvar sort id
            | Term.app symbol terms => Term.app symbol (abstractPatternArgsListWith args depth terms)
            | Term.apply fn arg =>
                Term.apply (abstractPatternArgsWith args depth fn)
                  (abstractPatternArgsWith args depth arg)
            | Term.lam domain codomain body =>
                Term.lam domain codomain (abstractPatternArgsWith args (depth + 1) body)

  /-- 对项列表执行 pattern 实参抽象。 -/
  partial def abstractPatternArgsListWith (args : List PatternArg) (depth : Nat) :
      List Term → List Term
    | [] => []
    | term :: rest =>
        abstractPatternArgsWith args depth term :: abstractPatternArgsListWith args depth rest
end

/-- 把目标项里 pattern 实参出现处抽象成 lambda 绑定变量。 -/
def abstractPatternArgs (args : List PatternArg) (target : Term) : Term :=
  abstractPatternArgsWith args 0 target

/-- 包装多元 lambda，同时尽量重建每层 lambda 的 codomain。 -/
def closePatternBinding (args : List PatternArg) (target : Term) : Term :=
  let body := abstractPatternArgs args target
  let bodySort :=
    (Term.inferSortWith (args.reverse.map PatternArg.sort) body).getD CoreSort.object
  let (_, closed) :=
    args.foldr
      (fun arg acc =>
        let codomain := acc.1
        let term := acc.2
        let closed := Term.lam arg.sort codomain term
        (CoreSort.arrow arg.sort codomain, closed))
      (bodySort, body)
  closed

/-- 尝试识别 `F a₁ ... aₙ = target` 的 Miller pattern 绑定。 -/
def patternBind? (head : Term) (args : List Term) (target : Term)
    (subst : PatternSubstitution) : Option PatternSubstitution :=
  match head with
  | Term.var varId =>
      match distinctPatternArgs? args with
      | some patternArgs =>
          let key := Variable.object varId
          if abstractionBodyOk key target then
            PatternSubstitution.bind? key (closePatternBinding patternArgs target) subst
          else
            none
      | none => none
  | Term.fvar sort varId =>
      if isFlexibleSort sort then
        match distinctPatternArgs? args with
        | some patternArgs =>
            let key : Variable := { sort := sort, id := varId }
            if abstractionBodyOk key target then
              PatternSubstitution.bind? key (closePatternBinding patternArgs target) subst
            else
              none
        | none => none
      else
        none
  | _ => none

/-- 是否是 pattern variable application。 -/
def isPatternHead : Term → Bool
  | Term.var _ => true
  | Term.fvar sort _ => isFlexibleSort sort
  | _ => false

/-- Pattern HO 合一主循环；不能安全处理的形状返回 residual。 -/
partial def patternLoop : PatternSubstitution → List (Term × Term) → Result
  | subst, [] => Result.solved subst
  | subst, (left, right) :: rest =>
      let left := normalizeBetaEta (PatternSubstitution.applyTerm subst left)
      let right := normalizeBetaEta (PatternSubstitution.applyTerm subst right)
      if termEq left right then
        patternLoop subst rest
      else
        match left, right with
        | Term.var x, term =>
            match PatternSubstitution.bind? (Variable.object x) term subst with
            | some subst => patternLoop subst rest
            | none => Result.residual ((left, right) :: rest)
        | term, Term.var x =>
            match PatternSubstitution.bind? (Variable.object x) term subst with
            | some subst => patternLoop subst rest
            | none => Result.residual ((left, right) :: rest)
        | Term.apply .., _ =>
            let (head, args) := collectSpine left
            if isPatternHead head then
              match patternBind? head args right subst with
              | some subst => patternLoop subst rest
              | none => Result.residual ((left, right) :: rest)
            else
              match right with
              | Term.apply rightFn rightArg =>
                  match left with
                  | Term.apply leftFn leftArg =>
                      patternLoop subst ((leftFn, rightFn) :: (leftArg, rightArg) :: rest)
                  | _ => Result.residual ((left, right) :: rest)
              | _ => Result.residual ((left, right) :: rest)
        | _, Term.apply .. =>
            let (head, args) := collectSpine right
            if isPatternHead head then
              match patternBind? head args left subst with
              | some subst => patternLoop subst rest
              | none => Result.residual ((left, right) :: rest)
            else
              Result.residual ((left, right) :: rest)
        | Term.fvar sort x, term =>
            match PatternSubstitution.bind? { sort := sort, id := x } term subst with
            | some subst => patternLoop subst rest
            | none => Result.residual ((left, right) :: rest)
        | term, Term.fvar sort x =>
            match PatternSubstitution.bind? { sort := sort, id := x } term subst with
            | some subst => patternLoop subst rest
            | none => Result.residual ((left, right) :: rest)
        | Term.app leftSymbol leftArgs, Term.app rightSymbol rightArgs =>
            if leftSymbol == rightSymbol then
              match zipTermPairs? leftArgs rightArgs with
              | some pairs => patternLoop subst (pairs ++ rest)
              | none => Result.residual ((left, right) :: rest)
            else
              Result.residual ((left, right) :: rest)
        | Term.lam leftDomain leftCodomain leftBody, Term.lam rightDomain rightCodomain rightBody =>
            if leftDomain == rightDomain && leftCodomain == rightCodomain then
              patternLoop subst ((leftBody, rightBody) :: rest)
            else
              Result.residual ((left, right) :: rest)
        | Term.bvar leftSort leftIndex, Term.bvar rightSort rightIndex =>
            if leftSort == rightSort && leftIndex == rightIndex then
              patternLoop subst rest
            else
              Result.residual ((left, right) :: rest)
        | _, _ => Result.residual ((left, right) :: rest)

/-- 执行 Miller pattern fragment 合一。 -/
def unifyPattern (left right : Term) : Result :=
  patternLoop PatternSubstitution.empty [(left, right)]

/-- 分层合一：先 FO，再 pattern HO，最后 residual。 -/
def unify (left right : Term) : Result :=
  match unifyLoop [] [(left, right)] with
  | some subst => Result.solved subst
  | none => unifyPattern left right

end HOUnification

/-- 分层合一调度的旧接口：只有完全解决时返回替换。 -/
def unify? (left right : Term) : Option Substitution :=
  (HOUnification.unify left right).toOption

/-- 分层合一多个约束；先走一阶，再走 Miller pattern fragment。 -/
def unifyConstraints? (constraints : List (Term × Term)) : Option Substitution :=
  match unifyLoop [] constraints with
  | some subst => some subst
  | none => (HOUnification.patternLoop PatternSubstitution.empty constraints).toOption

/-- 一阶项匹配：只允许左侧模式中的变量被绑定。 -/
partial def matchLoop : Substitution → List (Term × Term) → Option Substitution
  | subst, [] => some subst
  | subst, (pattern, target) :: rest =>
      let pattern := Substitution.applyTerm subst pattern
      if pattern == target then
        matchLoop subst rest
      else
        match pattern, target with
        | Term.var x, term =>
            match Substitution.bind? (Variable.object x) term subst with
            | some subst => matchLoop subst rest
            | none => none
        | Term.fvar sort x, term =>
            match Substitution.bind? { sort := sort, id := x } term subst with
            | some subst => matchLoop subst rest
            | none => none
        | Term.app patternSymbol patternArgs, Term.app targetSymbol targetArgs =>
            if patternSymbol == targetSymbol then
              match zipTermPairs? patternArgs targetArgs with
              | some pairs => matchLoop subst (pairs ++ rest)
              | none => none
            else
              none
        | Term.apply patternFn patternArg, Term.apply targetFn targetArg =>
            matchLoop subst ((patternFn, targetFn) :: (patternArg, targetArg) :: rest)
        | Term.lam patternDomain patternCodomain patternBody,
          Term.lam targetDomain targetCodomain targetBody =>
            if patternDomain == targetDomain && patternCodomain == targetCodomain then
              matchLoop subst ((patternBody, targetBody) :: rest)
            else
              none
        | Term.bvar patternSort patternIndex, Term.bvar targetSort targetIndex =>
            if patternSort == targetSort && patternIndex == targetIndex then
              matchLoop subst rest
            else
              none
        | _, _ => none

/-- 尝试让 `pattern` 匹配 `target`。 -/
def matchTerm? (pattern target : Term) : Option Substitution :=
  matchLoop [] [(pattern, target)]

/-- 从给定替换继续合一两对项。 -/
def unifyTwoPairs? (a b c d : Term) : Option Substitution :=
  unifyConstraints? [(a, b), (c, d)]

/-- 合一两个文字的原子部分；等词允许左右交换。 -/
def unifyAtom? (left right : Literal) : Option Substitution :=
  if left.predicate == right.predicate then
    if left.predicate == PredicateKind.equal then
      match unifyTwoPairs? left.left right.left left.right right.right with
      | some subst => some subst
      | none => unifyTwoPairs? left.left right.right left.right right.left
    else
      unifyTwoPairs? left.left right.left left.right right.right
  else
    none

/-- 用 standardize-apart 平移右字句变量，避免二元推理时父字句变量碰撞。 -/
def standardizeApart (left right : Clause) : Clause × Clause :=
  let offset := Clause.maxVarSucc left
  (left, Clause.renameVars offset right)


end Search

end CoreSyntax
end Automation
end YesMetaZFC
