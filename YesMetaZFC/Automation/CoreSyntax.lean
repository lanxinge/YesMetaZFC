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
abbrev VarId := Nat
abbrev SymbolId := Nat
inductive CoreSort where
  | object
  | bool
  | prop
  | named (id : Nat)
  | arrow (domain codomain : CoreSort)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable,
    Lean.ToExpr
namespace CoreSort
def arrowFrom : List CoreSort → CoreSort → CoreSort
  | [], result => result
  | arg :: rest, result => CoreSort.arrow arg (arrowFrom rest result)
def arrow? : CoreSort → Option (CoreSort × CoreSort)
  | CoreSort.arrow domain codomain => some (domain, codomain)
  | _ => none
end CoreSort
inductive FunctionRole where
  | parameter
  | skolem
  | definition
  | choice
  | builtin
  | extensionalWitness
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr
inductive PredicateRole where
  | relation
  | equalityProxy
  | membership
  | definition
  | builtin
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable,
    Lean.ToExpr
structure FunctionSymbol where
  id : SymbolId
  arity : Nat
  role : FunctionRole
  inputSorts : List CoreSort := []
  outputSort : CoreSort := CoreSort.object
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr
namespace FunctionSymbol
def sort (symbol : FunctionSymbol) : CoreSort :=
  CoreSort.arrowFrom symbol.inputSorts symbol.outputSort
def arityOk (symbol : FunctionSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity
end FunctionSymbol
structure PredicateSymbol where
  id : SymbolId
  arity : Nat
  role : PredicateRole
  inputSorts : List CoreSort := []
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable,
    Lean.ToExpr
namespace PredicateSymbol
def arityOk (symbol : PredicateSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity
end PredicateSymbol
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
def lookupBound? : List CoreSort → Nat → Option CoreSort
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookupBound? rest index
def sortListEq (left right : List CoreSort) : Bool :=
  decide (left = right)
def inputSortsOk (declared actual : List CoreSort) : Bool :=
  declared.isEmpty || sortListEq declared actual
end TypeCheck
mutual
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
  def Term.inferSortListWith (bound : List CoreSort) :
      List Term → Option (List CoreSort)
    | [] => some []
    | term :: rest => do
        let sort ← Term.inferSortWith bound term
        let sorts ← Term.inferSortListWith bound rest
        some (sort :: sorts)
end
mutual
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
  def Term.wellScopedListWith (bound : List CoreSort) : List Term → Bool
    | [] => true
    | term :: rest => Term.wellScopedWith bound term && Term.wellScopedListWith bound rest
end
namespace Term
def inferSort? (term : Term) : Option CoreSort :=
  Term.inferSortWith [] term
def wellScoped? (term : Term) : Bool :=
  Term.wellScopedWith [] term
end Term
namespace Formula
def check? (formula : Formula) : Bool :=
  Formula.checkWith [] formula
def wellScoped? (formula : Formula) : Bool :=
  Formula.wellScopedWith [] formula
end Formula
namespace Formula
def disjunctionList : List Formula → Formula
  | [] => falseE
  | [formula] => formula
  | formula :: rest => disj formula (disjunctionList rest)
def conjunctionList : List Formula → Formula
  | [] => trueE
  | [formula] => formula
  | formula :: rest => conj formula (conjunctionList rest)
end Formula
namespace Search
inductive SymbolKind where
  | parameter
  | skolem
  | definition
  | choice
  | builtin
  | extensionalWitness
  | tuple
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr
instance instBEqSymbolKind : BEq SymbolKind where
  beq left right := decide (left = right)
namespace SymbolKind
def toCoreRole : SymbolKind → FunctionRole
  | parameter => FunctionRole.parameter
  | skolem => FunctionRole.skolem
  | definition => FunctionRole.definition
  | choice => FunctionRole.choice
  | builtin => FunctionRole.builtin
  | extensionalWitness => FunctionRole.extensionalWitness
  | tuple => FunctionRole.builtin
end SymbolKind
structure FunctionSymbol where
  id : SymbolId
  arity : Nat
  kind : SymbolKind
  inputSorts : List CoreSort := []
  outputSort : CoreSort := CoreSort.object
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr
instance instBEqFunctionSymbol : BEq FunctionSymbol where
  beq left right := decide (left = right)
namespace FunctionSymbol
def toCore (symbol : FunctionSymbol) : CoreSyntax.FunctionSymbol :=
  {
    id := symbol.id
    arity := symbol.arity
    role := symbol.kind.toCoreRole
    inputSorts := symbol.inputSorts
    outputSort := symbol.outputSort
  }
def sort (symbol : FunctionSymbol) : CoreSort :=
  CoreSort.arrowFrom symbol.inputSorts symbol.outputSort
def arityOk (symbol : FunctionSymbol) : Bool :=
  symbol.inputSorts.isEmpty || symbol.inputSorts.length == symbol.arity
end FunctionSymbol
def isFlexibleSort (sort : CoreSort) : Bool :=
  match sort.arrow? with
  | some _ => true
  | none => false
inductive Term where
  | var (id : VarId)
  | bvar (sort : CoreSort) (index : Nat)
  | fvar (sort : CoreSort) (id : VarId)
  | app (symbol : FunctionSymbol) (args : List Term)
  | apply (fn arg : Term)
  | lam (domain codomain : CoreSort) (body : Term)
  deriving Repr, Hashable, Lean.ToExpr
namespace Term
partial def toCore : Term → CoreSyntax.Term
  | var id => CoreSyntax.Term.fvar CoreSort.object id
  | bvar sort index => CoreSyntax.Term.bvar sort index
  | fvar sort id => CoreSyntax.Term.fvar sort id
  | app symbol args => CoreSyntax.Term.app symbol.toCore (args.map toCore)
  | apply fn arg => CoreSyntax.Term.apply fn.toCore arg.toCore
  | lam domain codomain body => CoreSyntax.Term.lam domain codomain body.toCore
partial def size : Term → Nat
  | var _ => 1
  | bvar .. => 1
  | fvar .. => 1
  | app _ args => args.foldl (fun acc term => acc + size term) 1
  | apply fn arg => size fn + size arg + 1
  | lam _ _ body => size body + 1
partial def depth : Term → Nat
  | var _ => 0
  | bvar .. => 0
  | fvar .. => 0
  | app _ args => args.foldl (fun acc term => Nat.max acc (depth term)) 0 + 1
  | apply fn arg => Nat.max fn.depth arg.depth + 1
  | lam _ _ body => body.depth + 1
def lookupBound? : List CoreSort → Nat → Option CoreSort
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookupBound? rest index
partial def arityOk : Term → Bool
  | var _ => true
  | bvar .. => true
  | fvar .. => true
  | app symbol args =>
      symbol.arityOk && args.length == symbol.arity && args.all (fun term => arityOk term)
  | apply fn arg => fn.arityOk && arg.arityOk
  | lam _ _ body => body.arityOk
def isVar : Term → Bool
  | var _ => true
  | fvar .. => true
  | _ => false
partial def maxVarSucc : Term → Nat
  | var x => x + 1
  | bvar .. => 0
  | fvar _ x => x + 1
  | app _ args => args.foldl (fun acc term => Nat.max acc (maxVarSucc term)) 0
  | apply fn arg => Nat.max fn.maxVarSucc arg.maxVarSucc
  | lam _ _ body => body.maxVarSucc
def isSkolemApp : Term → Bool
  | var _ => false
  | bvar .. => false
  | fvar .. => false
  | app symbol _ => symbol.kind == SymbolKind.skolem
  | apply .. => false
  | lam .. => false
partial def isGround : Term → Bool
  | var _ => false
  | bvar .. => true
  | fvar .. => false
  | app _ args => args.all (fun arg => isGround arg)
  | apply fn arg => fn.isGround && arg.isGround
  | lam _ _ body => body.isGround
end Term
mutual
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
  partial def Term.inferSortListWith (bound : List CoreSort) : List Term → Option (List CoreSort)
    | [] => some []
    | term :: rest => do
        let sort ← Term.inferSortWith bound term
        let sorts ← Term.inferSortListWith bound rest
        some (sort :: sorts)
end
namespace Term
def inferSort? (term : Term) : Option CoreSort :=
  Term.inferSortWith [] term
def check? (term : Term) : Bool := (term.inferSort?).isSome
end Term
mutual
  def Term.renameVars (offset : Nat) : Term → Term
    | Term.var x => Term.var (x + offset)
    | Term.bvar sort index => Term.bvar sort index
    | Term.fvar sort x => Term.fvar sort (x + offset)
    | Term.app symbol args => Term.app symbol (Term.renameVarsList offset args)
    | Term.apply fn arg => Term.apply (fn.renameVars offset) (arg.renameVars offset)
    | Term.lam domain codomain body => Term.lam domain codomain (body.renameVars offset)
  def Term.renameVarsList (offset : Nat) : List Term → List Term
    | [] => []
    | term :: rest => term.renameVars offset :: Term.renameVarsList offset rest
end
mutual
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
  def termListEq : List Term → List Term → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        termEq left right && termListEq leftRest rightRest
    | _, _ => false
end
mutual
  @[simp]
  theorem termEq_eq_true {left right : Term} :
      termEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [termEq, termEq_eq_true, termListEq_eq_true, and_assoc]
  @[simp]
  theorem termListEq_eq_true {left right : List Term} :
      termListEq left right = true ↔ left = right := by
    cases left <;> cases right <;> simp [termListEq, termEq_eq_true, termListEq_eq_true]
end
instance instBEqTerm : BEq Term where
  beq := termEq
instance termDecidableEq : DecidableEq Term := fun left right =>
  if h : termEq left right = true then
    isTrue (termEq_eq_true.mp h)
  else
    isFalse (fun hEq => h (termEq_eq_true.mpr hEq))
mutual
  partial def Term.shiftAbove (amount cutoff : Nat) : Term → Term
    | Term.var id => Term.var id
    | Term.bvar sort index =>
        if index < cutoff then Term.bvar sort index else Term.bvar sort (index + amount)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.shiftListAbove amount cutoff args)
    | Term.apply fn arg => Term.apply (fn.shiftAbove amount cutoff) (arg.shiftAbove amount cutoff)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (body.shiftAbove amount (cutoff + 1))
  partial def Term.shiftListAbove (amount cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => term.shiftAbove amount cutoff :: Term.shiftListAbove amount cutoff rest
end
def Term.shift (amount : Nat) (term : Term) : Term :=
  term.shiftAbove amount 0
mutual
  partial def Term.instantiateAt (depth : Nat) (replacement : Term) : Term → Term
    | Term.var id => Term.var id
    | Term.bvar sort index =>
        if index == depth then replacement.shift depth else Term.bvar sort index
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.instantiateListAt depth replacement args)
    | Term.apply fn arg =>
        Term.apply (Term.instantiateAt depth replacement fn) (Term.instantiateAt depth replacement arg)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (Term.instantiateAt (depth + 1) replacement body)
  partial def Term.instantiateListAt (depth : Nat) (replacement : Term) : List Term → List Term
    | [] => []
    | term :: rest =>
        Term.instantiateAt depth replacement term :: Term.instantiateListAt depth replacement rest
end
def Term.instantiate (replacement body : Term) : Term :=
  Term.instantiateAt 0 replacement body
namespace BetaEta
mutual
  partial def Term.occursBVarAt (depth : Nat) : Term → Bool
    | Term.var .. => false
    | Term.bvar _ index => index == depth
    | Term.fvar .. => false
    | Term.app _ args => Term.occursBVarListAt depth args
    | Term.apply fn arg => Term.occursBVarAt depth fn || Term.occursBVarAt depth arg
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body
  partial def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end
mutual
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
  partial def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end
def etaContract? (domain : CoreSort) : Term → Option Term
  | Term.apply fn (Term.bvar argSort 0) =>
      if argSort == domain && !Term.occursBVarAt 0 fn then
        some (Term.lowerAbove 0 fn)
      else
        none
  | _ => none
end BetaEta
mutual
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
  partial def normalizeBetaEtaListWith : Nat → List Term → List Term
    | 0, terms => terms
    | _fuel + 1, [] => []
    | fuel + 1, term :: rest =>
        normalizeBetaEtaWith fuel term :: normalizeBetaEtaListWith fuel rest
end
def normalizeBetaEta (term : Term) : Term :=
  normalizeBetaEtaWith (term.size * 4 + 16) term
def termEqBetaEta (left right : Term) : Bool :=
  termEq (normalizeBetaEta left) (normalizeBetaEta right)
structure Intro where
  symbol : FunctionSymbol
  universalArgs : List Term
  term : Term
  contextDepth : Nat
  deriving Repr, BEq, Lean.ToExpr
namespace Intro
def check (intro : Intro) : Bool :=
  intro.symbol.kind == SymbolKind.skolem &&
    intro.symbol.arity == intro.universalArgs.length &&
    intro.contextDepth == intro.universalArgs.length &&
    termEq intro.term (Term.app intro.symbol intro.universalArgs) &&
    intro.term.arityOk &&
    intro.universalArgs.all Term.isVar
def traceCheck (trace : Array Intro) : Bool :=
  trace.all check
end Intro
structure SpecializationStep where
  binder : VarId
  term : Term
  proxy : VarId
  deriving Repr, BEq, Lean.ToExpr
namespace SpecializationStep
def directVariableOk (step : SpecializationStep) : Bool :=
  step.term == Term.var step.proxy
def check (step : SpecializationStep) : Bool :=
  step.term.arityOk
end SpecializationStep
abbrev SpecializationTrace := Array SpecializationStep
namespace SpecializationTrace
def check (trace : SpecializationTrace) : Bool :=
  trace.all SpecializationStep.check
end SpecializationTrace
inductive PredicateKind where
  | equal
  | member
  | boolHolds
  | definition (id arity : Nat)
  | predicate (symbol : CoreSyntax.PredicateSymbol)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace PredicateKind
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
structure Literal where
  positive : Bool
  predicate : PredicateKind
  left : Term
  right : Term
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
namespace Literal
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
def toCoreFormula (literal : Literal) : CoreSyntax.Formula :=
  if literal.positive then literal.toCoreAtom else CoreSyntax.Formula.neg literal.toCoreAtom
def maxVarSucc (literal : Literal) : Nat :=
  Nat.max literal.left.maxVarSucc literal.right.maxVarSucc
def maxDepth (literal : Literal) : Nat :=
  Nat.max literal.left.depth literal.right.depth
def isGround (literal : Literal) : Bool :=
  literal.left.isGround && literal.right.isGround
def renameVars (offset : Nat) (literal : Literal) : Literal :=
  {
    literal with
    left := literal.left.renameVars offset
    right := literal.right.renameVars offset
  }
end Literal
abbrev Clause := Array Literal
def literalEq (left right : Literal) : Bool :=
  decide (left.positive = right.positive) &&
    decide (left.predicate = right.predicate) &&
    termEq left.left right.left &&
    termEq left.right right.right
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
instance literalDecidableEq : DecidableEq Literal := fun left right =>
  if h : literalEq left right = true then
    isTrue (literalEq_eq_true.mp h)
  else
    isFalse (fun hEq => h (literalEq_eq_true.mpr hEq))
def literalListEq : List Literal → List Literal → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      literalEq left right && literalListEq leftRest rightRest
  | _, _ => false
@[simp]
theorem literalListEq_eq_true {left right : List Literal} :
    literalListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [literalListEq]
  | cons head tail ih =>
      cases right <;> simp [literalListEq, ih]
def clauseEq (left right : Clause) : Bool :=
  literalListEq left.toList right.toList
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
def clauseListEq : List Clause → List Clause → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      clauseEq left right && clauseListEq leftRest rightRest
  | _, _ => false
@[simp]
theorem clauseListEq_eq_true {left right : List Clause} :
    clauseListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [clauseListEq]
  | cons head tail ih =>
      cases right <;> simp [clauseListEq, ih]
def clauseArrayEq (left right : Array Clause) : Bool :=
  clauseListEq left.toList right.toList
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
def toCoreFormula (clause : Clause) : CoreSyntax.Formula :=
  CoreSyntax.Formula.disjunctionList (clause.toList.map Literal.toCoreFormula)
def isGround (clause : Clause) : Bool :=
  clause.all Literal.isGround
def maxVarSucc (clause : Clause) : Nat :=
  Id.run do
    let mut maxVar := 0
    for literal in clause do
      maxVar := Nat.max maxVar literal.maxVarSucc
    return maxVar
def maxDepth (clause : Clause) : Nat :=
  Id.run do
    let mut depth := 0
    for literal in clause do
      depth := Nat.max depth literal.maxDepth
    return depth
def renameVars (offset : Nat) (clause : Clause) : Clause :=
  clause.map (fun literal => literal.renameVars offset)
end Clause
/-!
## 搜索层替换、匹配与合一
搜索变量使用 `(sort, id)` 作为唯一身份。旧 `.var id` 只是对象 sort 自由变量的紧凑
表面；`.fvar sort id` 与它进入 substitution、standardize-apart 和索引前共享同一变量键。
-/
structure Variable where
  sort : CoreSort
  id : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr
namespace Variable
def object (id : VarId) : Variable := {
  sort := CoreSort.object
  id := id
}
def toTerm (key : Variable) : Term :=
  Term.fvar key.sort key.id
def matchesTerm (key : Variable) : Term → Bool
  | Term.var id => key.sort == CoreSort.object && key.id == id
  | Term.fvar sort id => key.sort == sort && key.id == id
  | _ => false
end Variable
namespace Term
def variable? : Term → Option Variable
  | Term.var id => some (Variable.object id)
  | Term.fvar sort id => some { sort := sort, id := id }
  | _ => none
mutual
  def variables : Term → List Variable
    | Term.var id => [Variable.object id]
    | Term.bvar .. => []
    | Term.fvar sort id => [{ sort := sort, id := id }]
    | Term.app _ args => variablesList args
    | Term.apply fn arg => variables fn ++ variables arg
    | Term.lam _ _ body => variables body
  def variablesList : List Term → List Variable
    | [] => []
    | term :: rest => variables term ++ variablesList rest
end
partial def occursVariable (key : Variable) : Term → Bool
  | Term.var id => key.matchesTerm (Term.var id)
  | Term.bvar .. => false
  | Term.fvar sort id => key.matchesTerm (Term.fvar sort id)
  | Term.app _ args => args.any (occursVariable key)
  | Term.apply fn arg => occursVariable key fn || occursVariable key arg
  | Term.lam _ _ body => occursVariable key body
end Term
structure SubstitutionBinding where
  key : Variable
  replacement : Term
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
abbrev Substitution := List SubstitutionBinding
namespace Substitution
def empty : Substitution := []
def singleton (key : Variable) (replacement : Term) : Substitution :=
  [{ key := key, replacement := replacement }]
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
  def Substitution.applyTerms (subst : Substitution) : List Term → List Term
    | [] => []
    | term :: rest => Substitution.applyTerm subst term :: Substitution.applyTerms subst rest
end
namespace Substitution
def applyLiteral (subst : Substitution) (literal : Literal) : Literal :=
  {
    literal with
    left := applyTerm subst literal.left
    right := applyTerm subst literal.right
  }
def applyClause (subst : Substitution) (clause : Clause) : Clause :=
  clause.map (fun literal => applyLiteral subst literal)
def compose (first second : Substitution) : Substitution :=
  first.map (fun binding =>
    { binding with replacement := applyTerm second binding.replacement }) ++ second
def rewriteBinding (key : Variable) (term : Term) (binding : SubstitutionBinding) : SubstitutionBinding :=
  {
    binding with
    replacement := applyTerm (singleton key term) binding.replacement
  }
def bind? (key : Variable) (term : Term) (subst : Substitution) : Option Substitution :=
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
    {key : Variable} {term : Term} (hLookup : lookup subst key = some term) :
    lookup (subst ++ rest) key = some term := by
  rw [lookup_append, hLookup]
@[simp]
theorem lookup_append_right {subst rest : Substitution}
    {key : Variable} (hLookup : lookup subst key = none) :
    lookup (subst ++ rest) key = lookup rest key := by
  rw [lookup_append, hLookup]
theorem lookup_map_replacements (subst : Substitution) (second : Substitution) (key : Variable) :
    lookup (subst.map fun binding =>
          { binding with replacement := applyTerm second binding.replacement })
        key = (lookup subst key).map (applyTerm second) := by
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
def zipTermPairs? : List Term → List Term → Option (List (Term × Term))
  | [], [] => some []
  | left :: leftRest, right :: rightRest =>
      match zipTermPairs? leftRest rightRest with
      | some rest => some ((left, right) :: rest)
      | none => none
  | _, _ => none
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
def unifyFO? (left right : Term) : Option Substitution :=
  unifyLoop [] [(left, right)]
abbrev PatternSubstitution := Substitution
namespace PatternSubstitution
def empty : PatternSubstitution := Substitution.empty
abbrev applyTerm := Substitution.applyTerm
abbrev bind? := Substitution.bind?
end PatternSubstitution
namespace HOUnification
inductive Result where
  | solved (subst : PatternSubstitution)
  | residual (constraints : List (Term × Term))
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace Result
def toOption : Result → Option Substitution
  | solved subst => some subst
  | residual _ => none
def hasResidual : Result → Bool
  | solved _ => false
  | residual _ => true
end Result
inductive PatternArg where
  | mvar (id : VarId)
  | free (sort : CoreSort) (id : VarId)
  | bound (sort : CoreSort) (index : Nat)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
namespace PatternArg
def sort : PatternArg → CoreSort
  | mvar _ => CoreSort.object
  | free sort _ => sort
  | bound sort _ => sort
def toTerm : PatternArg → Term
  | mvar id => Term.var id
  | free sort id => Term.fvar sort id
  | bound sort index => Term.bvar sort index
def toTermAtDepth (depth : Nat) : PatternArg → Term
  | mvar id => Term.var id
  | free sort id => Term.fvar sort id
  | bound sort index => Term.bvar sort (index + depth)
def eq (left right : PatternArg) : Bool :=
  left == right
def mem (arg : PatternArg) : List PatternArg → Bool
  | [] => false
  | head :: rest => eq arg head || mem arg rest
end PatternArg
partial def collectSpine : Term → Term × List Term
  | Term.apply fn arg =>
      let (head, args) := collectSpine fn
      (head, args ++ [arg])
  | term => (term, [])
def patternArg? : Term → Option PatternArg
  | Term.var id => some (PatternArg.mvar id)
  | Term.fvar sort id => some (PatternArg.free sort id)
  | Term.bvar sort index => some (PatternArg.bound sort index)
  | _ => none
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
def abstractionBodyOk (key : Variable) (body : Term) : Bool :=
  !Term.occursVariable key body
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
def abstractionIndex (args : List PatternArg) (position depth : Nat) : Nat :=
  depth + (args.length - position - 1)
mutual
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
                Term.apply (abstractPatternArgsWith args depth fn) (abstractPatternArgsWith args depth arg)
            | Term.lam domain codomain body =>
                Term.lam domain codomain (abstractPatternArgsWith args (depth + 1) body)
  partial def abstractPatternArgsListWith (args : List PatternArg) (depth : Nat) :
      List Term → List Term
    | [] => []
    | term :: rest =>
        abstractPatternArgsWith args depth term :: abstractPatternArgsListWith args depth rest
end
def abstractPatternArgs (args : List PatternArg) (target : Term) : Term :=
  abstractPatternArgsWith args 0 target
def closePatternBinding (args : List PatternArg) (target : Term) : Term :=
  let body := abstractPatternArgs args target
  let bodySort := (Term.inferSortWith (args.reverse.map PatternArg.sort) body).getD CoreSort.object
  let (_, closed) :=
    args.foldr (fun arg acc =>
        let codomain := acc.1
        let term := acc.2
        let closed := Term.lam arg.sort codomain term
        (CoreSort.arrow arg.sort codomain, closed)) (bodySort, body)
  closed
def patternBind? (head : Term) (args : List Term) (target : Term) (subst : PatternSubstitution) : Option PatternSubstitution :=
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
def isPatternHead : Term → Bool
  | Term.var _ => true
  | Term.fvar sort _ => isFlexibleSort sort
  | _ => false
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
def unifyPattern (left right : Term) : Result :=
  patternLoop PatternSubstitution.empty [(left, right)]
def unify (left right : Term) : Result :=
  match unifyLoop [] [(left, right)] with
  | some subst => Result.solved subst
  | none => unifyPattern left right
end HOUnification
def unify? (left right : Term) : Option Substitution := (HOUnification.unify left right).toOption
def unifyConstraints? (constraints : List (Term × Term)) : Option Substitution :=
  match unifyLoop [] constraints with
  | some subst => some subst
  | none => (HOUnification.patternLoop PatternSubstitution.empty constraints).toOption
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
def matchTerm? (pattern target : Term) : Option Substitution :=
  matchLoop [] [(pattern, target)]
def unifyTwoPairs? (a b c d : Term) : Option Substitution :=
  unifyConstraints? [(a, b), (c, d)]
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
def standardizeApart (left right : Clause) : Clause × Clause :=
  let offset := Clause.maxVarSucc left
  (left, Clause.renameVars offset right)
end Search
end CoreSyntax
end Automation
end YesMetaZFC
