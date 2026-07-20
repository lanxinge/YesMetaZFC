import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.CoreSyntax

/-!
# MF1 自动化：核心语法 normal form

本模块给 `CoreSyntax` 增加可计算归一化层。它只处理后端语法本身，不接触 MF1 章节
soundness 实例：

* 局部无名索引的 lift / instantiate；
* lambda βη 归约与函数外延化；
* FOOL 的公式/布尔项互嵌消去；
* 命题联结词的局部常量化简；
* core NNF、前束视图与 CNF 矩阵；
* 搜索层 literal / clause 到核心 normal form 的投影。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm

namespace CoreSort

/-- 若 sort 是函数 sort，取出定义域和值域。 -/
def arrow? : CoreSort → Option (CoreSort × CoreSort)
  | CoreSort.arrow domain codomain => some (domain, codomain)
  | _ => none

end CoreSort

/-- normal form 的执行配置。 -/
structure Config where
  fuel : Nat := 512
  beta : Bool := true
  eta : Bool := true
  extensionality : Bool := true
  fool : Bool := true
  connectiveSimp : Bool := true
  quantifierSimp : Bool := true
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Config

/--
纯一阶入口使用的恒等归一化配置。

一阶 source 不需要 FOOL、lambda 或局部逻辑化简；保持公式原样可以让预处理 soundness
只依赖一阶 Tarski 模型，而不要求调用者伪造高阶语义合同。
-/
def firstOrderIdentity : Config := {
  beta := false
  eta := false
  extensionality := false
  fool := false
  connectiveSimp := false
  quantifierSimp := false
}

end Config

namespace SyntaxEq

mutual
  /-- 核心项的透明结构相等。 -/
  def termEq : Term → Term → Bool
    | Term.bvar leftSort leftIndex, Term.bvar rightSort rightIndex =>
        decide (leftSort = rightSort) && decide (leftIndex = rightIndex)
    | Term.fvar leftSort leftId, Term.fvar rightSort rightId =>
        decide (leftSort = rightSort) && decide (leftId = rightId)
    | Term.app leftSymbol leftArgs, Term.app rightSymbol rightArgs =>
        decide (leftSymbol = rightSymbol) && termListEq leftArgs rightArgs
    | Term.apply leftFn leftArg, Term.apply rightFn rightArg =>
        termEq leftFn rightFn && termEq leftArg rightArg
    | Term.bool leftValue, Term.bool rightValue =>
        decide (leftValue = rightValue)
    | Term.notE leftBody, Term.notE rightBody =>
        termEq leftBody rightBody
    | Term.andE leftA leftB, Term.andE rightA rightB
    | Term.orE leftA leftB, Term.orE rightA rightB
    | Term.impE leftA leftB, Term.impE rightA rightB
    | Term.iffE leftA leftB, Term.iffE rightA rightB =>
        termEq leftA rightA && termEq leftB rightB
    | Term.quote leftFormula, Term.quote rightFormula =>
        formulaEq leftFormula rightFormula
    | Term.lam leftDomain leftCodomain leftBody, Term.lam rightDomain rightCodomain rightBody =>
        decide (leftDomain = rightDomain) && decide (leftCodomain = rightCodomain) &&
          termEq leftBody rightBody
    | Term.ite leftSort leftCond leftThen leftElse, Term.ite rightSort rightCond rightThen rightElse =>
        decide (leftSort = rightSort) && formulaEq leftCond rightCond &&
          termEq leftThen rightThen && termEq leftElse rightElse
    | _, _ => false

  /-- 核心公式的透明结构相等。 -/
  def formulaEq : Formula → Formula → Bool
    | Formula.trueE, Formula.trueE => true
    | Formula.falseE, Formula.falseE => true
    | Formula.atom leftPredicate leftArgs, Formula.atom rightPredicate rightArgs =>
        decide (leftPredicate = rightPredicate) && termListEq leftArgs rightArgs
    | Formula.equal leftSort leftLeft leftRight, Formula.equal rightSort rightLeft rightRight =>
        decide (leftSort = rightSort) && termEq leftLeft rightLeft && termEq leftRight rightRight
    | Formula.boolTerm leftTerm, Formula.boolTerm rightTerm =>
        termEq leftTerm rightTerm
    | Formula.neg leftBody, Formula.neg rightBody =>
        formulaEq leftBody rightBody
    | Formula.imp leftA leftB, Formula.imp rightA rightB
    | Formula.conj leftA leftB, Formula.conj rightA rightB
    | Formula.disj leftA leftB, Formula.disj rightA rightB
    | Formula.iffE leftA leftB, Formula.iffE rightA rightB =>
        formulaEq leftA rightA && formulaEq leftB rightB
    | Formula.forallE leftSort leftBody, Formula.forallE rightSort rightBody
    | Formula.existsE leftSort leftBody, Formula.existsE rightSort rightBody =>
        decide (leftSort = rightSort) && formulaEq leftBody rightBody
    | _, _ => false

  /-- 核心项列表的透明结构相等。 -/
  def termListEq : List Term → List Term → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        termEq left right && termListEq leftRest rightRest
    | _, _ => false
end

end SyntaxEq

mutual
  /--
  把大于等于 `cutoff` 的局部无名索引整体上移 `amount`。

  这是 beta 归约中把替换项穿过若干本地绑定器时需要的 lift。
  -/
  def Term.shiftAbove (amount cutoff : Nat) : Term → Term
    | Term.bvar sort index =>
        if index < cutoff then
          Term.bvar sort index
        else
          Term.bvar sort (index + amount)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.shiftListAbove amount cutoff args)
    | Term.apply fn arg =>
        Term.apply (Term.shiftAbove amount cutoff fn) (Term.shiftAbove amount cutoff arg)
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.shiftAbove amount cutoff body)
    | Term.andE left right =>
        Term.andE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.orE left right =>
        Term.orE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.impE left right =>
        Term.impE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.iffE left right =>
        Term.iffE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.quote formula => Term.quote (Formula.shiftAbove amount cutoff formula)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (Term.shiftAbove amount (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.shiftAbove amount cutoff condition)
          (Term.shiftAbove amount cutoff thenTerm) (Term.shiftAbove amount cutoff elseTerm)

  /-- 公式中的局部无名索引 lift。 -/
  def Formula.shiftAbove (amount cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.shiftListAbove amount cutoff args)
    | Formula.equal sort left right =>
        Formula.equal sort (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.shiftAbove amount cutoff term)
    | Formula.neg body => Formula.neg (Formula.shiftAbove amount cutoff body)
    | Formula.imp left right =>
        Formula.imp (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.conj left right =>
        Formula.conj (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.disj left right =>
        Formula.disj (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.iffE left right =>
        Formula.iffE (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.forallE sort body =>
        Formula.forallE sort (Formula.shiftAbove amount (cutoff + 1) body)
    | Formula.existsE sort body =>
        Formula.existsE sort (Formula.shiftAbove amount (cutoff + 1) body)

  /-- 项列表中的局部无名索引 lift。 -/
  def Term.shiftListAbove (amount cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest =>
        Term.shiftAbove amount cutoff term :: Term.shiftListAbove amount cutoff rest
end

/-- 把所有自由于当前上下文的局部无名索引整体上移。 -/
def Term.shift (amount : Nat) (term : Term) : Term :=
  Term.shiftAbove amount 0 term

/-- 把公式中所有自由于当前上下文的局部无名索引整体上移。 -/
def Formula.shift (amount : Nat) (formula : Formula) : Formula :=
  Formula.shiftAbove amount 0 formula

mutual
  /--
  删除深度 `depth` 的绑定器，并用 `replacement` 替换该绑定器。

  若遇到更外层的局部无名索引，需要下移一位；替换项穿过 `depth` 个本地绑定器时会
  自动 lift。
  -/
  def Term.instantiateAt (depth : Nat) (replacement : Term) : Term → Term
    | Term.bvar sort index =>
        if index < depth then
          Term.bvar sort index
        else if index == depth then
          Term.shift depth replacement
        else
          Term.bvar sort (index - 1)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.instantiateListAt depth replacement args)
    | Term.apply fn arg =>
        Term.apply (Term.instantiateAt depth replacement fn)
          (Term.instantiateAt depth replacement arg)
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.instantiateAt depth replacement body)
    | Term.andE left right =>
        Term.andE (Term.instantiateAt depth replacement left)
          (Term.instantiateAt depth replacement right)
    | Term.orE left right =>
        Term.orE (Term.instantiateAt depth replacement left)
          (Term.instantiateAt depth replacement right)
    | Term.impE left right =>
        Term.impE (Term.instantiateAt depth replacement left)
          (Term.instantiateAt depth replacement right)
    | Term.iffE left right =>
        Term.iffE (Term.instantiateAt depth replacement left)
          (Term.instantiateAt depth replacement right)
    | Term.quote formula => Term.quote (Formula.instantiateAt depth replacement formula)
    | Term.lam domain codomain body =>
        Term.lam domain codomain (Term.instantiateAt (depth + 1) replacement body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.instantiateAt depth replacement condition)
          (Term.instantiateAt depth replacement thenTerm)
          (Term.instantiateAt depth replacement elseTerm)

  /-- 公式中的局部无名绑定器实例化。 -/
  def Formula.instantiateAt (depth : Nat) (replacement : Term) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args =>
        Formula.atom predicate (Term.instantiateListAt depth replacement args)
    | Formula.equal sort left right =>
        Formula.equal sort (Term.instantiateAt depth replacement left)
          (Term.instantiateAt depth replacement right)
    | Formula.boolTerm term => Formula.boolTerm (Term.instantiateAt depth replacement term)
    | Formula.neg body => Formula.neg (Formula.instantiateAt depth replacement body)
    | Formula.imp left right =>
        Formula.imp (Formula.instantiateAt depth replacement left)
          (Formula.instantiateAt depth replacement right)
    | Formula.conj left right =>
        Formula.conj (Formula.instantiateAt depth replacement left)
          (Formula.instantiateAt depth replacement right)
    | Formula.disj left right =>
        Formula.disj (Formula.instantiateAt depth replacement left)
          (Formula.instantiateAt depth replacement right)
    | Formula.iffE left right =>
        Formula.iffE (Formula.instantiateAt depth replacement left)
          (Formula.instantiateAt depth replacement right)
    | Formula.forallE sort body =>
        Formula.forallE sort (Formula.instantiateAt (depth + 1) replacement body)
    | Formula.existsE sort body =>
        Formula.existsE sort (Formula.instantiateAt (depth + 1) replacement body)

  /-- 项列表中的局部无名绑定器实例化。 -/
  def Term.instantiateListAt (depth : Nat) (replacement : Term) : List Term → List Term
    | [] => []
    | term :: rest =>
        Term.instantiateAt depth replacement term ::
          Term.instantiateListAt depth replacement rest
end

/-- 顶层 lambda / quantifier body 的实例化入口。 -/
def Term.instantiate (replacement body : Term) : Term :=
  Term.instantiateAt 0 replacement body

/-- 顶层公式 body 的实例化入口。 -/
def Formula.instantiate (replacement : Term) (body : Formula) : Formula :=
  Formula.instantiateAt 0 replacement body

namespace Eta

mutual
  /-- η 收缩前检查指定 De Bruijn 深度是否真实出现。 -/
  def Term.occursBVarAt (depth : Nat) : Term → Bool
    | Term.bvar _ index => index == depth
    | Term.fvar .. => false
    | Term.app _ args => Term.occursBVarListAt depth args
    | Term.apply fn arg => Term.occursBVarAt depth fn || Term.occursBVarAt depth arg
    | Term.bool _ => false
    | Term.notE body => Term.occursBVarAt depth body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Term.quote formula => Formula.occursBVarAt depth formula
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.occursBVarAt depth condition ||
          Term.occursBVarAt depth thenTerm ||
            Term.occursBVarAt depth elseTerm

  /-- η 收缩前检查公式中的指定 De Bruijn 深度。 -/
  def Formula.occursBVarAt (depth : Nat) : Formula → Bool
    | Formula.trueE => false
    | Formula.falseE => false
    | Formula.atom _ args => Term.occursBVarListAt depth args
    | Formula.equal _ left right =>
        Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Formula.boolTerm term => Term.occursBVarAt depth term
    | Formula.neg body => Formula.occursBVarAt depth body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Formula.occursBVarAt depth left || Formula.occursBVarAt depth right
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Formula.occursBVarAt (depth + 1) body

  /-- η 收缩前检查项列表中的指定 De Bruijn 深度。 -/
  def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end

mutual
  /-- η 收缩删除当前 binder 后，下移更外层 De Bruijn 索引。 -/
  def Term.lowerAbove (cutoff : Nat) : Term → Term
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
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.lowerAbove cutoff body)
    | Term.andE left right =>
        Term.andE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.orE left right =>
        Term.orE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.impE left right =>
        Term.impE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.iffE left right =>
        Term.iffE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.quote formula => Term.quote (Formula.lowerAbove cutoff formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.lowerAbove (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.lowerAbove cutoff condition)
          (Term.lowerAbove cutoff thenTerm) (Term.lowerAbove cutoff elseTerm)

  /-- η 收缩时公式里的 De Bruijn 索引下移。 -/
  def Formula.lowerAbove (cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.lowerListAbove cutoff args)
    | Formula.equal sort left right =>
        Formula.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.lowerAbove cutoff term)
    | Formula.neg body => Formula.neg (Formula.lowerAbove cutoff body)
    | Formula.imp left right =>
        Formula.imp (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.conj left right =>
        Formula.conj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.disj left right =>
        Formula.disj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.iffE left right =>
        Formula.iffE (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.lowerAbove (cutoff + 1) body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.lowerAbove (cutoff + 1) body)

  /-- η 收缩时项列表里的 De Bruijn 索引下移。 -/
  def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end

/-- 若 `body` 是 `f bvar0` 且 `bvar0` 不自由出现在 `f`，执行 lambda η 收缩。 -/
def contract? (domain : CoreSort) : Term → Option Term
  | Term.apply fn (Term.bvar argSort 0) =>
      if argSort == domain && !Term.occursBVarAt 0 fn then
        some (Term.lowerAbove 0 fn)
      else
        none
  | _ => none

end Eta

mutual
  /-- 在给定燃料内归一化核心项。 -/
  def normalizeTermWith (config : Config) : Nat → Term → Term
    | 0, term => term
    | _fuel + 1, Term.bvar sort index => Term.bvar sort index
    | _fuel + 1, Term.fvar sort id => Term.fvar sort id
    | fuel + 1, Term.app symbol args =>
        Term.app symbol (normalizeTermListWith config fuel args)
    | fuel + 1, Term.apply fn arg =>
        let fn' := normalizeTermWith config fuel fn
        let arg' := normalizeTermWith config fuel arg
        match config.beta, fn' with
        | true, Term.lam _ _ body => normalizeTermWith config fuel (Term.instantiate arg' body)
        | _, _ => Term.apply fn' arg'
    | _fuel + 1, Term.bool value => Term.bool value
    | fuel + 1, Term.notE body =>
        let body' := normalizeTermWith config fuel body
        if config.fool then
          match body' with
          | Term.bool true => Term.bool false
          | Term.bool false => Term.bool true
          | Term.quote formula => normalizeTermWith config fuel (Term.quote (Formula.neg formula))
          | Term.notE inner => inner
          | _ => Term.notE body'
        else
          Term.notE body'
    | fuel + 1, Term.andE left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.fool then
          match left', right' with
          | Term.bool false, _ => Term.bool false
          | _, Term.bool false => Term.bool false
          | Term.bool true, _ => right'
          | _, Term.bool true => left'
          | Term.quote leftFormula, Term.quote rightFormula =>
              normalizeTermWith config fuel (Term.quote (Formula.conj leftFormula rightFormula))
          | _, _ =>
              if SyntaxEq.termEq left' right' then left' else Term.andE left' right'
        else
          Term.andE left' right'
    | fuel + 1, Term.orE left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.fool then
          match left', right' with
          | Term.bool true, _ => Term.bool true
          | _, Term.bool true => Term.bool true
          | Term.bool false, _ => right'
          | _, Term.bool false => left'
          | Term.quote leftFormula, Term.quote rightFormula =>
              normalizeTermWith config fuel (Term.quote (Formula.disj leftFormula rightFormula))
          | _, _ =>
              if SyntaxEq.termEq left' right' then left' else Term.orE left' right'
        else
          Term.orE left' right'
    | fuel + 1, Term.impE left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.fool then
          if SyntaxEq.termEq left' right' then
            Term.bool true
          else
            match left', right' with
            | Term.bool false, _ => Term.bool true
            | Term.bool true, _ => right'
            | _, Term.bool true => Term.bool true
            | _, Term.bool false => normalizeTermWith config fuel (Term.notE left')
            | Term.quote leftFormula, Term.quote rightFormula =>
                normalizeTermWith config fuel (Term.quote (Formula.imp leftFormula rightFormula))
            | _, _ => Term.impE left' right'
        else
          Term.impE left' right'
    | fuel + 1, Term.iffE left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.fool then
          if SyntaxEq.termEq left' right' then
            Term.bool true
          else
            match left', right' with
            | Term.bool true, _ => right'
            | _, Term.bool true => left'
            | Term.bool false, _ => normalizeTermWith config fuel (Term.notE right')
            | _, Term.bool false => normalizeTermWith config fuel (Term.notE left')
            | Term.quote leftFormula, Term.quote rightFormula =>
                normalizeTermWith config fuel (Term.quote (Formula.iffE leftFormula rightFormula))
            | _, _ => Term.iffE left' right'
        else
          Term.iffE left' right'
    | fuel + 1, Term.quote formula =>
        let formula' := normalizeFormulaWith config fuel formula
        if config.fool then
          match formula' with
          | Formula.trueE => Term.bool true
          | Formula.falseE => Term.bool false
          | _ => Term.quote formula'
        else
          Term.quote formula'
    | fuel + 1, Term.lam domain codomain body =>
        let body' := normalizeTermWith config fuel body
        if config.eta then
          match Eta.contract? domain body' with
          | some contracted => normalizeTermWith config fuel contracted
          | none => Term.lam domain codomain body'
        else
          Term.lam domain codomain body'
    | fuel + 1, Term.ite sort condition thenTerm elseTerm =>
        let condition' := normalizeFormulaWith config fuel condition
        let thenTerm' := normalizeTermWith config fuel thenTerm
        let elseTerm' := normalizeTermWith config fuel elseTerm
        if config.connectiveSimp then
          match condition' with
          | Formula.trueE => thenTerm'
          | Formula.falseE => elseTerm'
          | _ =>
              if SyntaxEq.termEq thenTerm' elseTerm' then
                thenTerm'
              else if config.fool && sort == CoreSort.bool then
                match thenTerm', elseTerm' with
                | Term.bool true, Term.bool false =>
                    normalizeTermWith config fuel (Term.quote condition')
                | Term.bool false, Term.bool true =>
                    normalizeTermWith config fuel (Term.quote (Formula.neg condition'))
                | Term.bool true, _ =>
                    normalizeTermWith config fuel (Term.orE (Term.quote condition') elseTerm')
                | Term.bool false, _ =>
                    normalizeTermWith config fuel
                      (Term.andE (Term.notE (Term.quote condition')) elseTerm')
                | _, Term.bool true =>
                    normalizeTermWith config fuel (Term.impE (Term.quote condition') thenTerm')
                | _, Term.bool false =>
                    normalizeTermWith config fuel (Term.andE (Term.quote condition') thenTerm')
                | _, _ => Term.ite sort condition' thenTerm' elseTerm'
              else
                Term.ite sort condition' thenTerm' elseTerm'
        else
          Term.ite sort condition' thenTerm' elseTerm'

  /-- 在给定燃料内归一化核心公式。 -/
  def normalizeFormulaWith (config : Config) : Nat → Formula → Formula
    | 0, formula => formula
    | _fuel + 1, Formula.trueE => Formula.trueE
    | _fuel + 1, Formula.falseE => Formula.falseE
    | fuel + 1, Formula.atom predicate args =>
        Formula.atom predicate (normalizeTermListWith config fuel args)
    | fuel + 1, Formula.equal sort left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.connectiveSimp && SyntaxEq.termEq left' right' then
          Formula.trueE
        else if config.extensionality then
          match CoreSort.arrow? sort with
          | some (domain, codomain) =>
              normalizeFormulaWith config fuel
                (Formula.forallE domain
                  (Formula.equal codomain
                    (Term.apply (Term.shift 1 left') (Term.bvar domain 0))
                    (Term.apply (Term.shift 1 right') (Term.bvar domain 0))))
          | none =>
              if config.fool && sort == CoreSort.bool then
                match left', right' with
                | Term.bool true, _ => normalizeFormulaWith config fuel (Formula.boolTerm right')
                | _, Term.bool true => normalizeFormulaWith config fuel (Formula.boolTerm left')
                | Term.bool false, _ =>
                    normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm right'))
                | _, Term.bool false =>
                    normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm left'))
                | Term.quote leftFormula, Term.quote rightFormula =>
                    normalizeFormulaWith config fuel (Formula.iffE leftFormula rightFormula)
                | _, _ =>
                    normalizeFormulaWith config fuel
                      (Formula.iffE (Formula.boolTerm left') (Formula.boolTerm right'))
              else
                Formula.equal sort left' right'
        else if config.fool && sort == CoreSort.bool then
          match left', right' with
          | Term.bool true, _ => normalizeFormulaWith config fuel (Formula.boolTerm right')
          | _, Term.bool true => normalizeFormulaWith config fuel (Formula.boolTerm left')
          | Term.bool false, _ =>
              normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm right'))
          | _, Term.bool false =>
              normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm left'))
          | Term.quote leftFormula, Term.quote rightFormula =>
              normalizeFormulaWith config fuel (Formula.iffE leftFormula rightFormula)
          | _, _ =>
              normalizeFormulaWith config fuel
                (Formula.iffE (Formula.boolTerm left') (Formula.boolTerm right'))
        else
          Formula.equal sort left' right'
    | fuel + 1, Formula.boolTerm term =>
        let term' := normalizeTermWith config fuel term
        if config.fool then
          match term' with
          | Term.bool true => Formula.trueE
          | Term.bool false => Formula.falseE
          | Term.notE body =>
              normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm body))
          | Term.andE left right =>
              normalizeFormulaWith config fuel (Formula.conj (Formula.boolTerm left)
                (Formula.boolTerm right))
          | Term.orE left right =>
              normalizeFormulaWith config fuel (Formula.disj (Formula.boolTerm left)
                (Formula.boolTerm right))
          | Term.impE left right =>
              normalizeFormulaWith config fuel (Formula.imp (Formula.boolTerm left)
                (Formula.boolTerm right))
          | Term.iffE left right =>
              normalizeFormulaWith config fuel (Formula.iffE (Formula.boolTerm left)
                (Formula.boolTerm right))
          | Term.quote formula => normalizeFormulaWith config fuel formula
          | Term.ite sort condition thenTerm elseTerm =>
              if sort == CoreSort.bool then
                normalizeFormulaWith config fuel
                  (Formula.disj
                    (Formula.conj condition (Formula.boolTerm thenTerm))
                    (Formula.conj (Formula.neg condition) (Formula.boolTerm elseTerm)))
              else
                Formula.boolTerm term'
          | _ => Formula.boolTerm term'
        else
          Formula.boolTerm term'
    | fuel + 1, Formula.neg body =>
        let body' := normalizeFormulaWith config fuel body
        if config.connectiveSimp then
          match body' with
          | Formula.trueE => Formula.falseE
          | Formula.falseE => Formula.trueE
          | Formula.neg inner => inner
          | _ => Formula.neg body'
        else
          Formula.neg body'
    | fuel + 1, Formula.imp left right =>
        let left' := normalizeFormulaWith config fuel left
        let right' := normalizeFormulaWith config fuel right
        if config.connectiveSimp then
          match left', right' with
          | Formula.falseE, _ => Formula.trueE
          | Formula.trueE, _ => right'
          | _, Formula.trueE => Formula.trueE
          | _, Formula.falseE => normalizeFormulaWith config fuel (Formula.neg left')
          | _, _ =>
              if SyntaxEq.formulaEq left' right' then Formula.trueE else Formula.imp left' right'
        else
          Formula.imp left' right'
    | fuel + 1, Formula.conj left right =>
        let left' := normalizeFormulaWith config fuel left
        let right' := normalizeFormulaWith config fuel right
        if config.connectiveSimp then
          match left', right' with
          | Formula.falseE, _ => Formula.falseE
          | _, Formula.falseE => Formula.falseE
          | Formula.trueE, _ => right'
          | _, Formula.trueE => left'
          | _, _ =>
              if SyntaxEq.formulaEq left' right' then left' else Formula.conj left' right'
        else
          Formula.conj left' right'
    | fuel + 1, Formula.disj left right =>
        let left' := normalizeFormulaWith config fuel left
        let right' := normalizeFormulaWith config fuel right
        if config.connectiveSimp then
          match left', right' with
          | Formula.trueE, _ => Formula.trueE
          | _, Formula.trueE => Formula.trueE
          | Formula.falseE, _ => right'
          | _, Formula.falseE => left'
          | _, _ =>
              if SyntaxEq.formulaEq left' right' then left' else Formula.disj left' right'
        else
          Formula.disj left' right'
    | fuel + 1, Formula.iffE left right =>
        let left' := normalizeFormulaWith config fuel left
        let right' := normalizeFormulaWith config fuel right
        if config.connectiveSimp then
          match left', right' with
          | Formula.trueE, _ => right'
          | _, Formula.trueE => left'
          | Formula.falseE, _ => normalizeFormulaWith config fuel (Formula.neg right')
          | _, Formula.falseE => normalizeFormulaWith config fuel (Formula.neg left')
          | _, _ =>
              if SyntaxEq.formulaEq left' right' then Formula.trueE else Formula.iffE left' right'
        else
          Formula.iffE left' right'
    | fuel + 1, Formula.forallE sort body =>
        let body' := normalizeFormulaWith config fuel body
        if config.quantifierSimp then
          match body' with
          | Formula.trueE => Formula.trueE
          | _ => Formula.forallE sort body'
        else
          Formula.forallE sort body'
    | fuel + 1, Formula.existsE sort body =>
        let body' := normalizeFormulaWith config fuel body
        if config.quantifierSimp then
          match body' with
          | Formula.falseE => Formula.falseE
          | _ => Formula.existsE sort body'
        else
          Formula.existsE sort body'

  /-- 在给定燃料内归一化核心项列表。 -/
  def normalizeTermListWith (config : Config) : Nat → List Term → List Term
    | 0, terms => terms
    | _fuel + 1, [] => []
    | fuel + 1, term :: rest =>
        normalizeTermWith config fuel term :: normalizeTermListWith config fuel rest
end

/-- 默认配置下的核心项 normal form。 -/
def normalizeTerm (term : Term) (config : Config := {}) : Term :=
  normalizeTermWith config config.fuel term

/-- 默认配置下的核心公式 normal form。 -/
def normalizeFormula (formula : Formula) (config : Config := {}) : Formula :=
  normalizeFormulaWith config config.fuel formula

/-- 默认配置下的核心项列表 normal form。 -/
def normalizeTermList (terms : List Term) (config : Config := {}) : List Term :=
  normalizeTermListWith config config.fuel terms

/-- normalization trace 中的一步规则标签。 -/
inductive StepRule where
  | beta
  | eta
  | foolQuote
  | foolBoolTerm
  | boolEquality
  | boolIte
  | functionExtensionality
  | connectiveSimp
  | quantifierSimp
  | equalityRefl
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 只检查项根部的一步归约，不递归进入子项。 -/
def rewriteRootTerm? (config : Config) : Term → Option (StepRule × Term)
  | Term.apply fn argument =>
      if config.beta then
        match fn with
        | Term.lam _ _ body => some (StepRule.beta, Term.instantiate argument body)
        | _ => none
      else
        none
  | Term.notE body =>
      if config.fool then
        match body with
        | Term.bool value => some (StepRule.connectiveSimp, Term.bool (!value))
        | Term.quote formula => some (StepRule.foolQuote, Term.quote (Formula.neg formula))
        | _ => none
      else
        none
  | Term.andE left right =>
      if config.fool then
        match left, right with
        | Term.bool false, _ => some (StepRule.connectiveSimp, Term.bool false)
        | _, Term.bool false => some (StepRule.connectiveSimp, Term.bool false)
        | Term.bool true, _ => some (StepRule.connectiveSimp, right)
        | _, Term.bool true => some (StepRule.connectiveSimp, left)
        | Term.quote leftFormula, Term.quote rightFormula =>
            some (StepRule.foolQuote, Term.quote (Formula.conj leftFormula rightFormula))
        | _, _ =>
            if SyntaxEq.termEq left right then
              some (StepRule.connectiveSimp, left)
            else
              none
      else
        none
  | Term.orE left right =>
      if config.fool then
        match left, right with
        | Term.bool true, _ => some (StepRule.connectiveSimp, Term.bool true)
        | _, Term.bool true => some (StepRule.connectiveSimp, Term.bool true)
        | Term.bool false, _ => some (StepRule.connectiveSimp, right)
        | _, Term.bool false => some (StepRule.connectiveSimp, left)
        | Term.quote leftFormula, Term.quote rightFormula =>
            some (StepRule.foolQuote, Term.quote (Formula.disj leftFormula rightFormula))
        | _, _ =>
            if SyntaxEq.termEq left right then
              some (StepRule.connectiveSimp, left)
            else
              none
      else
        none
  | Term.impE left right =>
      if config.fool then
        match left, right with
        | Term.bool false, _ => some (StepRule.connectiveSimp, Term.bool true)
        | Term.bool true, _ => some (StepRule.connectiveSimp, right)
        | _, Term.bool true => some (StepRule.connectiveSimp, Term.bool true)
        | _, Term.bool false => some (StepRule.connectiveSimp, Term.notE left)
        | Term.quote leftFormula, Term.quote rightFormula =>
            some (StepRule.foolQuote, Term.quote (Formula.imp leftFormula rightFormula))
        | _, _ =>
            if SyntaxEq.termEq left right then
              some (StepRule.connectiveSimp, Term.bool true)
            else
              none
      else
        none
  | Term.iffE left right =>
      if config.fool then
        match left, right with
        | Term.bool true, _ => some (StepRule.connectiveSimp, right)
        | _, Term.bool true => some (StepRule.connectiveSimp, left)
        | Term.bool false, _ => some (StepRule.connectiveSimp, Term.notE right)
        | _, Term.bool false => some (StepRule.connectiveSimp, Term.notE left)
        | Term.quote leftFormula, Term.quote rightFormula =>
            some (StepRule.foolQuote, Term.quote (Formula.iffE leftFormula rightFormula))
        | _, _ =>
            if SyntaxEq.termEq left right then
              some (StepRule.connectiveSimp, Term.bool true)
            else
              none
      else
        none
  | Term.quote formula =>
      if config.fool then
        match formula with
        | Formula.trueE => some (StepRule.foolQuote, Term.bool true)
        | Formula.falseE => some (StepRule.foolQuote, Term.bool false)
        | _ => none
      else
        none
  | Term.lam domain _ body =>
      if config.eta then
        match Eta.contract? domain body with
        | some contracted => some (StepRule.eta, contracted)
        | none => none
      else
        none
  | Term.ite sort condition thenTerm elseTerm =>
      match condition with
      | Formula.trueE => some (StepRule.boolIte, thenTerm)
      | Formula.falseE => some (StepRule.boolIte, elseTerm)
      | _ =>
          if SyntaxEq.termEq thenTerm elseTerm then
            some (StepRule.boolIte, thenTerm)
          else if config.fool then
            match sort, thenTerm, elseTerm with
            | CoreSort.bool, Term.bool true, Term.bool false =>
                some (StepRule.boolIte, Term.quote condition)
            | CoreSort.bool, Term.bool false, Term.bool true =>
                some (StepRule.boolIte, Term.quote (Formula.neg condition))
            | CoreSort.bool, Term.bool true, _ =>
                some (StepRule.boolIte, Term.orE (Term.quote condition) elseTerm)
            | CoreSort.bool, Term.bool false, _ =>
                some
                  ( StepRule.boolIte,
                    Term.andE (Term.quote (Formula.neg condition)) elseTerm )
            | CoreSort.bool, _, Term.bool true =>
                some (StepRule.boolIte, Term.impE (Term.quote condition) thenTerm)
            | CoreSort.bool, _, Term.bool false =>
                some (StepRule.boolIte, Term.andE (Term.quote condition) thenTerm)
            | _, _, _ => none
          else
            none
  | _ => none

/-- 只检查公式根部的一步归约，不递归进入子式。 -/
def rewriteRootFormula? (config : Config) : Formula → Option (StepRule × Formula)
  | Formula.equal sort left right =>
      if config.connectiveSimp && SyntaxEq.termEq left right then
        some (StepRule.equalityRefl, Formula.trueE)
      else
        match sort with
        | CoreSort.arrow domain codomain =>
            if config.extensionality then
              let shiftedLeft := Term.shift 1 left
              let shiftedRight := Term.shift 1 right
              let binder := Term.bvar domain 0
              some
                ( StepRule.functionExtensionality,
                  Formula.forallE domain
                    (Formula.equal codomain
                      (Term.apply shiftedLeft binder)
                      (Term.apply shiftedRight binder)) )
            else
              none
        | CoreSort.bool =>
            if config.fool then
              match left, right with
              | Term.bool true, _ => some (StepRule.boolEquality, Formula.boolTerm right)
              | _, Term.bool true => some (StepRule.boolEquality, Formula.boolTerm left)
              | Term.bool false, _ =>
                  some (StepRule.boolEquality, Formula.neg (Formula.boolTerm right))
              | _, Term.bool false =>
                  some (StepRule.boolEquality, Formula.neg (Formula.boolTerm left))
              | Term.quote leftFormula, Term.quote rightFormula =>
                  some (StepRule.boolEquality, Formula.iffE leftFormula rightFormula)
              | _, _ =>
                  some
                    ( StepRule.boolEquality,
                      Formula.iffE (Formula.boolTerm left) (Formula.boolTerm right) )
            else
              none
        | _ => none
  | Formula.boolTerm term =>
      if config.fool then
        match term with
        | Term.bool true => some (StepRule.foolBoolTerm, Formula.trueE)
        | Term.bool false => some (StepRule.foolBoolTerm, Formula.falseE)
        | Term.notE body => some (StepRule.foolBoolTerm, Formula.neg (Formula.boolTerm body))
        | Term.andE left right =>
            some
              ( StepRule.foolBoolTerm,
                Formula.conj (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.orE left right =>
            some
              ( StepRule.foolBoolTerm,
                Formula.disj (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.impE left right =>
            some
              ( StepRule.foolBoolTerm,
                Formula.imp (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.iffE left right =>
            some
              ( StepRule.foolBoolTerm,
                Formula.iffE (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.quote formula => some (StepRule.foolBoolTerm, formula)
        | Term.ite CoreSort.bool condition thenTerm elseTerm =>
            some
              ( StepRule.boolIte,
                Formula.disj
                  (Formula.conj condition (Formula.boolTerm thenTerm))
                  (Formula.conj (Formula.neg condition) (Formula.boolTerm elseTerm)) )
        | _ => none
      else
        none
  | Formula.neg body =>
      if config.connectiveSimp then
        match body with
        | Formula.trueE => some (StepRule.connectiveSimp, Formula.falseE)
        | Formula.falseE => some (StepRule.connectiveSimp, Formula.trueE)
        | Formula.neg inner => some (StepRule.connectiveSimp, inner)
        | _ => none
      else
        none
  | Formula.imp left right =>
      if config.connectiveSimp then
        match left, right with
        | Formula.falseE, _ => some (StepRule.connectiveSimp, Formula.trueE)
        | Formula.trueE, _ => some (StepRule.connectiveSimp, right)
        | _, Formula.trueE => some (StepRule.connectiveSimp, Formula.trueE)
        | _, Formula.falseE => some (StepRule.connectiveSimp, Formula.neg left)
        | _, _ =>
            if SyntaxEq.formulaEq left right then
              some (StepRule.connectiveSimp, Formula.trueE)
            else
              none
      else
        none
  | Formula.conj left right =>
      if config.connectiveSimp then
        match left, right with
        | Formula.falseE, _ => some (StepRule.connectiveSimp, Formula.falseE)
        | _, Formula.falseE => some (StepRule.connectiveSimp, Formula.falseE)
        | Formula.trueE, _ => some (StepRule.connectiveSimp, right)
        | _, Formula.trueE => some (StepRule.connectiveSimp, left)
        | _, _ =>
            if SyntaxEq.formulaEq left right then
              some (StepRule.connectiveSimp, left)
            else
              none
      else
        none
  | Formula.disj left right =>
      if config.connectiveSimp then
        match left, right with
        | Formula.trueE, _ => some (StepRule.connectiveSimp, Formula.trueE)
        | _, Formula.trueE => some (StepRule.connectiveSimp, Formula.trueE)
        | Formula.falseE, _ => some (StepRule.connectiveSimp, right)
        | _, Formula.falseE => some (StepRule.connectiveSimp, left)
        | _, _ =>
            if SyntaxEq.formulaEq left right then
              some (StepRule.connectiveSimp, left)
            else
              none
      else
        none
  | Formula.iffE left right =>
      if config.connectiveSimp then
        match left, right with
        | Formula.trueE, _ => some (StepRule.connectiveSimp, right)
        | _, Formula.trueE => some (StepRule.connectiveSimp, left)
        | Formula.falseE, _ => some (StepRule.connectiveSimp, Formula.neg right)
        | _, Formula.falseE => some (StepRule.connectiveSimp, Formula.neg left)
        | _, _ =>
            if SyntaxEq.formulaEq left right then
              some (StepRule.connectiveSimp, Formula.trueE)
            else
              none
      else
        none
  | Formula.forallE _ body =>
      if config.quantifierSimp then
        match body with
        | Formula.trueE => some (StepRule.quantifierSimp, Formula.trueE)
        | _ => none
      else
        none
  | Formula.existsE _ body =>
      if config.quantifierSimp then
        match body with
        | Formula.falseE => some (StepRule.quantifierSimp, Formula.falseE)
        | _ => none
      else
        none
  | _ => none

/-- trace replay 的表达式载体：normalizer 可以从项或公式入口开始。 -/
inductive TraceExpr where
  | term (term : Term)
  | formula (formula : Formula)
  deriving Repr, Lean.ToExpr

namespace TraceExpr

/-- trace 表达式的透明结构相等。 -/
def eq : TraceExpr → TraceExpr → Bool
  | TraceExpr.term left, TraceExpr.term right => SyntaxEq.termEq left right
  | TraceExpr.formula left, TraceExpr.formula right => SyntaxEq.formulaEq left right
  | _, _ => false

/-- trace 表达式大小，用来给单步 replay 分配更宽裕的燃料。 -/
def size : TraceExpr → Nat
  | TraceExpr.term t => t.size
  | TraceExpr.formula p => p.size

/-- trace 表达式的 sort / well-scoped 检查。 -/
def check? : TraceExpr → Bool
  | TraceExpr.term t => t.wellScoped? && t.inferSort?.isSome
  | TraceExpr.formula p => p.check?

/-- 使用当前 normalizer 复算表达式的 normal form。 -/
def normalize (config : Config) : TraceExpr → TraceExpr
  | TraceExpr.term t => TraceExpr.term (normalizeTerm t (config := config))
  | TraceExpr.formula p => TraceExpr.formula (normalizeFormula p (config := config))

end TraceExpr

mutual
  /-- 在公式中执行一次子式优先的可审计重写。 -/
  def rewriteOnceFormula? (config : Config) : Formula → Option (StepRule × Formula)
    | Formula.trueE => none
    | Formula.falseE => none
    | Formula.atom predicate args =>
        match rewriteOnceTermList? config args with
        | some (rule, args') => some (rule, Formula.atom predicate args')
        | none => rewriteRootFormula? config (Formula.atom predicate args)
    | Formula.equal sort left right =>
        match rewriteOnceTerm? config left with
        | some (rule, left') => some (rule, Formula.equal sort left' right)
        | none =>
            match rewriteOnceTerm? config right with
            | some (rule, right') => some (rule, Formula.equal sort left right')
            | none => rewriteRootFormula? config (Formula.equal sort left right)
    | Formula.boolTerm term =>
        match rewriteOnceTerm? config term with
        | some (rule, term') => some (rule, Formula.boolTerm term')
        | none => rewriteRootFormula? config (Formula.boolTerm term)
    | Formula.neg body =>
        match rewriteOnceFormula? config body with
        | some (rule, body') => some (rule, Formula.neg body')
        | none => rewriteRootFormula? config (Formula.neg body)
    | Formula.imp left right =>
        match rewriteOnceFormula? config left with
        | some (rule, left') => some (rule, Formula.imp left' right)
        | none =>
            match rewriteOnceFormula? config right with
            | some (rule, right') => some (rule, Formula.imp left right')
            | none => rewriteRootFormula? config (Formula.imp left right)
    | Formula.conj left right =>
        match rewriteOnceFormula? config left with
        | some (rule, left') => some (rule, Formula.conj left' right)
        | none =>
            match rewriteOnceFormula? config right with
            | some (rule, right') => some (rule, Formula.conj left right')
            | none => rewriteRootFormula? config (Formula.conj left right)
    | Formula.disj left right =>
        match rewriteOnceFormula? config left with
        | some (rule, left') => some (rule, Formula.disj left' right)
        | none =>
            match rewriteOnceFormula? config right with
            | some (rule, right') => some (rule, Formula.disj left right')
            | none => rewriteRootFormula? config (Formula.disj left right)
    | Formula.iffE left right =>
        match rewriteOnceFormula? config left with
        | some (rule, left') => some (rule, Formula.iffE left' right)
        | none =>
            match rewriteOnceFormula? config right with
            | some (rule, right') => some (rule, Formula.iffE left right')
            | none => rewriteRootFormula? config (Formula.iffE left right)
    | Formula.forallE sort body =>
        match rewriteOnceFormula? config body with
        | some (rule, body') => some (rule, Formula.forallE sort body')
        | none => rewriteRootFormula? config (Formula.forallE sort body)
    | Formula.existsE sort body =>
        match rewriteOnceFormula? config body with
        | some (rule, body') => some (rule, Formula.existsE sort body')
        | none => rewriteRootFormula? config (Formula.existsE sort body)

  /-- 在项中执行一次子式优先的可审计重写。 -/
  def rewriteOnceTerm? (config : Config) : Term → Option (StepRule × Term)
    | Term.bvar .. => none
    | Term.fvar .. => none
    | Term.app symbol args =>
        match rewriteOnceTermList? config args with
        | some (rule, args') => some (rule, Term.app symbol args')
        | none => rewriteRootTerm? config (Term.app symbol args)
    | Term.apply fn arg =>
        match rewriteOnceTerm? config fn with
        | some (rule, fn') => some (rule, Term.apply fn' arg)
        | none =>
            match rewriteOnceTerm? config arg with
            | some (rule, arg') => some (rule, Term.apply fn arg')
            | none => rewriteRootTerm? config (Term.apply fn arg)
    | Term.bool .. => none
    | Term.notE body =>
        match rewriteOnceTerm? config body with
        | some (rule, body') => some (rule, Term.notE body')
        | none => rewriteRootTerm? config (Term.notE body)
    | Term.andE left right =>
        match rewriteOnceTerm? config left with
        | some (rule, left') => some (rule, Term.andE left' right)
        | none =>
            match rewriteOnceTerm? config right with
            | some (rule, right') => some (rule, Term.andE left right')
            | none => rewriteRootTerm? config (Term.andE left right)
    | Term.orE left right =>
        match rewriteOnceTerm? config left with
        | some (rule, left') => some (rule, Term.orE left' right)
        | none =>
            match rewriteOnceTerm? config right with
            | some (rule, right') => some (rule, Term.orE left right')
            | none => rewriteRootTerm? config (Term.orE left right)
    | Term.impE left right =>
        match rewriteOnceTerm? config left with
        | some (rule, left') => some (rule, Term.impE left' right)
        | none =>
            match rewriteOnceTerm? config right with
            | some (rule, right') => some (rule, Term.impE left right')
            | none => rewriteRootTerm? config (Term.impE left right)
    | Term.iffE left right =>
        match rewriteOnceTerm? config left with
        | some (rule, left') => some (rule, Term.iffE left' right)
        | none =>
            match rewriteOnceTerm? config right with
            | some (rule, right') => some (rule, Term.iffE left right')
            | none => rewriteRootTerm? config (Term.iffE left right)
    | Term.quote formula =>
        match rewriteOnceFormula? config formula with
        | some (rule, formula') => some (rule, Term.quote formula')
        | none => rewriteRootTerm? config (Term.quote formula)
    | Term.lam domain codomain body =>
        match rewriteOnceTerm? config body with
        | some (rule, body') => some (rule, Term.lam domain codomain body')
        | none => rewriteRootTerm? config (Term.lam domain codomain body)
    | Term.ite sort condition thenTerm elseTerm =>
        match rewriteOnceFormula? config condition with
        | some (rule, condition') => some (rule, Term.ite sort condition' thenTerm elseTerm)
        | none =>
            match rewriteOnceTerm? config thenTerm with
            | some (rule, thenTerm') => some (rule, Term.ite sort condition thenTerm' elseTerm)
            | none =>
                match rewriteOnceTerm? config elseTerm with
                | some (rule, elseTerm') =>
                    some (rule, Term.ite sort condition thenTerm elseTerm')
                | none =>
                    rewriteRootTerm? config
                      (Term.ite sort condition thenTerm elseTerm)

  /-- 在项列表中执行一次从左到右的可审计重写。 -/
  def rewriteOnceTermList? (config : Config) :
      List Term → Option (StepRule × List Term)
    | [] => none
    | term :: rest =>
        match rewriteOnceTerm? config term with
        | some (rule, term') => some (rule, term' :: rest)
        | none =>
            match rewriteOnceTermList? config rest with
            | some (rule, rest') => some (rule, term :: rest')
            | none => none
end

namespace TraceExpr

/-- 在 trace 表达式上执行一次可审计重写。 -/
def rewriteOnce? (config : Config) : TraceExpr → Option (StepRule × TraceExpr)
  | TraceExpr.term t => do
      let (rule, t') ← rewriteOnceTerm? config t
      some (rule, TraceExpr.term t')
  | TraceExpr.formula p => do
      let (rule, p') ← rewriteOnceFormula? config p
      some (rule, TraceExpr.formula p')

end TraceExpr

/-- normalization trace 的一步：`before` 到 `after` 必须能由 `rule` 单步复算。 -/
structure Step where
  rule : StepRule
  before : TraceExpr
  after : TraceExpr
  deriving Repr, Lean.ToExpr

namespace Step

/-- 检查一步 rewrite 是否正是当前 checker 可复算的下一步。 -/
def check (config : Config) (step : Step) : Bool :=
  step.before.check? &&
    step.after.check? &&
      match TraceExpr.rewriteOnce? config step.before with
      | some (rule, after) => rule == step.rule && TraceExpr.eq after step.after
      | none => false

end Step

/-- 可审计 normalization trace。 -/
structure Trace where
  source : TraceExpr
  target : TraceExpr
  steps : Array Step
  deriving Repr, Lean.ToExpr

namespace Trace

/-- 单步 trace 的 replay 循环。 -/
def replay? (config : Config) (current : TraceExpr) : List Step → Option TraceExpr
  | [] => some current
  | step :: rest =>
      if TraceExpr.eq current step.before && step.check config then
        replay? config step.after rest
      else
        none

/-- `Trace.check` 同时检查 replay endpoint 与当前 normalizer 的复算结果。 -/
def check (config : Config) (trace : Trace) : Bool :=
  trace.source.check? &&
    trace.target.check? &&
      match replay? config trace.source trace.steps.toList with
      | some target =>
          TraceExpr.eq target trace.target &&
            TraceExpr.eq target (TraceExpr.normalize config trace.source)
      | none => false

/-- trace 中是否出现过指定规则；用于证书审计与 smoke tests。 -/
def containsRule (rule : StepRule) (trace : Trace) : Bool :=
  trace.steps.any (fun step => step.rule == rule)

/-- 规则标签是否已经在数组中。 -/
def containsCertificateTag (tags : Array Certificate.RuleTag)
    (tag : Certificate.RuleTag) : Bool :=
  tags.any (fun existing => existing == tag)

/-- 向规则标签数组加入一个不重复标签。 -/
def pushCertificateTag (tags : Array Certificate.RuleTag)
    (tag : Certificate.RuleTag) : Array Certificate.RuleTag :=
  if containsCertificateTag tags tag then tags else tags.push tag

/-- normalization 单步规则对应的公共证书规则族。 -/
def certificateTagOfRule : StepRule → Certificate.RuleTag
  | StepRule.beta => Certificate.RuleTag.betaEta
  | StepRule.eta => Certificate.RuleTag.betaEta
  | StepRule.foolQuote => Certificate.RuleTag.foolClausification
  | StepRule.foolBoolTerm => Certificate.RuleTag.foolClausification
  | StepRule.boolEquality => Certificate.RuleTag.foolClausification
  | StepRule.boolIte => Certificate.RuleTag.foolClausification
  | StepRule.functionExtensionality => Certificate.RuleTag.lambdaExtensionality
  | StepRule.connectiveSimp => Certificate.RuleTag.coreNormalFormTrace
  | StepRule.quantifierSimp => Certificate.RuleTag.coreNormalFormTrace
  | StepRule.equalityRefl => Certificate.RuleTag.coreNormalFormTrace

/-- trace 中实际出现过的公共证书规则标签。 -/
def certificateTags (trace : Trace) : Array Certificate.RuleTag :=
  trace.steps.foldl
    (fun tags step => pushCertificateTag tags (certificateTagOfRule step.rule))
    #[Certificate.RuleTag.coreNormalFormTrace]

/-- trace 的公共证书摘要。 -/
def certificateStats (config : Config) (trace : Trace) : Certificate.Stats :=
  {
    steps := trace.steps.size
    generated := trace.source.size
    retained := trace.target.size
    verified := trace.steps.size
    fuel := config.fuel * (trace.source.size + 1) + 1
  }

/-- trace 构造时使用的燃料：比 normalizer 的结构燃料更贴近“单步数量”。 -/
def fuel (config : Config) (source : TraceExpr) : Nat :=
  config.fuel * (source.size + 1) + 1

/-- 从表达式反复抽取可审计单步，直到抵达 normal form 或耗尽 trace fuel。 -/
partial def buildLoop (config : Config) :
    Nat → TraceExpr → Array Step → TraceExpr × Array Step
  | 0, current, steps => (current, steps)
  | fuel + 1, current, steps =>
      match TraceExpr.rewriteOnce? config current with
      | some (rule, next) =>
          buildLoop config fuel next (steps.push { rule := rule, before := current, after := next })
      | none => (current, steps)

/-- 从任意 trace 表达式构造 normalization trace。 -/
def build (source : TraceExpr) (config : Config := {}) : Trace :=
  let (target, steps) := buildLoop config (fuel config source) source #[]
  { source := source, target := target, steps := steps }

/-- 从项入口构造 trace。 -/
def ofTerm (source : Term) (config : Config := {}) : Trace :=
  build (TraceExpr.term source) (config := config)

/-- 从公式入口构造 trace。 -/
def ofFormula (source : Formula) (config : Config := {}) : Trace :=
  build (TraceExpr.formula source) (config := config)

/-- 已进入公共证书层的 normal form trace payload。 -/
structure SoundnessPayload where
  config : Config
  trace : Trace
  deriving Repr, Lean.ToExpr

namespace SoundnessPayload

/-- trace payload 的可计算 checker。 -/
def check (payload : SoundnessPayload) : Bool :=
  Trace.check payload.config payload.trace

/-- 从 trace 构造 soundness bridge payload。 -/
def ofTrace (config : Config) (trace : Trace) : SoundnessPayload :=
  { config := config, trace := trace }

/-- 计算式构造 checked trace payload。 -/
def mk? (config : Config) (trace : Trace) :
    Option (Certificate.Checked SoundnessPayload SoundnessPayload.check) :=
  Certificate.Checked.mk? (check := SoundnessPayload.check) (ofTrace config trace)

/-- checked trace payload 的公共证书节点。 -/
def toCoreNode (payload : SoundnessPayload) (id : Certificate.NodeId := 0)
    (dependencies : Array Certificate.NodeId := #[])
    (closureKind? : Option Certificate.ClosureKind := some Certificate.ClosureKind.frontendNormalization) :
    Certificate.Node :=
  {
    id := id
    backend := Certificate.Backend.coreNormalForm
    phase := Certificate.Phase.frontendNormalization
    label := "checked core normal form trace"
    ruleTags := payload.trace.certificateTags
    closureKind? := closureKind?
    stats := Trace.certificateStats payload.config payload.trace
    dependencies := dependencies
  }

end SoundnessPayload

end Trace

/-- 可复算、可 replay 的项 normal form payload。 -/
structure TermPayload where
  config : Config
  source : Term
  normal : Term
  trace : Trace
  sourceSize : Nat
  normalSize : Nat
  deriving Repr, Lean.ToExpr

namespace TermPayload

/-- 从源项生成 payload。 -/
def build (source : Term) (config : Config := {}) : TermPayload :=
  let normal := normalizeTerm source (config := config)
  let trace := Trace.ofTerm source (config := config)
  {
    config := config
    source := source
    normal := normal
    trace := trace
    sourceSize := source.size
    normalSize := normal.size
  }

/-- 检查 payload 是否由当前 normalizer 与 trace checker 同时复算得到。 -/
def check (payload : TermPayload) : Bool :=
  payload.source.wellScoped? &&
    (match payload.source.inferSort?, payload.normal.inferSort? with
    | some sourceSort, some normalSort => sourceSort == normalSort
    | _, _ => false) &&
      Trace.check payload.config payload.trace &&
        TraceExpr.eq payload.trace.source (TraceExpr.term payload.source) &&
          TraceExpr.eq payload.trace.target (TraceExpr.term payload.normal) &&
            SyntaxEq.termEq payload.normal (normalizeTerm payload.source (config := payload.config)) &&
              payload.sourceSize == payload.source.size &&
                payload.normalSize == payload.normal.size

end TermPayload

/-- 可复算、可 replay 的公式 normal form payload。 -/
structure FormulaPayload where
  config : Config
  source : Formula
  normal : Formula
  trace : Trace
  sourceSize : Nat
  normalSize : Nat
  deriving Repr, Lean.ToExpr

namespace FormulaPayload

/-- 从源公式生成 payload。 -/
def build (source : Formula) (config : Config := {}) : FormulaPayload :=
  let normal := normalizeFormula source (config := config)
  let trace := Trace.ofFormula source (config := config)
  {
    config := config
    source := source
    normal := normal
    trace := trace
    sourceSize := source.size
    normalSize := normal.size
  }

/-- 检查 payload 是否由当前 normalizer 与 trace checker 同时复算得到。 -/
def check (payload : FormulaPayload) : Bool :=
  payload.source.check? &&
    payload.normal.check? &&
      Trace.check payload.config payload.trace &&
        TraceExpr.eq payload.trace.source (TraceExpr.formula payload.source) &&
          TraceExpr.eq payload.trace.target (TraceExpr.formula payload.normal) &&
            SyntaxEq.formulaEq payload.normal
              (normalizeFormula payload.source (config := payload.config)) &&
              payload.sourceSize == payload.source.size &&
                payload.normalSize == payload.normal.size

end FormulaPayload

namespace Search

/-- 搜索层 literal 投影到核心公式后归一化。 -/
def normalizeLiteralFormula (literal : CoreSyntax.Search.Literal) (config : Config := {}) :
    Formula :=
  normalizeFormula literal.toCoreFormula (config := config)

/-- 搜索层 clause 投影到核心析取公式后归一化。 -/
def normalizeClauseFormula (clause : CoreSyntax.Search.Clause) (config : Config := {}) :
    Formula :=
  normalizeFormula clause.toCoreFormula (config := config)

/-- 可复算的搜索层 clause normal form payload。 -/
structure ClausePayload where
  config : Config
  source : CoreSyntax.Search.Clause
  normal : Formula
  deriving Repr, Lean.ToExpr

namespace ClausePayload

/-- 从搜索层 clause 生成核心 normal form payload。 -/
def build (source : CoreSyntax.Search.Clause) (config : Config := {}) : ClausePayload :=
  {
    config := config
    source := source
    normal := normalizeClauseFormula source (config := config)
  }

/-- 检查 clause payload 是否由当前 normalizer 复算得到。 -/
def check (payload : ClausePayload) : Bool :=
  SyntaxEq.formulaEq payload.normal
    (normalizeClauseFormula payload.source (config := payload.config))

end ClausePayload

end Search

/-!
## Core NNF 与前束/CNF 视图

这一层是后续 FOOL/lambda 叠加演算真正应该消费的 normal form。它不再复用旧 MF1
`Formula` 上的兼容 NNF，而是直接在 `CoreSyntax.Formula` 上给出可复算数据。
-/

/-- NNF 中保留的原子。`boolTerm` 表示尚未被 FOOL 归约消掉的布尔项原子。 -/
inductive Atom where
  | predicate (predicate : PredicateSymbol) (args : List Term)
  | equal (sort : CoreSort) (left right : Term)
  | boolTerm (term : Term)
  deriving Repr, Inhabited, Lean.ToExpr

namespace Atom

/-- 原子公式的节点数。 -/
def size : Atom → Nat
  | Atom.predicate _ args => args.foldl (fun acc term => acc + term.size) 1
  | Atom.equal _ left right => left.size + right.size + 1
  | Atom.boolTerm term => term.size + 1

/-- 原子公式重新嵌回核心公式。 -/
def toFormula : Atom → Formula
  | Atom.predicate predSym args => Formula.atom predSym args
  | Atom.equal sort left right => Formula.equal sort left right
  | Atom.boolTerm term => Formula.boolTerm term

end Atom

/-- NNF 字面量；`positive = false` 表示否定原子。 -/
structure Literal where
  positive : Bool
  atom : Atom
  deriving Repr, Inhabited, Lean.ToExpr

namespace Literal

/-- 字面量节点数。 -/
def size (literal : Literal) : Nat :=
  literal.atom.size + 1

/-- 字面量重新嵌回核心公式。 -/
def toFormula (literal : Literal) : Formula :=
  if literal.positive then literal.atom.toFormula else Formula.neg literal.atom.toFormula

/-- 翻转字面量极性。 -/
def negate (literal : Literal) : Literal :=
  { literal with positive := !literal.positive }

end Literal

/-- Core NNF；允许常量，便于 CNF 阶段精确表达真/假矩阵。 -/
inductive Nnf where
  | trueE
  | falseE
  | lit (literal : Literal)
  | conj (left right : Nnf)
  | disj (left right : Nnf)
  | forallE (sort : CoreSort) (body : Nnf)
  | existsE (sort : CoreSort) (body : Nnf)
  deriving Repr, Inhabited, Lean.ToExpr

namespace Nnf

/-- NNF 节点数。 -/
partial def size : Nnf → Nat
  | trueE => 1
  | falseE => 1
  | lit literal => literal.size + 1
  | conj left right => left.size + right.size + 1
  | disj left right => left.size + right.size + 1
  | forallE _ body => body.size + 1
  | existsE _ body => body.size + 1

/-- NNF 中字面量数量。 -/
partial def literalCount : Nnf → Nat
  | trueE => 0
  | falseE => 0
  | lit _ => 1
  | conj left right => left.literalCount + right.literalCount
  | disj left right => left.literalCount + right.literalCount
  | forallE _ body => body.literalCount
  | existsE _ body => body.literalCount

/-- NNF 中量词数量。 -/
def quantifierCount : Nnf → Nat
  | trueE => 0
  | falseE => 0
  | lit _ => 0
  | conj left right => left.quantifierCount + right.quantifierCount
  | disj left right => left.quantifierCount + right.quantifierCount
  | forallE _ body => body.quantifierCount + 1
  | existsE _ body => body.quantifierCount + 1

/-- NNF 是否已经没有量词。 -/
def quantifierFree (nnf : Nnf) : Bool :=
  nnf.quantifierCount == 0

/-- NNF 重新嵌回核心公式。 -/
def toFormula : Nnf → Formula
  | trueE => Formula.trueE
  | falseE => Formula.falseE
  | lit literal => literal.toFormula
  | conj left right => Formula.conj left.toFormula right.toFormula
  | disj left right => Formula.disj left.toFormula right.toFormula
  | forallE sort body => Formula.forallE sort body.toFormula
  | existsE sort body => Formula.existsE sort body.toFormula

/-- 反转 NNF 极性。 -/
partial def negate : Nnf → Nnf
  | trueE => falseE
  | falseE => trueE
  | lit literal => lit literal.negate
  | conj left right => disj left.negate right.negate
  | disj left right => conj left.negate right.negate
  | forallE sort body => existsE sort body.negate
  | existsE sort body => forallE sort body.negate

end Nnf

namespace SyntaxEq

mutual
  /-- Core NNF 原子的透明结构相等。 -/
  def atomEq : Atom → Atom → Bool
    | Atom.predicate leftPredicate leftArgs, Atom.predicate rightPredicate rightArgs =>
        decide (leftPredicate = rightPredicate) && termListEq leftArgs rightArgs
    | Atom.equal leftSort leftLeft leftRight, Atom.equal rightSort rightLeft rightRight =>
        decide (leftSort = rightSort) && termEq leftLeft rightLeft && termEq leftRight rightRight
    | Atom.boolTerm leftTerm, Atom.boolTerm rightTerm =>
        termEq leftTerm rightTerm
    | _, _ => false

  /-- Core NNF 字面量的透明结构相等。 -/
  def literalEq (left right : Literal) : Bool :=
    decide (left.positive = right.positive) && atomEq left.atom right.atom

  /-- Core NNF 的透明结构相等。 -/
  def nnfEq : Nnf → Nnf → Bool
    | Nnf.trueE, Nnf.trueE => true
    | Nnf.falseE, Nnf.falseE => true
    | Nnf.lit left, Nnf.lit right => literalEq left right
    | Nnf.conj leftA leftB, Nnf.conj rightA rightB
    | Nnf.disj leftA leftB, Nnf.disj rightA rightB =>
        nnfEq leftA rightA && nnfEq leftB rightB
    | Nnf.forallE leftSort leftBody, Nnf.forallE rightSort rightBody
    | Nnf.existsE leftSort leftBody, Nnf.existsE rightSort rightBody =>
        decide (leftSort = rightSort) && nnfEq leftBody rightBody
    | _, _ => false

  /-- Core NNF 字面量列表的透明结构相等。 -/
  def literalListEq : List Literal → List Literal → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        literalEq left right && literalListEq leftRest rightRest
    | _, _ => false
end

end SyntaxEq

mutual
  /-- 项里是否出现指定 De Bruijn 深度的绑定变量。 -/
  def Term.occursBVarAt (depth : Nat) : Term → Bool
    | Term.bvar _ index => index == depth
    | Term.fvar .. => false
    | Term.app _ args => Term.occursBVarListAt depth args
    | Term.apply fn arg => Term.occursBVarAt depth fn || Term.occursBVarAt depth arg
    | Term.bool _ => false
    | Term.notE body => Term.occursBVarAt depth body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Term.quote formula => Formula.occursBVarAt depth formula
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.occursBVarAt depth condition ||
          Term.occursBVarAt depth thenTerm ||
            Term.occursBVarAt depth elseTerm

  /-- 公式里是否出现指定 De Bruijn 深度的绑定变量。 -/
  def Formula.occursBVarAt (depth : Nat) : Formula → Bool
    | Formula.trueE => false
    | Formula.falseE => false
    | Formula.atom _ args => Term.occursBVarListAt depth args
    | Formula.equal _ left right =>
        Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Formula.boolTerm term => Term.occursBVarAt depth term
    | Formula.neg body => Formula.occursBVarAt depth body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Formula.occursBVarAt depth left || Formula.occursBVarAt depth right
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Formula.occursBVarAt (depth + 1) body

  /-- 项列表里是否出现指定 De Bruijn 深度的绑定变量。 -/
  def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end

mutual
  /--
  删除深度 `cutoff` 的绑定器后，下移更外层的 De Bruijn 索引。

  调用方应先通过独立性检查确认 `cutoff` 本身不会真实出现；若出现则保留原索引，便于
  checker 暴露错误形状，而不是静默改写成别的变量。
  -/
  def Term.lowerAbove (cutoff : Nat) : Term → Term
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
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.lowerAbove cutoff body)
    | Term.andE left right =>
        Term.andE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.orE left right =>
        Term.orE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.impE left right =>
        Term.impE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.iffE left right =>
        Term.iffE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.quote formula => Term.quote (Formula.lowerAbove cutoff formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.lowerAbove (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.lowerAbove cutoff condition)
          (Term.lowerAbove cutoff thenTerm) (Term.lowerAbove cutoff elseTerm)

  /-- 公式里的 De Bruijn 索引下移。 -/
  def Formula.lowerAbove (cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.lowerListAbove cutoff args)
    | Formula.equal sort left right =>
        Formula.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.lowerAbove cutoff term)
    | Formula.neg body => Formula.neg (Formula.lowerAbove cutoff body)
    | Formula.imp left right =>
        Formula.imp (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.conj left right =>
        Formula.conj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.disj left right =>
        Formula.disj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.iffE left right =>
        Formula.iffE (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.lowerAbove (cutoff + 1) body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.lowerAbove (cutoff + 1) body)

  /-- 项列表里的 De Bruijn 索引下移。 -/
  def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end

namespace Atom

/-- 原子中是否出现指定 De Bruijn 深度的绑定变量。 -/
def occursBVarAt (depth : Nat) : Atom → Bool
  | Atom.predicate _ args => Term.occursBVarListAt depth args
  | Atom.equal _ left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
  | Atom.boolTerm term => Term.occursBVarAt depth term

/-- 对原子执行 De Bruijn lift。 -/
def shiftAbove (amount cutoff : Nat) : Atom → Atom
  | Atom.predicate predSym args =>
      Atom.predicate predSym (Term.shiftListAbove amount cutoff args)
  | Atom.equal sort left right =>
      Atom.equal sort (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
  | Atom.boolTerm term => Atom.boolTerm (Term.shiftAbove amount cutoff term)

/-- 删除一个外层绑定器时对原子执行 De Bruijn 下移。 -/
def lowerAbove (cutoff : Nat) : Atom → Atom
  | Atom.predicate predSym args =>
      Atom.predicate predSym (Term.lowerListAbove cutoff args)
  | Atom.equal sort left right =>
      Atom.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
  | Atom.boolTerm term => Atom.boolTerm (Term.lowerAbove cutoff term)

end Atom

namespace Literal

/-- 字面量中是否出现指定 De Bruijn 深度的绑定变量。 -/
def occursBVarAt (depth : Nat) (literal : Literal) : Bool :=
  literal.atom.occursBVarAt depth

/-- 对字面量执行 De Bruijn lift。 -/
def shiftAbove (amount cutoff : Nat) (literal : Literal) : Literal :=
  { literal with atom := literal.atom.shiftAbove amount cutoff }

/-- 删除一个外层绑定器时对字面量执行 De Bruijn 下移。 -/
def lowerAbove (cutoff : Nat) (literal : Literal) : Literal :=
  { literal with atom := literal.atom.lowerAbove cutoff }

end Literal

namespace Nnf

/-- NNF 中是否出现指定 De Bruijn 深度的绑定变量。 -/
def occursBVarAt (depth : Nat) : Nnf → Bool
  | trueE => false
  | falseE => false
  | lit literal => literal.occursBVarAt depth
  | conj left right => left.occursBVarAt depth || right.occursBVarAt depth
  | disj left right => left.occursBVarAt depth || right.occursBVarAt depth
  | forallE _ body => body.occursBVarAt (depth + 1)
  | existsE _ body => body.occursBVarAt (depth + 1)

/-- 当前最外层绑定器是否真实支配该 NNF。 -/
def usesCurrentBinder (nnf : Nnf) : Bool :=
  nnf.occursBVarAt 0

/-- 对 NNF 执行 De Bruijn lift。 -/
def shiftAbove (amount cutoff : Nat) : Nnf → Nnf
  | trueE => trueE
  | falseE => falseE
  | lit literal => lit (literal.shiftAbove amount cutoff)
  | conj left right => conj (left.shiftAbove amount cutoff) (right.shiftAbove amount cutoff)
  | disj left right => disj (left.shiftAbove amount cutoff) (right.shiftAbove amount cutoff)
  | forallE sort body => forallE sort (body.shiftAbove amount (cutoff + 1))
  | existsE sort body => existsE sort (body.shiftAbove amount (cutoff + 1))

/-- 对 NNF 中所有自由于当前上下文的 De Bruijn 索引执行 lift。 -/
def shift (amount : Nat) (nnf : Nnf) : Nnf :=
  nnf.shiftAbove amount 0

/-- 删除一个绑定器时对 NNF 执行 De Bruijn 下移。 -/
def lowerAbove (cutoff : Nat) : Nnf → Nnf
  | trueE => trueE
  | falseE => falseE
  | lit literal => lit (literal.lowerAbove cutoff)
  | conj left right => conj (left.lowerAbove cutoff) (right.lowerAbove cutoff)
  | disj left right => disj (left.lowerAbove cutoff) (right.lowerAbove cutoff)
  | forallE sort body => forallE sort (body.lowerAbove (cutoff + 1))
  | existsE sort body => existsE sort (body.lowerAbove (cutoff + 1))

/-- 删除当前最外层绑定器。调用方应先确认当前绑定器没有真实出现。 -/
def dropCurrentBinder (body : Nnf) : Nnf :=
  body.lowerAbove 0

end Nnf

/-- NNF 转换时的极性。 -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Polarity

/-- 翻转极性。 -/
def flip : Polarity → Polarity
  | positive => negative
  | negative => positive

/-- 在当前极性下构造字面量。 -/
def literal (polarity : Polarity) (atom : Atom) : Literal :=
  { positive := polarity == positive, atom := atom }

end Polarity

/-- 把已经过局部归一化的公式转成 NNF。该递归严格下降到公式子项。 -/
def toNnfWith : Polarity → Formula → Nnf
  | Polarity.positive, Formula.trueE => Nnf.trueE
  | Polarity.negative, Formula.trueE => Nnf.falseE
  | Polarity.positive, Formula.falseE => Nnf.falseE
  | Polarity.negative, Formula.falseE => Nnf.trueE
  | polarity, Formula.atom predicate args =>
      Nnf.lit (polarity.literal (Atom.predicate predicate args))
  | polarity, Formula.equal sort left right =>
      Nnf.lit (polarity.literal (Atom.equal sort left right))
  | polarity, Formula.boolTerm term =>
      Nnf.lit (polarity.literal (Atom.boolTerm term))
  | polarity, Formula.neg body =>
      toNnfWith polarity.flip body
  | Polarity.positive, Formula.imp left right =>
      Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.imp left right =>
      Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.conj left right =>
      Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.conj left right =>
      Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.disj left right =>
      Nnf.disj (toNnfWith Polarity.positive left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.disj left right =>
      Nnf.conj (toNnfWith Polarity.negative left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.iffE left right =>
      Nnf.conj
        (Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.positive right))
        (Nnf.disj (toNnfWith Polarity.negative right) (toNnfWith Polarity.positive left))
  | Polarity.negative, Formula.iffE left right =>
      Nnf.disj
        (Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.negative right))
        (Nnf.conj (toNnfWith Polarity.positive right) (toNnfWith Polarity.negative left))
  | Polarity.positive, Formula.forallE sort body =>
      Nnf.forallE sort (toNnfWith Polarity.positive body)
  | Polarity.negative, Formula.forallE sort body =>
      Nnf.existsE sort (toNnfWith Polarity.negative body)
  | Polarity.positive, Formula.existsE sort body =>
      Nnf.existsE sort (toNnfWith Polarity.positive body)
  | Polarity.negative, Formula.existsE sort body =>
      Nnf.forallE sort (toNnfWith Polarity.negative body)

/-- 先执行局部归一化，再把核心公式转成 NNF。 -/
def toNnf (formula : Formula) (config : Config := {}) : Nnf :=
  toNnfWith Polarity.positive (normalizeFormula formula (config := config))

/-- 前束量词条目。列表按外到内排列。 -/
inductive Quantifier where
  | forallE (sort : CoreSort)
  | existsE (sort : CoreSort)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Quantifier

/-- 量词绑定的 sort。 -/
def sort : Quantifier → CoreSort
  | forallE sort => sort
  | existsE sort => sort

/-- 用一个量词包住 NNF。 -/
def wrap (quantifier : Quantifier) (body : Nnf) : Nnf :=
  match quantifier with
  | forallE sort => Nnf.forallE sort body
  | existsE sort => Nnf.existsE sort body

end Quantifier

abbrev Prefix := List Quantifier

namespace Prefix

/-- 前束对矩阵提供的本地绑定上下文；上下文按 De Bruijn 索引从近到远排列。 -/
def boundSorts (qs : Prefix) : List CoreSort :=
  qs.foldl (fun bound quantifier => quantifier.sort :: bound) []

/-- 用前束量词列表包住矩阵。 -/
def wrap : Prefix → Nnf → Nnf
  | [], matrix => matrix
  | quantifier :: rest, matrix => quantifier.wrap (wrap rest matrix)

/-- 前束列表的透明结构相等。 -/
def eq : Prefix → Prefix → Bool
  | [], [] => true
  | Quantifier.forallE left :: leftRest, Quantifier.forallE right :: rightRest =>
      left == right && eq leftRest rightRest
  | Quantifier.existsE left :: leftRest, Quantifier.existsE right :: rightRest =>
      left == right && eq leftRest rightRest
  | _, _ => false

end Prefix

/-- 前束 normal form 视图：`prefix.wrap matrix` 等价于源 NNF 的前束化形状。 -/
structure PrenexView where
  quantifiers : Prefix
  matrix : Nnf
  deriving Repr, Inhabited, Lean.ToExpr

namespace PrenexView

/-- 前束视图重新嵌回 NNF。 -/
def toNnf (view : PrenexView) : Nnf :=
  view.quantifiers.wrap view.matrix

/-- 前束视图重新嵌回核心公式。 -/
def toFormula (view : PrenexView) : Formula :=
  view.toNnf.toFormula

/-- 前束视图的透明结构相等。 -/
def eq (left right : PrenexView) : Bool :=
  Prefix.eq left.quantifiers right.quantifiers && SyntaxEq.nnfEq left.matrix right.matrix

/--
合并二元联结词两侧的前束视图。

最终前束顺序固定为“左前束在外，右前束在内”。矩阵侧的 lift 是局部无名索引下
最容易出错的部分：左矩阵进入右前束时整体上移；右矩阵进入左前束时只上移原外层上下文。
-/
def combine (mk : Nnf → Nnf → Nnf) (left right : PrenexView) : PrenexView :=
  let leftDepth := left.quantifiers.length
  let rightDepth := right.quantifiers.length
  {
    quantifiers := left.quantifiers ++ right.quantifiers
    matrix :=
      mk (left.matrix.shift rightDepth) (right.matrix.shiftAbove leftDepth rightDepth)
  }

/-- 把 NNF 拉成前束视图。 -/
partial def ofNnf : Nnf → PrenexView
  | Nnf.trueE => { quantifiers := [], matrix := Nnf.trueE }
  | Nnf.falseE => { quantifiers := [], matrix := Nnf.falseE }
  | Nnf.lit literal => { quantifiers := [], matrix := Nnf.lit literal }
  | Nnf.conj left right => combine Nnf.conj (ofNnf left) (ofNnf right)
  | Nnf.disj left right => combine Nnf.disj (ofNnf left) (ofNnf right)
  | Nnf.forallE sort body =>
      let view := ofNnf body
      { view with quantifiers := Quantifier.forallE sort :: view.quantifiers }
  | Nnf.existsE sort body =>
      let view := ofNnf body
      { view with quantifiers := Quantifier.existsE sort :: view.quantifiers }

end PrenexView

/-- Core normal form 字句。 -/
abbrev Clause := Array Literal

/-- Core CNF 字句集；外层数组表示合取，内层数组表示析取。 -/
abbrev ClauseSet := Array Clause

namespace Clause

/-- 字句的透明结构相等。 -/
def eq (left right : Clause) : Bool :=
  SyntaxEq.literalListEq left.toList right.toList

/-- 字句中的字面量数量。 -/
def literalCount (clause : Clause) : Nat :=
  clause.size

/-- 字句重新嵌回核心公式；空字句解释为假。 -/
def toFormula (clause : Clause) : Formula :=
  Formula.disjunctionList (clause.toList.map Literal.toFormula)

end Clause

namespace ClauseSet

/-- 字句集的透明结构相等。 -/
def eq (left right : ClauseSet) : Bool :=
  let rec go : List Clause → List Clause → Bool
    | [], [] => true
    | leftClause :: leftRest, rightClause :: rightRest =>
        Clause.eq leftClause rightClause && go leftRest rightRest
    | _, _ => false
  go left.toList right.toList

/-- 字句集中是否已经含有空字句。 -/
def containsEmpty (clauses : ClauseSet) : Bool :=
  clauses.any (fun clause => clause.isEmpty)

/-- CNF 的合取。 -/
def conj (left right : ClauseSet) : ClauseSet :=
  left ++ right

/-- CNF 的析取，用分配律生成笛卡尔积字句。 -/
def disj (left right : ClauseSet) : ClauseSet :=
  Id.run do
    if left.isEmpty then
      return #[]
    if right.isEmpty then
      return #[]
    let mut out := #[]
    for leftClause in left do
      for rightClause in right do
        out := out.push (leftClause ++ rightClause)
    return out

/-- 字句集中的字面量总数。 -/
def literalCount (clauses : ClauseSet) : Nat :=
  Id.run do
    let mut count := 0
    for clause in clauses do
      count := count + clause.literalCount
    return count

/-- 字句集重新嵌回核心公式；空字句集解释为真。 -/
def toFormula (clauses : ClauseSet) : Formula :=
  let rec go : List Clause → Formula
    | [] => Formula.trueE
    | [clause] => clause.toFormula
    | clause :: rest => Formula.conj clause.toFormula (go rest)
  go clauses.toList

end ClauseSet

/-- 从量词自由 NNF 矩阵生成 CNF；若矩阵里仍有量词则拒绝。 -/
partial def cnfOfMatrix? : Nnf → Option ClauseSet
  | Nnf.trueE => some #[]
  | Nnf.falseE => some #[#[]]
  | Nnf.lit literal => some #[#[literal]]
  | Nnf.conj left right => do
      let leftClauses ← cnfOfMatrix? left
      let rightClauses ← cnfOfMatrix? right
      some (ClauseSet.conj leftClauses rightClauses)
  | Nnf.disj left right => do
      let leftClauses ← cnfOfMatrix? left
      let rightClauses ← cnfOfMatrix? right
      some (ClauseSet.disj leftClauses rightClauses)
  | Nnf.forallE .. => none
  | Nnf.existsE .. => none

/-- 从量词自由 NNF 矩阵生成 CNF。非矩阵输入返回显式假字句作为防御性默认值。 -/
def cnfOfMatrix (matrix : Nnf) : ClauseSet :=
  (cnfOfMatrix? matrix).getD #[#[]]

/-- 完整 core normal form 结果。 -/
structure Pipeline where
  config : Config
  source : Formula
  normalized : Formula
  trace : Trace
  nnf : Nnf
  prenex : PrenexView
  clauses : ClauseSet
  sourceSize : Nat
  normalizedSize : Nat
  nnfSize : Nat
  matrixSize : Nat
  prefixDepth : Nat
  clauseCount : Nat
  literalCount : Nat
  deriving Repr, Lean.ToExpr

namespace Pipeline

/-- 从核心公式构造完整 normal form pipeline。 -/
def build (source : Formula) (config : Config := {}) : Pipeline :=
  let normalized := normalizeFormula source (config := config)
  let trace := Trace.ofFormula source (config := config)
  let nnf := toNnfWith Polarity.positive normalized
  let prenex := PrenexView.ofNnf nnf
  let clauses := cnfOfMatrix prenex.matrix
  {
    config := config
    source := source
    normalized := normalized
    trace := trace
    nnf := nnf
    prenex := prenex
    clauses := clauses
    sourceSize := source.size
    normalizedSize := normalized.size
    nnfSize := nnf.size
    matrixSize := prenex.matrix.size
    prefixDepth := prenex.quantifiers.length
    clauseCount := clauses.size
    literalCount := clauses.literalCount
  }

/-- 检查 normal form pipeline 是否可由当前算法复算。 -/
def check (payload : Pipeline) : Bool :=
  let expected := build payload.source (config := payload.config)
  payload.source.check? &&
    payload.normalized.check? &&
    Trace.check payload.config payload.trace &&
    TraceExpr.eq payload.trace.source (TraceExpr.formula payload.source) &&
    TraceExpr.eq payload.trace.target (TraceExpr.formula payload.normalized) &&
    payload.prenex.toFormula.check? &&
    Formula.checkWith (Prefix.boundSorts payload.prenex.quantifiers) payload.clauses.toFormula &&
  SyntaxEq.formulaEq payload.normalized expected.normalized &&
    SyntaxEq.nnfEq payload.nnf expected.nnf &&
      PrenexView.eq payload.prenex expected.prenex &&
        (match cnfOfMatrix? payload.prenex.matrix with
        | some clauses => ClauseSet.eq payload.clauses clauses
        | none => false) &&
          ClauseSet.eq payload.clauses expected.clauses &&
            payload.sourceSize == expected.sourceSize &&
              payload.normalizedSize == expected.normalizedSize &&
                payload.nnfSize == expected.nnfSize &&
                  payload.matrixSize == expected.matrixSize &&
                    payload.prefixDepth == expected.prefixDepth &&
                      payload.clauseCount == expected.clauseCount &&
                        payload.literalCount == expected.literalCount &&
                          payload.prenex.matrix.quantifierFree

end Pipeline

namespace FirstOrderProjection

/-!
`CoreSyntax.Search` 当前仍是二元 literal 表面：等词与成员关系直接使用左右项，其他
谓词用一个 tuple 项装载真实参数。这里把 core/FOOL normal form 的前束 CNF 投影到这
个搜索表面，供 resolution、superposition 与 demodulation 直接消费。
-/

/-- 投影过程中使用的状态。 -/
structure State where
  nextVar : Nat
  nextSkolem : Nat
  auxBase : Nat
  skolemTrace : Array CoreSyntax.Search.Intro := #[]
  deriving Repr, Lean.ToExpr

/-- 当前 De Bruijn 前束上下文。`bound` 按近到远排列。 -/
structure Context where
  bound : List CoreSyntax.Search.Term := []
  universals : List CoreSyntax.Search.Term := []
  deriving Repr, Inhabited, BEq, Lean.ToExpr

abbrev ProjectM := StateT State Option

/-- 投影失败。 -/
def fail {α : Type} : ProjectM α :=
  fun _ => none

/-- 本地列表查找，避免把投影器绑到额外 API 上。 -/
def lookupList? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => lookupList? tail index

/-- core 函数角色到当前搜索层符号种类的擦除。 -/
def symbolKindOfRole : FunctionRole → CoreSyntax.Search.SymbolKind
  | FunctionRole.parameter => CoreSyntax.Search.SymbolKind.parameter
  | FunctionRole.skolem => CoreSyntax.Search.SymbolKind.skolem
  | FunctionRole.definition => CoreSyntax.Search.SymbolKind.definition
  | FunctionRole.choice => CoreSyntax.Search.SymbolKind.choice
  | FunctionRole.builtin => CoreSyntax.Search.SymbolKind.builtin
  | FunctionRole.extensionalWitness => CoreSyntax.Search.SymbolKind.extensionalWitness

/-- core 函数符号到搜索层函数符号的投影。 -/
def functionSymbol (symbol : FunctionSymbol) : CoreSyntax.Search.FunctionSymbol :=
  {
    id := symbol.id
    arity := symbol.arity
    kind := symbolKindOfRole symbol.role
    inputSorts := symbol.inputSorts
    outputSort := symbol.outputSort
  }

namespace Aux

/-- FOOL 投影内部保留的辅助函数符号偏移。 -/
def boolFalse : Nat := 0
def boolTrue : Nat := 1
def notE : Nat := 2
def andE : Nat := 3
def orE : Nat := 4
def impE : Nat := 5
def iffE : Nat := 6
def ite : Nat := 7
def boolHolds : Nat := 8
def quote : Nat := 9
def apply : Nat := 10
def lambda : Nat := 11

end Aux

/-- 投影内部辅助符号的返回 sort。 -/
def auxOutputSort (offset : Nat) : CoreSort :=
  if offset == Aux.boolFalse || offset == Aux.boolTrue ||
      offset == Aux.notE || offset == Aux.andE || offset == Aux.orE ||
        offset == Aux.impE || offset == Aux.iffE || offset == Aux.boolHolds ||
          offset == Aux.quote then
    CoreSort.bool
  else
    CoreSort.object

/-- 构造投影内部辅助函数符号。 -/
def auxSymbol (offset arity : Nat) : ProjectM CoreSyntax.Search.FunctionSymbol := do
  let state ← get
  pure {
    id := state.auxBase + offset
    arity := arity
    kind := CoreSyntax.Search.SymbolKind.builtin
    outputSort := auxOutputSort offset
  }

/-- 构造投影内部辅助项。 -/
def auxApp (offset : Nat) (args : List CoreSyntax.Search.Term) : ProjectM CoreSyntax.Search.Term := do
  let symbol ← auxSymbol offset args.length
  pure (CoreSyntax.Search.Term.app symbol args)

/-- FOOL 布尔常量在一阶搜索层中的编码。 -/
def boolConst (value : Bool) : ProjectM CoreSyntax.Search.Term :=
  auxApp (if value then Aux.boolTrue else Aux.boolFalse) []

/-- tuple 项；只在搜索表面打包参数，可信 materializer 会在进入 DAG 前重新展开。 -/
def tupleTerm (predicate : PredicateSymbol)
    (args : List CoreSyntax.Search.Term) : CoreSyntax.Search.Term :=
  let symbol : CoreSyntax.Search.FunctionSymbol :=
    {
      id := predicate.id
      arity := args.length
      kind := CoreSyntax.Search.SymbolKind.tuple
      inputSorts := predicate.inputSorts
    }
  CoreSyntax.Search.Term.app symbol args

namespace Projectable

mutual
  /-- 可由一阶 DAG 直接解释的 core 项片段。 -/
  def term : Term → Bool
    | Term.fvar .. => true
    | Term.app _ arguments => termList arguments
    | _ => false

  /-- 可由一阶 DAG 直接解释的 core 项列表。 -/
  def termList : List Term → Bool
    | [] => true
    | head :: tail => term head && termList tail
end

/-- 可由一阶 DAG 直接解释的 core 原子。 -/
def atom : Atom → Bool
  | Atom.predicate _ arguments => termList arguments
  | Atom.equal _ left right => term left && term right
  | Atom.boolTerm input => term input

/-- 可由一阶 DAG 直接解释的 core 文字。 -/
def literal (input : Literal) : Bool :=
  atom input.atom

/-- 可由一阶 DAG 直接解释的 core 字句。 -/
def clause (input : Clause) : Bool :=
  input.all literal

/-- 可由一阶 DAG 直接解释的 core 字句集。 -/
def clauseSet (input : ClauseSet) : Bool :=
  input.all clause

end Projectable

mutual
  /-- 源项中自由变量编号的最大后继。 -/
  def Term.maxFreeVarSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar _ id => id + 1
    | Term.app _ args => Term.maxFreeVarListSucc args
    | Term.apply fn arg => Nat.max (Term.maxFreeVarSucc fn) (Term.maxFreeVarSucc arg)
    | Term.bool _ => 0
    | Term.notE body => Term.maxFreeVarSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Nat.max (Term.maxFreeVarSucc left) (Term.maxFreeVarSucc right)
    | Term.quote formula => Formula.maxFreeVarSucc formula
    | Term.lam _ _ body => Term.maxFreeVarSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (Formula.maxFreeVarSucc condition)
          (Nat.max (Term.maxFreeVarSucc thenTerm) (Term.maxFreeVarSucc elseTerm))

  /-- 源公式中自由变量编号的最大后继。 -/
  def Formula.maxFreeVarSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom _ args => Term.maxFreeVarListSucc args
    | Formula.equal _ left right => Nat.max (Term.maxFreeVarSucc left) (Term.maxFreeVarSucc right)
    | Formula.boolTerm term => Term.maxFreeVarSucc term
    | Formula.neg body => Formula.maxFreeVarSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Nat.max (Formula.maxFreeVarSucc left) (Formula.maxFreeVarSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.maxFreeVarSucc body

  /-- 源项列表中自由变量编号的最大后继。 -/
  def Term.maxFreeVarListSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (Term.maxFreeVarSucc term) (Term.maxFreeVarListSucc rest)
end

mutual
  /-- 源项中函数符号编号的最大后继。 -/
  def Term.maxFunctionIdSucc : Term → Nat
    | Term.bvar .. => 0
    | Term.fvar .. => 0
    | Term.app symbol args => Nat.max (symbol.id + 1) (Term.maxFunctionListIdSucc args)
    | Term.apply fn arg => Nat.max (Term.maxFunctionIdSucc fn) (Term.maxFunctionIdSucc arg)
    | Term.bool _ => 0
    | Term.notE body => Term.maxFunctionIdSucc body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Nat.max (Term.maxFunctionIdSucc left) (Term.maxFunctionIdSucc right)
    | Term.quote formula => Formula.maxFunctionIdSucc formula
    | Term.lam _ _ body => Term.maxFunctionIdSucc body
    | Term.ite _ condition thenTerm elseTerm =>
        Nat.max (Formula.maxFunctionIdSucc condition)
          (Nat.max (Term.maxFunctionIdSucc thenTerm) (Term.maxFunctionIdSucc elseTerm))

  /-- 源公式中函数符号编号的最大后继。 -/
  def Formula.maxFunctionIdSucc : Formula → Nat
    | Formula.trueE => 0
    | Formula.falseE => 0
    | Formula.atom _ args => Term.maxFunctionListIdSucc args
    | Formula.equal _ left right => Nat.max (Term.maxFunctionIdSucc left) (Term.maxFunctionIdSucc right)
    | Formula.boolTerm term => Term.maxFunctionIdSucc term
    | Formula.neg body => Formula.maxFunctionIdSucc body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        Nat.max (Formula.maxFunctionIdSucc left) (Formula.maxFunctionIdSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.maxFunctionIdSucc body

  /-- 源项列表中函数符号编号的最大后继。 -/
  def Term.maxFunctionListIdSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (Term.maxFunctionIdSucc term) (Term.maxFunctionListIdSucc rest)
end

/-- 按当前 De Bruijn 上下文生成定义符号的实参。上下文按近到远排列。 -/
def contextArgsFrom (index : Nat) : List CoreSort → List Term
  | [] => []
  | sort :: rest => Term.bvar sort index :: contextArgsFrom (index + 1) rest

/-- 按当前 De Bruijn 上下文生成定义符号的实参。 -/
def contextArgs (contextSorts : List CoreSort) : List Term :=
  contextArgsFrom 0 contextSorts

/-- FOOL 公式参数定义显式依赖的 typed 自由变量。 -/
structure FormulaArgumentFreeVarParam where
  sort : CoreSort
  varId : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr

namespace FormulaArgumentFreeVarParam

/-- 自由变量参数对应的核心项。 -/
def term (parameter : FormulaArgumentFreeVarParam) : Term :=
  Term.fvar parameter.sort parameter.varId

/-- 保持首次出现顺序地插入自由变量参数。 -/
def insert (parameter : FormulaArgumentFreeVarParam)
    (parameters : List FormulaArgumentFreeVarParam) :
    List FormulaArgumentFreeVarParam :=
  if parameters.contains parameter then parameters else parameters ++ [parameter]

/-- 合并两个自由变量参数表，并保持首次出现顺序。 -/
def merge (left right : List FormulaArgumentFreeVarParam) :
    List FormulaArgumentFreeVarParam :=
  right.foldl (fun parameters parameter => insert parameter parameters) left

/-- 自由变量参数表是否无重复。 -/
def distinct (parameters : List FormulaArgumentFreeVarParam) : Bool :=
  parameters.Pairwise fun left right => left != right

/-- 自由变量参数对应的输入 sort。 -/
def sorts (parameters : List FormulaArgumentFreeVarParam) : List CoreSort :=
  parameters.map (fun parameter => parameter.sort)

/-- 自由变量参数对应的实参项。 -/
def terms (parameters : List FormulaArgumentFreeVarParam) : List Term :=
  parameters.map term

end FormulaArgumentFreeVarParam

mutual
  /-- 核心项中 typed 自由变量的首次出现有序表。 -/
  def Term.formulaArgumentFreeVarParams : Term → List FormulaArgumentFreeVarParam
    | Term.bvar .. => []
    | Term.fvar sort varId => [{ sort := sort, varId := varId }]
    | Term.app _ args => Term.formulaArgumentFreeVarParamsList args
    | Term.apply fn arg =>
        FormulaArgumentFreeVarParam.merge
          (Term.formulaArgumentFreeVarParams fn)
          (Term.formulaArgumentFreeVarParams arg)
    | Term.bool _ => []
    | Term.notE body => Term.formulaArgumentFreeVarParams body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        FormulaArgumentFreeVarParam.merge
          (Term.formulaArgumentFreeVarParams left)
          (Term.formulaArgumentFreeVarParams right)
    | Term.quote formula => Formula.formulaArgumentFreeVarParams formula
    | Term.lam _ _ body => Term.formulaArgumentFreeVarParams body
    | Term.ite _ condition thenTerm elseTerm =>
        FormulaArgumentFreeVarParam.merge
          (Formula.formulaArgumentFreeVarParams condition)
          (FormulaArgumentFreeVarParam.merge
            (Term.formulaArgumentFreeVarParams thenTerm)
            (Term.formulaArgumentFreeVarParams elseTerm))

  /-- 核心公式中 typed 自由变量的首次出现有序表。 -/
  def Formula.formulaArgumentFreeVarParams :
      Formula → List FormulaArgumentFreeVarParam
    | Formula.trueE => []
    | Formula.falseE => []
    | Formula.atom _ args => Term.formulaArgumentFreeVarParamsList args
    | Formula.equal _ left right =>
        FormulaArgumentFreeVarParam.merge
          (Term.formulaArgumentFreeVarParams left)
          (Term.formulaArgumentFreeVarParams right)
    | Formula.boolTerm term => Term.formulaArgumentFreeVarParams term
    | Formula.neg body => Formula.formulaArgumentFreeVarParams body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        FormulaArgumentFreeVarParam.merge
          (Formula.formulaArgumentFreeVarParams left)
          (Formula.formulaArgumentFreeVarParams right)
    | Formula.forallE _ body
    | Formula.existsE _ body =>
        Formula.formulaArgumentFreeVarParams body

  /-- 核心项列表中 typed 自由变量的首次出现有序表。 -/
  def Term.formulaArgumentFreeVarParamsList :
      List Term → List FormulaArgumentFreeVarParam
    | [] => []
    | term :: rest =>
        FormulaArgumentFreeVarParam.merge
          (Term.formulaArgumentFreeVarParams term)
          (Term.formulaArgumentFreeVarParamsList rest)
end

/-- 把一个公式按当前上下文全称闭合。上下文按近到远排列。 -/
def closeForall (contextSorts : List CoreSort) (body : Formula) : Formula :=
  contextSorts.foldl (fun acc sort => Formula.forallE sort acc) body

/-- FOOL 公式参数引入的布尔定义。 -/
structure BoolDefinition where
  index : Nat
  symbol : FunctionSymbol
  contextSorts : List CoreSort
  freeVarParams : List FormulaArgumentFreeVarParam
  sourceFormula : Formula
  formula : Formula
  deriving Repr, Lean.ToExpr

namespace BoolDefinition

/-- 定义符号的完整输入 sort。 -/
def inputSorts (definition : BoolDefinition) : List CoreSort :=
  definition.contextSorts ++
    FormulaArgumentFreeVarParam.sorts definition.freeVarParams

/-- 定义符号在当前上下文中的完整实参。 -/
def arguments (definition : BoolDefinition) : List Term :=
  contextArgs definition.contextSorts ++
    FormulaArgumentFreeVarParam.terms definition.freeVarParams

/-- 定义符号在当前上下文中的替换项。 -/
def replacement (definition : BoolDefinition) : Term :=
  Term.app definition.symbol definition.arguments

/-- 定义公式：`∀ctx, d(ctx) ↔ φ(ctx)`。 -/
def definitionFormula (definition : BoolDefinition) : Formula :=
  closeForall definition.contextSorts
    (Formula.iffE (Formula.boolTerm definition.replacement) definition.formula)

/-- 布尔定义本身的可计算检查。 -/
def check (definition : BoolDefinition) : Bool :=
  definition.symbol.role == FunctionRole.definition &&
    definition.freeVarParams ==
      Formula.formulaArgumentFreeVarParams definition.sourceFormula &&
      definition.freeVarParams ==
        Formula.formulaArgumentFreeVarParams definition.formula &&
        FormulaArgumentFreeVarParam.distinct definition.freeVarParams &&
          definition.symbol.arity == definition.inputSorts.length &&
            definition.symbol.inputSorts == definition.inputSorts &&
              definition.symbol.outputSort == CoreSort.bool &&
                Formula.checkWith definition.contextSorts definition.sourceFormula &&
                  Formula.checkWith definition.contextSorts definition.formula &&
                    (match
                      Term.inferSortWith definition.contextSorts definition.replacement with
                    | some sort => sort == CoreSort.bool
                    | none => false) &&
                      definition.definitionFormula.check?

/-- 布尔定义的透明结构相等。 -/
def eq (left right : BoolDefinition) : Bool :=
  left.index == right.index &&
    left.symbol == right.symbol &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.formulaEq left.sourceFormula right.sourceFormula &&
            SyntaxEq.formulaEq left.formula right.formula

/-- 布尔定义列表的透明结构相等。 -/
def listEq : List BoolDefinition → List BoolDefinition → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false

/-- 布尔定义数组的透明结构相等。 -/
def arrayEq (left right : Array BoolDefinition) : Bool :=
  listEq left.toList right.toList

end BoolDefinition

/-- 一处公式参数被替换成布尔定义符号的 trace 记录。 -/
structure FormulaArgumentIntro where
  definitionIndex : Nat
  symbol : FunctionSymbol
  contextSorts : List CoreSort
  freeVarParams : List FormulaArgumentFreeVarParam
  sourceFormula : Formula
  formula : Formula
  replacement : Term
  deriving Repr, Lean.ToExpr

namespace FormulaArgumentIntro

/-- 从布尔定义构造公式参数引入记录。 -/
def ofDefinition (definition : BoolDefinition) : FormulaArgumentIntro :=
  {
    definitionIndex := definition.index
    symbol := definition.symbol
    contextSorts := definition.contextSorts
    freeVarParams := definition.freeVarParams
    sourceFormula := definition.sourceFormula
    formula := definition.formula
    replacement := definition.replacement
  }

/-- 本地列表查找，避免依赖不同 Lean 版本中的 `List.get?` API 名称。 -/
def lookupDefinition? : List BoolDefinition → Nat → Option BoolDefinition
  | [], _ => none
  | definition :: _, 0 => some definition
  | _ :: rest, index + 1 => lookupDefinition? rest index

/-- 本地数组查找，避免依赖不同 Lean 版本中的 `Array.get?` API 名称。 -/
def definitionAt? (definitions : Array BoolDefinition) (index : Nat) : Option BoolDefinition :=
  lookupDefinition? definitions.toList index

/-- 公式参数引入记录是否由给定定义表支撑。 -/
def check (definitions : Array BoolDefinition) (intro : FormulaArgumentIntro) : Bool :=
  match definitionAt? definitions intro.definitionIndex with
  | some definition =>
      BoolDefinition.check definition &&
        intro.symbol == definition.symbol &&
          intro.contextSorts == definition.contextSorts &&
            intro.freeVarParams == definition.freeVarParams &&
              SyntaxEq.formulaEq intro.sourceFormula definition.sourceFormula &&
                SyntaxEq.formulaEq intro.formula definition.formula &&
                  SyntaxEq.termEq intro.replacement definition.replacement
  | none => false

/-- 公式参数引入记录的透明结构相等。 -/
def eq (left right : FormulaArgumentIntro) : Bool :=
  left.definitionIndex == right.definitionIndex &&
    left.symbol == right.symbol &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.formulaEq left.sourceFormula right.sourceFormula &&
            SyntaxEq.formulaEq left.formula right.formula &&
              SyntaxEq.termEq left.replacement right.replacement

/-- 公式参数引入列表的透明结构相等。 -/
def listEq : List FormulaArgumentIntro → List FormulaArgumentIntro → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false

/-- 公式参数引入数组的透明结构相等。 -/
def arrayEq (left right : Array FormulaArgumentIntro) : Bool :=
  listEq left.toList right.toList

end FormulaArgumentIntro

/-- 公式参数定义化过程中的构造状态。 -/
structure FormulaArgumentState where
  nextDefinition : Nat
  intros : Array FormulaArgumentIntro := #[]
  definitions : Array BoolDefinition := #[]
  deriving Repr, Lean.ToExpr

abbrev FormulaArgumentM := StateM FormulaArgumentState

/-- 引入一个新的布尔定义符号，并返回当前上下文中的替换项。 -/
def introBoolDefinition (contextSorts : List CoreSort)
    (sourceFormula formula : Formula) : FormulaArgumentM Term := do
  let state ← get
  let freeVarParams := Formula.formulaArgumentFreeVarParams sourceFormula
  let inputSorts :=
    contextSorts ++ FormulaArgumentFreeVarParam.sorts freeVarParams
  let symbol : FunctionSymbol := {
    id := state.nextDefinition
    arity := inputSorts.length
    role := FunctionRole.definition
    inputSorts := inputSorts
    outputSort := CoreSort.bool
  }
  let definition : BoolDefinition := {
    index := state.definitions.size
    symbol := symbol
    contextSorts := contextSorts
    freeVarParams := freeVarParams
    sourceFormula := sourceFormula
    formula := formula
  }
  let intro := FormulaArgumentIntro.ofDefinition definition
  set {
    state with
    nextDefinition := state.nextDefinition + 1
    intros := state.intros.push intro
    definitions := state.definitions.push definition
  }
  pure definition.replacement

mutual
  /-- 对公式执行 FOOL 公式参数定义化。Bool sort 量词保留为 typed 一阶量词。 -/
  def introduceFormulaArguments (contextSorts : List CoreSort) :
      Formula → FormulaArgumentM Formula
    | Formula.trueE => pure Formula.trueE
    | Formula.falseE => pure Formula.falseE
    | Formula.atom predicate args => do
        let args ← introduceTermListFormulaArguments contextSorts args
        pure (Formula.atom predicate args)
    | Formula.equal sort left right => do
        let left ← introduceTermFormulaArguments contextSorts left
        let right ← introduceTermFormulaArguments contextSorts right
        pure (Formula.equal sort left right)
    | Formula.boolTerm term => do
        let term ← introduceBoolViewTermFormulaArguments contextSorts term
        pure (Formula.boolTerm term)
    | Formula.neg body => do
        let body ← introduceFormulaArguments contextSorts body
        pure (Formula.neg body)
    | Formula.imp left right => do
        let left ← introduceFormulaArguments contextSorts left
        let right ← introduceFormulaArguments contextSorts right
        pure (Formula.imp left right)
    | Formula.conj left right => do
        let left ← introduceFormulaArguments contextSorts left
        let right ← introduceFormulaArguments contextSorts right
        pure (Formula.conj left right)
    | Formula.disj left right => do
        let left ← introduceFormulaArguments contextSorts left
        let right ← introduceFormulaArguments contextSorts right
        pure (Formula.disj left right)
    | Formula.iffE left right => do
        let left ← introduceFormulaArguments contextSorts left
        let right ← introduceFormulaArguments contextSorts right
        pure (Formula.iffE left right)
    | Formula.forallE sort body => do
        let body ← introduceFormulaArguments (sort :: contextSorts) body
        pure (Formula.forallE sort body)
    | Formula.existsE sort body => do
        let body ← introduceFormulaArguments (sort :: contextSorts) body
        pure (Formula.existsE sort body)

  /-- 对项执行 FOOL 公式参数定义化。 -/
  def introduceTermFormulaArguments (contextSorts : List CoreSort) :
      Term → FormulaArgumentM Term
    | Term.bvar sort index => pure (Term.bvar sort index)
    | Term.fvar sort id => pure (Term.fvar sort id)
    | Term.app symbol args => do
        let args ← introduceTermListFormulaArguments contextSorts args
        pure (Term.app symbol args)
    | Term.apply fn arg => do
        let fn ← introduceTermFormulaArguments contextSorts fn
        let arg ← introduceTermFormulaArguments contextSorts arg
        pure (Term.apply fn arg)
    | Term.bool value => pure (Term.bool value)
    | Term.notE body => do
        let body ← introduceTermFormulaArguments contextSorts body
        pure (Term.notE body)
    | Term.andE left right => do
        let left ← introduceTermFormulaArguments contextSorts left
        let right ← introduceTermFormulaArguments contextSorts right
        pure (Term.andE left right)
    | Term.orE left right => do
        let left ← introduceTermFormulaArguments contextSorts left
        let right ← introduceTermFormulaArguments contextSorts right
        pure (Term.orE left right)
    | Term.impE left right => do
        let left ← introduceTermFormulaArguments contextSorts left
        let right ← introduceTermFormulaArguments contextSorts right
        pure (Term.impE left right)
    | Term.iffE left right => do
        let left ← introduceTermFormulaArguments contextSorts left
        let right ← introduceTermFormulaArguments contextSorts right
        pure (Term.iffE left right)
    | Term.quote formula => do
        let sourceFormula := formula
        let formula ← introduceFormulaArguments contextSorts sourceFormula
        introBoolDefinition contextSorts sourceFormula formula
    | Term.lam domain codomain body => do
        let body ← introduceTermFormulaArguments (domain :: contextSorts) body
        pure (Term.lam domain codomain body)
    | Term.ite sort condition thenTerm elseTerm => do
        let condition ← introduceFormulaArguments contextSorts condition
        let thenTerm ← introduceTermFormulaArguments contextSorts thenTerm
        let elseTerm ← introduceTermFormulaArguments contextSorts elseTerm
        pure (Term.ite sort condition thenTerm elseTerm)

  /--
  `boolTerm (quote φ)` 是 FOOL 的公式/布尔项桥，不作为“公式参数”定义化；
  但 `boolTerm (f (quote φ))` 中的子参数仍会被定义化。
  -/
  def introduceBoolViewTermFormulaArguments (contextSorts : List CoreSort) :
      Term → FormulaArgumentM Term
    | Term.quote formula => do
        let formula ← introduceFormulaArguments contextSorts formula
        pure (Term.quote formula)
    | term => introduceTermFormulaArguments contextSorts term

  /-- 对项列表执行 FOOL 公式参数定义化。 -/
  def introduceTermListFormulaArguments (contextSorts : List CoreSort) :
      List Term → FormulaArgumentM (List Term)
    | [] => pure []
    | term :: rest => do
        let term ← introduceTermFormulaArguments contextSorts term
        let rest ← introduceTermListFormulaArguments contextSorts rest
        pure (term :: rest)
end

/-- 公式参数定义化 trace。 -/
structure FormulaArgumentTrace where
  source : Formula
  targetCore : Formula
  target : Formula
  intros : Array FormulaArgumentIntro
  definitions : Array BoolDefinition
  deriving Repr, Lean.ToExpr

namespace FormulaArgumentTrace

/-- 从定义化后的核心公式和定义表生成最终公式。 -/
def withDefinitions (targetCore : Formula) (definitions : Array BoolDefinition) : Formula :=
  Formula.conjunctionList
    (targetCore :: definitions.toList.map BoolDefinition.definitionFormula)

/-- 构造公式参数定义化 trace。 -/
def build (source : Formula) : FormulaArgumentTrace :=
  let initial : FormulaArgumentState := { nextDefinition := Formula.maxFunctionIdSucc source + 1 }
  let (targetCore, state) := (introduceFormulaArguments [] source).run initial
  {
    source := source
    targetCore := targetCore
    target := withDefinitions targetCore state.definitions
    intros := state.intros
    definitions := state.definitions
  }

/-- 公式参数定义化 trace 的可计算 checker。 -/
def check (trace : FormulaArgumentTrace) : Bool :=
  let expected := build trace.source
  trace.source.check? &&
    trace.targetCore.check? &&
      trace.target.check? &&
        SyntaxEq.formulaEq trace.targetCore expected.targetCore &&
          SyntaxEq.formulaEq trace.target expected.target &&
            FormulaArgumentIntro.arrayEq trace.intros expected.intros &&
              BoolDefinition.arrayEq trace.definitions expected.definitions &&
                trace.definitions.toList.all BoolDefinition.check &&
                  trace.intros.toList.all (FormulaArgumentIntro.check trace.definitions)

end FormulaArgumentTrace

/-- FOOL 定义化子句化 payload。 -/
structure FOOLClausePayload where
  config : Config
  source : Formula
  sourcePipeline : Pipeline
  argumentSource : Formula
  argumentTrace : FormulaArgumentTrace
  clauseSource : Formula
  clausePipeline : Pipeline
  intros : Array FormulaArgumentIntro
  definitions : Array BoolDefinition
  deriving Repr, Lean.ToExpr

namespace FOOLClausePayload

/-- 构造 FOOL 定义化子句 payload。 -/
def build (source : Formula) (config : Config := {}) : FOOLClausePayload :=
  let sourcePipeline := Pipeline.build source (config := config)
  let argumentConfig : Config := { config with fool := false }
  let argumentSource := normalizeFormula source (config := argumentConfig)
  let argumentTrace := FormulaArgumentTrace.build argumentSource
  let clauseSource := argumentTrace.target
  let clausePipeline := Pipeline.build clauseSource (config := config)
  {
    config := config
    source := source
    sourcePipeline := sourcePipeline
    argumentSource := argumentSource
    argumentTrace := argumentTrace
    clauseSource := clauseSource
    clausePipeline := clausePipeline
    intros := argumentTrace.intros
    definitions := argumentTrace.definitions
  }

/-- FOOL 定义化子句 payload 的可计算 checker。 -/
def check (payload : FOOLClausePayload) : Bool :=
  let expected := build payload.source (config := payload.config)
  payload.source.check? &&
    Pipeline.check payload.sourcePipeline &&
      SyntaxEq.formulaEq payload.sourcePipeline.source payload.source &&
        SyntaxEq.formulaEq payload.argumentSource
          (normalizeFormula payload.source (config := { payload.config with fool := false })) &&
        FormulaArgumentTrace.check payload.argumentTrace &&
          SyntaxEq.formulaEq payload.argumentTrace.source payload.argumentSource &&
            SyntaxEq.formulaEq payload.clauseSource payload.argumentTrace.target &&
              Pipeline.check payload.clausePipeline &&
                SyntaxEq.formulaEq payload.clausePipeline.source payload.clauseSource &&
                  FormulaArgumentIntro.arrayEq payload.intros payload.argumentTrace.intros &&
                    BoolDefinition.arrayEq payload.definitions payload.argumentTrace.definitions &&
                      SyntaxEq.formulaEq payload.argumentSource expected.argumentSource &&
                      SyntaxEq.formulaEq payload.clauseSource expected.clauseSource &&
                        Pipeline.check expected.clausePipeline &&
                          FormulaArgumentIntro.arrayEq payload.intros expected.intros &&
                            BoolDefinition.arrayEq payload.definitions expected.definitions

end FOOLClausePayload

/-- 投影初始状态。辅助符号从源函数符号命名空间之后开始。 -/
def initialState (source : Formula) : State :=
  let fnBase := Formula.maxFunctionIdSucc source + 1
  {
    nextVar := Formula.maxFreeVarSucc source
    nextSkolem := fnBase + 32
    auxBase := fnBase
  }

/-- 生成一个新的全称变量。 -/
def freshUniversal : ProjectM CoreSyntax.Search.Term := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  pure (CoreSyntax.Search.Term.var state.nextVar)

/-- 生成一个依赖当前全称上下文的 Skolem 项。 -/
def freshSkolem (ctx : Context) : ProjectM CoreSyntax.Search.Term := do
  let state ← get
  let args := ctx.universals.reverse
  let symbol : CoreSyntax.Search.FunctionSymbol :=
    {
      id := state.nextSkolem
      arity := args.length
      kind := CoreSyntax.Search.SymbolKind.skolem
    }
  let term := CoreSyntax.Search.Term.app symbol args
  let intro : CoreSyntax.Search.Intro := {
    symbol := symbol
    universalArgs := args
    term := term
    contextDepth := args.length
  }
  set {
    state with
    nextSkolem := state.nextSkolem + 1
    skolemTrace := state.skolemTrace.push intro
  }
  pure term

/-- 为残留 lambda reification 生成不会逃逸成一阶自由变量的闭包占位常量。 -/
def freshLambdaBinder : ProjectM CoreSyntax.Search.Term := do
  let state ← get
  let symbol : CoreSyntax.Search.FunctionSymbol :=
    { id := state.nextSkolem, arity := 0, kind := CoreSyntax.Search.SymbolKind.parameter }
  set { state with nextSkolem := state.nextSkolem + 1 }
  pure (CoreSyntax.Search.Term.app symbol [])

mutual
  /-- 把 core 项投影到当前搜索层项。 -/
  partial def projectTerm (ctx : Context) : Term → ProjectM CoreSyntax.Search.Term
    | Term.bvar _ index =>
        match lookupList? ctx.bound index with
        | some term => pure term
        | none => fail
    | Term.fvar CoreSort.object id =>
        -- 当前一阶搜索替换以无类型 `VarId` 为键；对象变量在投影边界统一降为 canonical var。
        pure (CoreSyntax.Search.Term.var id)
    | Term.fvar sort id => pure (CoreSyntax.Search.Term.fvar sort id)
    | Term.app symbol args => do
        let args ← projectTermList ctx args
        pure (CoreSyntax.Search.Term.app (functionSymbol symbol) args)
    | Term.apply fn arg => do
        let fn ← projectTerm ctx fn
        let arg ← projectTerm ctx arg
        pure (CoreSyntax.Search.Term.apply fn arg)
    | Term.bool value => boolConst value
    | Term.notE body => do
        let body ← projectTerm ctx body
        auxApp Aux.notE [body]
    | Term.andE left right => do
        let left ← projectTerm ctx left
        let right ← projectTerm ctx right
        auxApp Aux.andE [left, right]
    | Term.orE left right => do
        let left ← projectTerm ctx left
        let right ← projectTerm ctx right
        auxApp Aux.orE [left, right]
    | Term.impE left right => do
        let left ← projectTerm ctx left
        let right ← projectTerm ctx right
        auxApp Aux.impE [left, right]
    | Term.iffE left right => do
        let left ← projectTerm ctx left
        let right ← projectTerm ctx right
        auxApp Aux.iffE [left, right]
    | Term.quote formula => do
        let term ← projectFormulaAsTerm ctx formula
        auxApp Aux.quote [term]
    | Term.lam domain codomain body => do
        let binder := CoreSyntax.Search.Term.bvar domain 0
        let body ← projectTerm { ctx with bound := binder :: ctx.bound } body
        pure (CoreSyntax.Search.Term.lam domain codomain body)
    | Term.ite _ condition thenTerm elseTerm => do
        let condition ← projectFormulaAsTerm ctx condition
        let thenTerm ← projectTerm ctx thenTerm
        let elseTerm ← projectTerm ctx elseTerm
        auxApp Aux.ite [condition, thenTerm, elseTerm]

  /-- 把 core 公式作为布尔项编码到搜索层项。 -/
  partial def projectFormulaAsTerm (ctx : Context) : Formula → ProjectM CoreSyntax.Search.Term
    | Formula.trueE => boolConst true
    | Formula.falseE => boolConst false
    | Formula.atom predicate args => do
        let args ← projectTermList ctx args
        pure (tupleTerm predicate args)
    | Formula.equal _ left right => do
        let left ← projectTerm ctx left
        let right ← projectTerm ctx right
        auxApp Aux.iffE [left, right]
    | Formula.boolTerm term => projectTerm ctx term
    | Formula.neg body => do
        let body ← projectFormulaAsTerm ctx body
        auxApp Aux.notE [body]
    | Formula.imp left right => do
        let left ← projectFormulaAsTerm ctx left
        let right ← projectFormulaAsTerm ctx right
        auxApp Aux.impE [left, right]
    | Formula.conj left right => do
        let left ← projectFormulaAsTerm ctx left
        let right ← projectFormulaAsTerm ctx right
        auxApp Aux.andE [left, right]
    | Formula.disj left right => do
        let left ← projectFormulaAsTerm ctx left
        let right ← projectFormulaAsTerm ctx right
        auxApp Aux.orE [left, right]
    | Formula.iffE left right => do
        let left ← projectFormulaAsTerm ctx left
        let right ← projectFormulaAsTerm ctx right
        auxApp Aux.iffE [left, right]
    | Formula.forallE .. => fail
    | Formula.existsE .. => fail

  /-- 把 core 项列表投影到搜索层项列表。 -/
  partial def projectTermList (ctx : Context) : List Term → ProjectM (List CoreSyntax.Search.Term)
    | [] => pure []
    | term :: rest => do
        let term ← projectTerm ctx term
        let rest ← projectTermList ctx rest
        pure (term :: rest)
end

/-- 把 core 原子投影到搜索层 literal。 -/
def projectAtom (ctx : Context) (positive : Bool) :
    Atom → ProjectM CoreSyntax.Search.Literal := fun
  | Atom.equal _ left right => do
      let left ← projectTerm ctx left
      let right ← projectTerm ctx right
      pure {
        positive := positive
        predicate := CoreSyntax.Search.PredicateKind.equal
        left := left
        right := right
      }
  | Atom.boolTerm term => do
      let left ← projectTerm ctx term
      pure {
        positive := positive
        predicate := CoreSyntax.Search.PredicateKind.boolHolds
        left := left
        right := left
      }
  | Atom.predicate predicate args => do
      let args ← projectTermList ctx args
      let right ← boolConst true
      pure {
        positive := positive
        predicate := CoreSyntax.Search.PredicateKind.predicate predicate
        left := tupleTerm predicate args
        right := right
      }

/-- 把 core literal 投影到搜索层 literal。 -/
def projectLiteral (ctx : Context) (literal : Literal) :
    ProjectM CoreSyntax.Search.Literal :=
  projectAtom ctx literal.positive literal.atom

/-- 把 core CNF 字句投影到搜索层字句。 -/
def projectClause (ctx : Context) (clause : Clause) :
    ProjectM CoreSyntax.Search.Clause := do
  let literals ←
    clause.toList.foldr
      (fun literal acc => do
        let literal ← projectLiteral ctx literal
        let rest ← acc
        pure (literal :: rest))
      (pure [])
  pure literals.toArray

/-- 把 core CNF 字句集投影到搜索层字句集。 -/
def projectClauseSet (ctx : Context) (clauses : ClauseSet) :
    ProjectM (Array CoreSyntax.Search.Clause) := do
  let clauseList ←
    clauses.toList.foldr
      (fun clause acc => do
        let clause ← projectClause ctx clause
        let rest ← acc
        pure (clause :: rest))
      (pure [])
  pure clauseList.toArray

/-- 按前束量词生成全称变量和 Skolem 项。 -/
def enterPrefix : Prefix → Context → ProjectM Context
  | [], ctx => pure ctx
  | Quantifier.forallE _ :: rest, ctx => do
      let term ← freshUniversal
      enterPrefix rest { bound := term :: ctx.bound, universals := term :: ctx.universals }
  | Quantifier.existsE _ :: rest, ctx => do
      let term ← freshSkolem ctx
      enterPrefix rest { ctx with bound := term :: ctx.bound }

/-- 完整投影结果。 -/
structure Result where
  foolPayload : FOOLClausePayload
  pipeline : Pipeline
  clausePipeline : Pipeline
  clauses : Array CoreSyntax.Search.Clause
  skolemTrace : Array CoreSyntax.Search.Intro
  auxBase : Nat
  deriving Repr, Lean.ToExpr

/-- 执行 core normal form 到搜索层字句的投影。 -/
def build? (source : Formula) (config : Config := {}) : Option Result := do
  if !source.check? then
    none
  else
  let foolPayload := FOOLClausePayload.build source (config := config)
  let pipeline := foolPayload.sourcePipeline
  let clausePipeline := foolPayload.clausePipeline
  let initial := initialState foolPayload.clauseSource
  let some ((_, clauses), state) :=
    (do
      let ctx ← enterPrefix clausePipeline.prenex.quantifiers {}
      let clauses ← projectClauseSet ctx clausePipeline.clauses
      pure (ctx, clauses)) initial
    | none
  some {
    foolPayload := foolPayload
    pipeline := pipeline
    clausePipeline := clausePipeline
    clauses := clauses
    skolemTrace := state.skolemTrace
    auxBase := state.auxBase
  }

/-- 投影结果的可计算 checker。 -/
def check (result : Result) : Bool :=
  Pipeline.check result.pipeline &&
    FOOLClausePayload.check result.foolPayload &&
    Pipeline.check result.clausePipeline &&
    SyntaxEq.formulaEq result.pipeline.source result.foolPayload.source &&
    SyntaxEq.formulaEq result.clausePipeline.source result.foolPayload.clauseSource &&
    match build? result.pipeline.source (config := result.pipeline.config) with
    | some expected =>
        CoreSyntax.Search.clauseArrayEq result.clauses expected.clauses &&
          result.skolemTrace == expected.skolemTrace &&
            result.auxBase == expected.auxBase &&
              FOOLClausePayload.check expected.foolPayload
    | none => false

end FirstOrderProjection

namespace FoolClausification

/-!
阶段 7 的 FOOL 子句化桥接层。

`FirstOrderProjection.Result` 仍然保存完整算法数据；这里额外给它一个公共证书 payload
名字，使 replay/scheduler 可以明确区分“FOOL 定义化子句化闭合”和普通一阶投影。
-/

/-- FOOL 定义化子句化进入公共证书层后的 payload。 -/
structure Payload where
  source : Formula
  projection : FirstOrderProjection.Result
  traceReplayChecked : Bool
  deriving Repr, Lean.ToExpr

namespace Payload

/-- 从投影结果构造 FOOL 子句化 bridge payload。 -/
def build (projection : FirstOrderProjection.Result) : Payload :=
  {
    source := projection.pipeline.source
    projection := projection
    traceReplayChecked := FirstOrderProjection.check projection
  }

/-- FOOL 子句化公共 payload 的可计算 checker。 -/
def check (payload : Payload) : Bool :=
  payload.traceReplayChecked &&
    FirstOrderProjection.check payload.projection &&
      SyntaxEq.formulaEq payload.source payload.projection.pipeline.source &&
        FirstOrderProjection.FOOLClausePayload.check payload.projection.foolPayload &&
          FirstOrderProjection.FormulaArgumentTrace.check
            payload.projection.foolPayload.argumentTrace

/-- 计算式构造 checked FOOL 子句化 payload。 -/
def mk? (projection : FirstOrderProjection.Result) :
    Option (Certificate.Checked Payload Payload.check) :=
  Certificate.Checked.mk? (check := Payload.check) (build projection)

/-- FOOL 子句化 bridge 的摘要。 -/
def stats (payload : Payload) : Certificate.Stats :=
  {
    steps :=
      payload.projection.pipeline.trace.steps.size +
        payload.projection.clausePipeline.trace.steps.size +
          payload.projection.foolPayload.argumentTrace.intros.size +
            payload.projection.skolemTrace.size
    clauses := payload.projection.clauses.size
    literals := payload.projection.pipeline.literalCount
    generated := payload.projection.foolPayload.argumentTrace.intros.size
    retained := payload.projection.foolPayload.argumentTrace.definitions.size
    verified := payload.projection.clausePipeline.trace.steps.size
    residuals := payload.projection.clauses.size
    fuel := payload.projection.pipeline.config.fuel
  }

/-- FOOL 子句化 bridge 中出现过的规则族标签。 -/
def ruleTags (payload : Payload) : Array Certificate.RuleTag :=
  Id.run do
    let mut tags := #[Certificate.RuleTag.foolClausification]
    if payload.projection.foolPayload.argumentTrace.intros.size != 0 then
      tags := Trace.pushCertificateTag tags Certificate.RuleTag.foolFormulaArgumentIntro
    if payload.projection.foolPayload.argumentTrace.definitions.size != 0 then
      tags := Trace.pushCertificateTag tags Certificate.RuleTag.foolBoolDefinition
    if payload.projection.skolemTrace.size != 0 then
      tags := Trace.pushCertificateTag tags Certificate.RuleTag.skolemization
    return tags

/-- FOOL 子句化 bridge 对应的公共证书节点。 -/
def toCoreNode (payload : Payload) (id : Certificate.NodeId := 0)
    (dependencies : Array Certificate.NodeId := #[])
    (closureKind? : Option Certificate.ClosureKind := some Certificate.ClosureKind.foolClausification) :
    Certificate.Node :=
  {
    id := id
    backend := Certificate.Backend.foolClausification
    phase := Certificate.Phase.foolClausification
    label := "checked FOOL definitional clausification"
    ruleTags := payload.ruleTags
    closureKind? := closureKind?
    stats := payload.stats
    dependencies := dependencies
  }

end Payload

/-- 对 FOOL 子句化 checked payload 做一层 replay 包装。 -/
structure ReplayPayload where
  checked : Certificate.Checked Payload Payload.check
  replayChecker : Bool

namespace ReplayPayload

/-- replay wrapper 的可计算 checker。 -/
def check (payload : ReplayPayload) : Bool :=
  Payload.check payload.checked.payload && payload.replayChecker

/-- 从 checked payload 构造 replay wrapper。 -/
def ofChecked (checked : Certificate.Checked Payload Payload.check) : ReplayPayload :=
  { checked := checked, replayChecker := Payload.check checked.payload }

end ReplayPayload

end FoolClausification


end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
