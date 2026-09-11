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
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort
def arrow? : CoreSort → Option (CoreSort × CoreSort)
  | CoreSort.arrow domain codomain => some (domain, codomain)
  | _ => none
end CoreSort
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
def foolOnly : Config := {
  beta := false
  eta := false
  extensionality := false
}
def firstOrderIdentity : Config := {
  beta := false
  eta := false
  extensionality := false
  fool := false
  connectiveSimp := false
  quantifierSimp := false
}
end Config
mutual
  def Term.foolFragment : Term → Bool
    | Term.bvar .. => true
    | Term.fvar .. => true
    | Term.app _ arguments => Term.foolFragmentList arguments
    | Term.apply .. => false
    | Term.bool .. => true
    | Term.notE body => Term.foolFragment body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => Term.foolFragment left && Term.foolFragment right
    | Term.quote formula => Formula.foolFragment formula
    | Term.lam .. => false
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.foolFragment condition &&
          Term.foolFragment thenTerm &&
            Term.foolFragment elseTerm
  def Formula.foolFragment : Formula → Bool
    | Formula.trueE => true
    | Formula.falseE => true
    | Formula.atom _ arguments => Term.foolFragmentList arguments
    | Formula.equal _ left right => Term.foolFragment left && Term.foolFragment right
    | Formula.boolTerm term => Term.foolFragment term
    | Formula.neg body => Formula.foolFragment body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Formula.foolFragment left && Formula.foolFragment right
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.foolFragment body
  def Term.foolFragmentList : List Term → Bool
    | [] => true
    | term :: rest => Term.foolFragment term && Term.foolFragmentList rest
end
namespace SyntaxEq
mutual
  def termEq : Term → Term → Bool
    | Term.bvar leftSort leftIndex, Term.bvar rightSort rightIndex => decide (leftSort = rightSort) && decide (leftIndex = rightIndex)
    | Term.fvar leftSort leftId, Term.fvar rightSort rightId => decide (leftSort = rightSort) && decide (leftId = rightId)
    | Term.app leftSymbol leftArgs, Term.app rightSymbol rightArgs => decide (leftSymbol = rightSymbol) && termListEq leftArgs rightArgs
    | Term.apply leftFn leftArg, Term.apply rightFn rightArg => termEq leftFn rightFn && termEq leftArg rightArg
    | Term.bool leftValue, Term.bool rightValue => decide (leftValue = rightValue)
    | Term.notE leftBody, Term.notE rightBody => termEq leftBody rightBody
    | Term.andE leftA leftB, Term.andE rightA rightB
    | Term.orE leftA leftB, Term.orE rightA rightB
    | Term.impE leftA leftB, Term.impE rightA rightB
    | Term.iffE leftA leftB, Term.iffE rightA rightB => termEq leftA rightA && termEq leftB rightB
    | Term.quote leftFormula, Term.quote rightFormula => formulaEq leftFormula rightFormula
    | Term.lam leftDomain leftCodomain leftBody, Term.lam rightDomain rightCodomain rightBody =>
        decide (leftDomain = rightDomain) && decide (leftCodomain = rightCodomain) &&
          termEq leftBody rightBody
    | Term.ite leftSort leftCond leftThen leftElse, Term.ite rightSort rightCond rightThen rightElse =>
        decide (leftSort = rightSort) && formulaEq leftCond rightCond &&
          termEq leftThen rightThen && termEq leftElse rightElse
    | _, _ => false
  def formulaEq : Formula → Formula → Bool
    | Formula.trueE, Formula.trueE => true
    | Formula.falseE, Formula.falseE => true
    | Formula.atom leftPredicate leftArgs, Formula.atom rightPredicate rightArgs => decide (leftPredicate = rightPredicate) && termListEq leftArgs rightArgs
    | Formula.equal leftSort leftLeft leftRight, Formula.equal rightSort rightLeft rightRight => decide (leftSort = rightSort) && termEq leftLeft rightLeft && termEq leftRight rightRight
    | Formula.boolTerm leftTerm, Formula.boolTerm rightTerm => termEq leftTerm rightTerm
    | Formula.neg leftBody, Formula.neg rightBody => formulaEq leftBody rightBody
    | Formula.imp leftA leftB, Formula.imp rightA rightB
    | Formula.conj leftA leftB, Formula.conj rightA rightB
    | Formula.disj leftA leftB, Formula.disj rightA rightB
    | Formula.iffE leftA leftB, Formula.iffE rightA rightB => formulaEq leftA rightA && formulaEq leftB rightB
    | Formula.forallE leftSort leftBody, Formula.forallE rightSort rightBody
    | Formula.existsE leftSort leftBody, Formula.existsE rightSort rightBody => decide (leftSort = rightSort) && formulaEq leftBody rightBody
    | _, _ => false
  def termListEq : List Term → List Term → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest => termEq left right && termListEq leftRest rightRest
    | _, _ => false
end
end SyntaxEq
mutual
  def Term.shiftAbove (amount cutoff : Nat) : Term → Term
    | Term.bvar sort index =>
        if index < cutoff then
          Term.bvar sort index
        else
          Term.bvar sort (index + amount)
    | Term.fvar sort id => Term.fvar sort id
    | Term.app symbol args => Term.app symbol (Term.shiftListAbove amount cutoff args)
    | Term.apply fn arg => Term.apply (Term.shiftAbove amount cutoff fn) (Term.shiftAbove amount cutoff arg)
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.shiftAbove amount cutoff body)
    | Term.andE left right => Term.andE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.orE left right => Term.orE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.impE left right => Term.impE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.iffE left right => Term.iffE (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Term.quote formula => Term.quote (Formula.shiftAbove amount cutoff formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.shiftAbove amount (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.shiftAbove amount cutoff condition) (Term.shiftAbove amount cutoff thenTerm) (Term.shiftAbove amount cutoff elseTerm)
  def Formula.shiftAbove (amount cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.shiftListAbove amount cutoff args)
    | Formula.equal sort left right => Formula.equal sort (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.shiftAbove amount cutoff term)
    | Formula.neg body => Formula.neg (Formula.shiftAbove amount cutoff body)
    | Formula.imp left right => Formula.imp (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.conj left right => Formula.conj (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.disj left right => Formula.disj (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.iffE left right => Formula.iffE (Formula.shiftAbove amount cutoff left) (Formula.shiftAbove amount cutoff right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.shiftAbove amount (cutoff + 1) body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.shiftAbove amount (cutoff + 1) body)
  def Term.shiftListAbove (amount cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.shiftAbove amount cutoff term :: Term.shiftListAbove amount cutoff rest
end
def Term.shift (amount : Nat) (term : Term) : Term :=
  Term.shiftAbove amount 0 term
def Formula.shift (amount : Nat) (formula : Formula) : Formula :=
  Formula.shiftAbove amount 0 formula
mutual
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
        Term.apply (Term.instantiateAt depth replacement fn) (Term.instantiateAt depth replacement arg)
    | Term.bool value => Term.bool value
    | Term.notE body => Term.notE (Term.instantiateAt depth replacement body)
    | Term.andE left right =>
        Term.andE (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
    | Term.orE left right =>
        Term.orE (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
    | Term.impE left right =>
        Term.impE (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
    | Term.iffE left right =>
        Term.iffE (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
    | Term.quote formula => Term.quote (Formula.instantiateAt depth replacement formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.instantiateAt (depth + 1) replacement body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.instantiateAt depth replacement condition) (Term.instantiateAt depth replacement thenTerm)
          (Term.instantiateAt depth replacement elseTerm)
  def Formula.instantiateAt (depth : Nat) (replacement : Term) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.instantiateListAt depth replacement args)
    | Formula.equal sort left right =>
        Formula.equal sort (Term.instantiateAt depth replacement left) (Term.instantiateAt depth replacement right)
    | Formula.boolTerm term => Formula.boolTerm (Term.instantiateAt depth replacement term)
    | Formula.neg body => Formula.neg (Formula.instantiateAt depth replacement body)
    | Formula.imp left right =>
        Formula.imp (Formula.instantiateAt depth replacement left) (Formula.instantiateAt depth replacement right)
    | Formula.conj left right =>
        Formula.conj (Formula.instantiateAt depth replacement left) (Formula.instantiateAt depth replacement right)
    | Formula.disj left right =>
        Formula.disj (Formula.instantiateAt depth replacement left) (Formula.instantiateAt depth replacement right)
    | Formula.iffE left right =>
        Formula.iffE (Formula.instantiateAt depth replacement left) (Formula.instantiateAt depth replacement right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.instantiateAt (depth + 1) replacement body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.instantiateAt (depth + 1) replacement body)
  def Term.instantiateListAt (depth : Nat) (replacement : Term) : List Term → List Term
    | [] => []
    | term :: rest =>
        Term.instantiateAt depth replacement term ::
          Term.instantiateListAt depth replacement rest
end
def Term.instantiate (replacement body : Term) : Term :=
  Term.instantiateAt 0 replacement body
def Formula.instantiate (replacement : Term) (body : Formula) : Formula :=
  Formula.instantiateAt 0 replacement body
namespace Eta
mutual
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
    | Term.iffE left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Term.quote formula => Formula.occursBVarAt depth formula
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.occursBVarAt depth condition ||
          Term.occursBVarAt depth thenTerm ||
            Term.occursBVarAt depth elseTerm
  def Formula.occursBVarAt (depth : Nat) : Formula → Bool
    | Formula.trueE => false
    | Formula.falseE => false
    | Formula.atom _ args => Term.occursBVarListAt depth args
    | Formula.equal _ left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Formula.boolTerm term => Term.occursBVarAt depth term
    | Formula.neg body => Formula.occursBVarAt depth body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Formula.occursBVarAt depth left || Formula.occursBVarAt depth right
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.occursBVarAt (depth + 1) body
  def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end
mutual
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
    | Term.andE left right => Term.andE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.orE left right => Term.orE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.impE left right => Term.impE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.iffE left right => Term.iffE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.quote formula => Term.quote (Formula.lowerAbove cutoff formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.lowerAbove (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.lowerAbove cutoff condition) (Term.lowerAbove cutoff thenTerm) (Term.lowerAbove cutoff elseTerm)
  def Formula.lowerAbove (cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.lowerListAbove cutoff args)
    | Formula.equal sort left right => Formula.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.lowerAbove cutoff term)
    | Formula.neg body => Formula.neg (Formula.lowerAbove cutoff body)
    | Formula.imp left right => Formula.imp (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.conj left right => Formula.conj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.disj left right => Formula.disj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.iffE left right => Formula.iffE (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.lowerAbove (cutoff + 1) body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.lowerAbove (cutoff + 1) body)
  def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end
def contract? (domain : CoreSort) : Term → Option Term
  | Term.apply fn (Term.bvar argSort 0) =>
      if argSort == domain && !Term.occursBVarAt 0 fn then
        some (Term.lowerAbove 0 fn)
      else
        none
  | _ => none
end Eta
mutual
  def normalizeTermWith (config : Config) : Nat → Term → Term
    | 0, term => term
    | _fuel + 1, Term.bvar sort index => Term.bvar sort index
    | _fuel + 1, Term.fvar sort id => Term.fvar sort id
    | fuel + 1, Term.app symbol args => Term.app symbol (normalizeTermListWith config fuel args)
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
          | Term.quote leftFormula, Term.quote rightFormula => normalizeTermWith config fuel (Term.quote (Formula.conj leftFormula rightFormula))
          | _, _ => if SyntaxEq.termEq left' right' then left' else Term.andE left' right'
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
          | Term.quote leftFormula, Term.quote rightFormula => normalizeTermWith config fuel (Term.quote (Formula.disj leftFormula rightFormula))
          | _, _ => if SyntaxEq.termEq left' right' then left' else Term.orE left' right'
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
            | Term.quote leftFormula, Term.quote rightFormula => normalizeTermWith config fuel (Term.quote (Formula.imp leftFormula rightFormula))
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
            | Term.quote leftFormula, Term.quote rightFormula => normalizeTermWith config fuel (Term.quote (Formula.iffE leftFormula rightFormula))
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
                | Term.bool true, Term.bool false => normalizeTermWith config fuel (Term.quote condition')
                | Term.bool false, Term.bool true => normalizeTermWith config fuel (Term.quote (Formula.neg condition'))
                | Term.bool true, _ => normalizeTermWith config fuel (Term.orE (Term.quote condition') elseTerm')
                | Term.bool false, _ =>
                    normalizeTermWith config fuel (Term.andE (Term.notE (Term.quote condition')) elseTerm')
                | _, Term.bool true => normalizeTermWith config fuel (Term.impE (Term.quote condition') thenTerm')
                | _, Term.bool false => normalizeTermWith config fuel (Term.andE (Term.quote condition') thenTerm')
                | _, _ => Term.ite sort condition' thenTerm' elseTerm'
              else
                Term.ite sort condition' thenTerm' elseTerm'
        else
          Term.ite sort condition' thenTerm' elseTerm'
  def normalizeFormulaWith (config : Config) : Nat → Formula → Formula
    | 0, formula => formula
    | _fuel + 1, Formula.trueE => Formula.trueE
    | _fuel + 1, Formula.falseE => Formula.falseE
    | fuel + 1, Formula.atom predicate args => Formula.atom predicate (normalizeTermListWith config fuel args)
    | fuel + 1, Formula.equal sort left right =>
        let left' := normalizeTermWith config fuel left
        let right' := normalizeTermWith config fuel right
        if config.connectiveSimp && SyntaxEq.termEq left' right' then
          Formula.trueE
        else if config.extensionality then
          match CoreSort.arrow? sort with
          | some (domain, codomain) =>
              normalizeFormulaWith config fuel
                (Formula.forallE domain (Formula.equal codomain (Term.apply (Term.shift 1 left') (Term.bvar domain 0)) (Term.apply (Term.shift 1 right') (Term.bvar domain 0))))
          | none =>
              if config.fool && sort == CoreSort.bool then
                match left', right' with
                | Term.bool true, _ => normalizeFormulaWith config fuel (Formula.boolTerm right')
                | _, Term.bool true => normalizeFormulaWith config fuel (Formula.boolTerm left')
                | Term.bool false, _ => normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm right'))
                | _, Term.bool false => normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm left'))
                | Term.quote leftFormula, Term.quote rightFormula => normalizeFormulaWith config fuel (Formula.iffE leftFormula rightFormula)
                | _, _ =>
                    normalizeFormulaWith config fuel (Formula.iffE (Formula.boolTerm left') (Formula.boolTerm right'))
              else
                Formula.equal sort left' right'
        else if config.fool && sort == CoreSort.bool then
          match left', right' with
          | Term.bool true, _ => normalizeFormulaWith config fuel (Formula.boolTerm right')
          | _, Term.bool true => normalizeFormulaWith config fuel (Formula.boolTerm left')
          | Term.bool false, _ => normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm right'))
          | _, Term.bool false => normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm left'))
          | Term.quote leftFormula, Term.quote rightFormula => normalizeFormulaWith config fuel (Formula.iffE leftFormula rightFormula)
          | _, _ =>
              normalizeFormulaWith config fuel (Formula.iffE (Formula.boolTerm left') (Formula.boolTerm right'))
        else
          Formula.equal sort left' right'
    | fuel + 1, Formula.boolTerm term =>
        let term' := normalizeTermWith config fuel term
        if config.fool then
          match term' with
          | Term.bool true => Formula.trueE
          | Term.bool false => Formula.falseE
          | Term.notE body => normalizeFormulaWith config fuel (Formula.neg (Formula.boolTerm body))
          | Term.andE left right =>
              normalizeFormulaWith config fuel (Formula.conj (Formula.boolTerm left) (Formula.boolTerm right))
          | Term.orE left right =>
              normalizeFormulaWith config fuel (Formula.disj (Formula.boolTerm left) (Formula.boolTerm right))
          | Term.impE left right =>
              normalizeFormulaWith config fuel (Formula.imp (Formula.boolTerm left) (Formula.boolTerm right))
          | Term.iffE left right =>
              normalizeFormulaWith config fuel (Formula.iffE (Formula.boolTerm left) (Formula.boolTerm right))
          | Term.quote formula => normalizeFormulaWith config fuel formula
          | Term.ite sort condition thenTerm elseTerm =>
              if sort == CoreSort.bool then
                normalizeFormulaWith config fuel
                  (Formula.disj (Formula.conj condition (Formula.boolTerm thenTerm)) (Formula.conj (Formula.neg condition) (Formula.boolTerm elseTerm)))
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
          | _, _ => if SyntaxEq.formulaEq left' right' then Formula.trueE else Formula.imp left' right'
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
          | _, _ => if SyntaxEq.formulaEq left' right' then left' else Formula.conj left' right'
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
          | _, _ => if SyntaxEq.formulaEq left' right' then left' else Formula.disj left' right'
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
          | _, _ => if SyntaxEq.formulaEq left' right' then Formula.trueE else Formula.iffE left' right'
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
  def normalizeTermListWith (config : Config) : Nat → List Term → List Term
    | 0, terms => terms
    | _fuel + 1, [] => []
    | fuel + 1, term :: rest => normalizeTermWith config fuel term :: normalizeTermListWith config fuel rest
end
def normalizeTerm (term : Term) (config : Config := {}) : Term :=
  normalizeTermWith config config.fuel term
def normalizeFormula (formula : Formula) (config : Config := {}) : Formula :=
  normalizeFormulaWith config config.fuel formula
def normalizeTermList (terms : List Term) (config : Config := {}) : List Term :=
  normalizeTermListWith config config.fuel terms
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
        | Term.quote leftFormula, Term.quote rightFormula => some (StepRule.foolQuote, Term.quote (Formula.conj leftFormula rightFormula))
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
        | Term.quote leftFormula, Term.quote rightFormula => some (StepRule.foolQuote, Term.quote (Formula.disj leftFormula rightFormula))
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
        | Term.quote leftFormula, Term.quote rightFormula => some (StepRule.foolQuote, Term.quote (Formula.imp leftFormula rightFormula))
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
        | Term.quote leftFormula, Term.quote rightFormula => some (StepRule.foolQuote, Term.quote (Formula.iffE leftFormula rightFormula))
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
            | CoreSort.bool, Term.bool true, Term.bool false => some (StepRule.boolIte, Term.quote condition)
            | CoreSort.bool, Term.bool false, Term.bool true => some (StepRule.boolIte, Term.quote (Formula.neg condition))
            | CoreSort.bool, Term.bool true, _ => some (StepRule.boolIte, Term.orE (Term.quote condition) elseTerm)
            | CoreSort.bool, Term.bool false, _ =>
                some ( StepRule.boolIte, Term.andE (Term.quote (Formula.neg condition)) elseTerm )
            | CoreSort.bool, _, Term.bool true => some (StepRule.boolIte, Term.impE (Term.quote condition) thenTerm)
            | CoreSort.bool, _, Term.bool false => some (StepRule.boolIte, Term.andE (Term.quote condition) thenTerm)
            | _, _, _ => none
          else
            none
  | _ => none
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
                ( StepRule.functionExtensionality, Formula.forallE domain (Formula.equal codomain (Term.apply shiftedLeft binder) (Term.apply shiftedRight binder)) )
            else
              none
        | CoreSort.bool =>
            if config.fool then
              match left, right with
              | Term.bool true, _ => some (StepRule.boolEquality, Formula.boolTerm right)
              | _, Term.bool true => some (StepRule.boolEquality, Formula.boolTerm left)
              | Term.bool false, _ => some (StepRule.boolEquality, Formula.neg (Formula.boolTerm right))
              | _, Term.bool false => some (StepRule.boolEquality, Formula.neg (Formula.boolTerm left))
              | Term.quote leftFormula, Term.quote rightFormula => some (StepRule.boolEquality, Formula.iffE leftFormula rightFormula)
              | _, _ =>
                  some ( StepRule.boolEquality, Formula.iffE (Formula.boolTerm left) (Formula.boolTerm right) )
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
            some ( StepRule.foolBoolTerm, Formula.conj (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.orE left right =>
            some ( StepRule.foolBoolTerm, Formula.disj (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.impE left right =>
            some ( StepRule.foolBoolTerm, Formula.imp (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.iffE left right =>
            some ( StepRule.foolBoolTerm, Formula.iffE (Formula.boolTerm left) (Formula.boolTerm right) )
        | Term.quote formula => some (StepRule.foolBoolTerm, formula)
        | Term.ite CoreSort.bool condition thenTerm elseTerm =>
            some
              ( StepRule.boolIte, Formula.disj (Formula.conj condition (Formula.boolTerm thenTerm)) (Formula.conj (Formula.neg condition) (Formula.boolTerm elseTerm)) )
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
inductive TraceExpr where
  | term (term : Term)
  | formula (formula : Formula)
  deriving Repr, Lean.ToExpr
namespace TraceExpr
def eq : TraceExpr → TraceExpr → Bool
  | TraceExpr.term left, TraceExpr.term right => SyntaxEq.termEq left right
  | TraceExpr.formula left, TraceExpr.formula right => SyntaxEq.formulaEq left right
  | _, _ => false
def size : TraceExpr → Nat
  | TraceExpr.term t => t.size
  | TraceExpr.formula p => p.size
def check? : TraceExpr → Bool
  | TraceExpr.term t => t.wellScoped? && t.inferSort?.isSome
  | TraceExpr.formula p => p.check?
def foolFragment : TraceExpr → Bool
  | TraceExpr.term t => Term.foolFragment t
  | TraceExpr.formula p => Formula.foolFragment p
def normalize (config : Config) : TraceExpr → TraceExpr
  | TraceExpr.term t => TraceExpr.term (normalizeTerm t (config := config))
  | TraceExpr.formula p => TraceExpr.formula (normalizeFormula p (config := config))
end TraceExpr
mutual
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
                | some (rule, elseTerm') => some (rule, Term.ite sort condition thenTerm elseTerm')
                | none =>
                    rewriteRootTerm? config (Term.ite sort condition thenTerm elseTerm)
  def rewriteOnceTermList? (config : Config) : List Term → Option (StepRule × List Term)
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
def rewriteOnce? (config : Config) : TraceExpr → Option (StepRule × TraceExpr)
  | TraceExpr.term t => do
      let (rule, t') ← rewriteOnceTerm? config t
      some (rule, TraceExpr.term t')
  | TraceExpr.formula p => do
      let (rule, p') ← rewriteOnceFormula? config p
      some (rule, TraceExpr.formula p')
end TraceExpr
structure Step where
  rule : StepRule
  before : TraceExpr
  after : TraceExpr
  deriving Repr, Lean.ToExpr
namespace Step
def check (config : Config) (step : Step) : Bool :=
  step.before.check? &&
    step.after.check? &&
      match TraceExpr.rewriteOnce? config step.before with
      | some (rule, after) => rule == step.rule && TraceExpr.eq after step.after
      | none => false
def foolCheck (step : Step) : Bool :=
  step.before.foolFragment &&
    step.after.foolFragment &&
      step.check Config.foolOnly
end Step
structure Trace where
  source : TraceExpr
  target : TraceExpr
  steps : Array Step
  deriving Repr, Lean.ToExpr
namespace Trace
def replay? (config : Config) (current : TraceExpr) : List Step → Option TraceExpr
  | [] => some current
  | step :: rest =>
      if TraceExpr.eq current step.before && step.check config then
        replay? config step.after rest
      else
        none
def check (config : Config) (trace : Trace) : Bool :=
  trace.source.check? &&
    trace.target.check? &&
      match replay? config trace.source trace.steps.toList with
      | some target =>
          TraceExpr.eq target trace.target &&
            TraceExpr.eq target (TraceExpr.normalize config trace.source)
      | none => false
def foolCheck (trace : Trace) : Bool :=
  trace.source.foolFragment &&
    trace.target.foolFragment &&
      trace.steps.all Step.foolCheck &&
        trace.check Config.foolOnly
def containsRule (rule : StepRule) (trace : Trace) : Bool :=
  trace.steps.any (fun step => step.rule == rule)
def containsCertificateTag (tags : Array Certificate.RuleTag) (tag : Certificate.RuleTag) : Bool :=
  tags.any (fun existing => existing == tag)
def pushCertificateTag (tags : Array Certificate.RuleTag) (tag : Certificate.RuleTag) : Array Certificate.RuleTag :=
  if containsCertificateTag tags tag then tags else tags.push tag
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
def certificateTags (trace : Trace) : Array Certificate.RuleTag :=
  trace.steps.foldl (fun tags step => pushCertificateTag tags (certificateTagOfRule step.rule))
    #[Certificate.RuleTag.coreNormalFormTrace]
def certificateStats (config : Config) (trace : Trace) : Certificate.Stats :=
  {
    steps := trace.steps.size
    generated := trace.source.size
    retained := trace.target.size
    verified := trace.steps.size
    fuel := config.fuel * (trace.source.size + 1) + 1
  }
def fuel (config : Config) (source : TraceExpr) : Nat :=
  config.fuel * (source.size + 1) + 1
partial def buildLoop (config : Config) :
    Nat → TraceExpr → Array Step → TraceExpr × Array Step
  | 0, current, steps => (current, steps)
  | fuel + 1, current, steps =>
      match TraceExpr.rewriteOnce? config current with
      | some (rule, next) => buildLoop config fuel next (steps.push { rule := rule, before := current, after := next })
      | none => (current, steps)
def build (source : TraceExpr) (config : Config := {}) : Trace :=
  let (target, steps) := buildLoop config (fuel config source) source #[]
  { source := source, target := target, steps := steps }
def ofTerm (source : Term) (config : Config := {}) : Trace :=
  build (TraceExpr.term source) (config := config)
def ofFormula (source : Formula) (config : Config := {}) : Trace :=
  build (TraceExpr.formula source) (config := config)
structure SoundnessPayload where
  config : Config
  trace : Trace
  deriving Repr, Lean.ToExpr
namespace SoundnessPayload
def check (payload : SoundnessPayload) : Bool :=
  Trace.check payload.config payload.trace
def ofTrace (config : Config) (trace : Trace) : SoundnessPayload :=
  { config := config, trace := trace }
def mk? (config : Config) (trace : Trace) : Option (Certificate.Checked SoundnessPayload SoundnessPayload.check) :=
  Certificate.Checked.mk? (check := SoundnessPayload.check) (ofTrace config trace)
def toCoreNode (payload : SoundnessPayload) (id : Certificate.NodeId := 0) (dependencies : Array Certificate.NodeId := #[])
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
structure TermPayload where
  config : Config
  source : Term
  normal : Term
  trace : Trace
  sourceSize : Nat
  normalSize : Nat
  deriving Repr, Lean.ToExpr
namespace TermPayload
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
def check (payload : TermPayload) : Bool :=
  payload.source.wellScoped? && (match payload.source.inferSort?, payload.normal.inferSort? with
    | some sourceSort, some normalSort => sourceSort == normalSort
    | _, _ => false) &&
      Trace.check payload.config payload.trace &&
        TraceExpr.eq payload.trace.source (TraceExpr.term payload.source) &&
          TraceExpr.eq payload.trace.target (TraceExpr.term payload.normal) &&
            SyntaxEq.termEq payload.normal (normalizeTerm payload.source (config := payload.config)) &&
              payload.sourceSize == payload.source.size &&
                payload.normalSize == payload.normal.size
end TermPayload
structure FormulaPayload where
  config : Config
  source : Formula
  normal : Formula
  trace : Trace
  sourceSize : Nat
  normalSize : Nat
  deriving Repr, Lean.ToExpr
namespace FormulaPayload
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
def check (payload : FormulaPayload) : Bool :=
  payload.source.check? &&
    payload.normal.check? &&
      Trace.check payload.config payload.trace &&
        TraceExpr.eq payload.trace.source (TraceExpr.formula payload.source) &&
          TraceExpr.eq payload.trace.target (TraceExpr.formula payload.normal) &&
            SyntaxEq.formulaEq payload.normal (normalizeFormula payload.source (config := payload.config)) &&
              payload.sourceSize == payload.source.size &&
                payload.normalSize == payload.normal.size
end FormulaPayload
namespace Search
def normalizeLiteralFormula (literal : CoreSyntax.Search.Literal) (config : Config := {}) :
    Formula :=
  normalizeFormula literal.toCoreFormula (config := config)
def normalizeClauseFormula (clause : CoreSyntax.Search.Clause) (config : Config := {}) :
    Formula :=
  normalizeFormula clause.toCoreFormula (config := config)
structure ClausePayload where
  config : Config
  source : CoreSyntax.Search.Clause
  normal : Formula
  deriving Repr, Lean.ToExpr
namespace ClausePayload
def build (source : CoreSyntax.Search.Clause) (config : Config := {}) : ClausePayload :=
  {
    config := config
    source := source
    normal := normalizeClauseFormula source (config := config)
  }
def check (payload : ClausePayload) : Bool :=
  SyntaxEq.formulaEq payload.normal (normalizeClauseFormula payload.source (config := payload.config))
end ClausePayload
end Search
/-!
## Core NNF 与前束/CNF 视图
这一层是后续 FOOL/lambda 叠加演算真正应该消费的 normal form。它不再复用旧 MF1
`Formula` 上的兼容 NNF，而是直接在 `CoreSyntax.Formula` 上给出可复算数据。
-/
inductive Atom where
  | predicate (predicate : PredicateSymbol) (args : List Term)
  | equal (sort : CoreSort) (left right : Term)
  | boolTerm (term : Term)
  deriving Repr, Inhabited, Lean.ToExpr
namespace Atom
def size : Atom → Nat
  | Atom.predicate _ args => args.foldl (fun acc term => acc + term.size) 1
  | Atom.equal _ left right => left.size + right.size + 1
  | Atom.boolTerm term => term.size + 1
def toFormula : Atom → Formula
  | Atom.predicate predSym args => Formula.atom predSym args
  | Atom.equal sort left right => Formula.equal sort left right
  | Atom.boolTerm term => Formula.boolTerm term
end Atom
structure Literal where
  positive : Bool
  atom : Atom
  deriving Repr, Inhabited, Lean.ToExpr
namespace Literal
def size (literal : Literal) : Nat :=
  literal.atom.size + 1
def toFormula (literal : Literal) : Formula :=
  if literal.positive then literal.atom.toFormula else Formula.neg literal.atom.toFormula
def negate (literal : Literal) : Literal :=
  { literal with positive := !literal.positive }
end Literal
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
partial def size : Nnf → Nat
  | trueE => 1
  | falseE => 1
  | lit literal => literal.size + 1
  | conj left right => left.size + right.size + 1
  | disj left right => left.size + right.size + 1
  | forallE _ body => body.size + 1
  | existsE _ body => body.size + 1
partial def literalCount : Nnf → Nat
  | trueE => 0
  | falseE => 0
  | lit _ => 1
  | conj left right => left.literalCount + right.literalCount
  | disj left right => left.literalCount + right.literalCount
  | forallE _ body => body.literalCount
  | existsE _ body => body.literalCount
def quantifierCount : Nnf → Nat
  | trueE => 0
  | falseE => 0
  | lit _ => 0
  | conj left right => left.quantifierCount + right.quantifierCount
  | disj left right => left.quantifierCount + right.quantifierCount
  | forallE _ body => body.quantifierCount + 1
  | existsE _ body => body.quantifierCount + 1
def quantifierFree (nnf : Nnf) : Bool :=
  nnf.quantifierCount == 0
def toFormula : Nnf → Formula
  | trueE => Formula.trueE
  | falseE => Formula.falseE
  | lit literal => literal.toFormula
  | conj left right => Formula.conj left.toFormula right.toFormula
  | disj left right => Formula.disj left.toFormula right.toFormula
  | forallE sort body => Formula.forallE sort body.toFormula
  | existsE sort body => Formula.existsE sort body.toFormula
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
  def atomEq : Atom → Atom → Bool
    | Atom.predicate leftPredicate leftArgs, Atom.predicate rightPredicate rightArgs => decide (leftPredicate = rightPredicate) && termListEq leftArgs rightArgs
    | Atom.equal leftSort leftLeft leftRight, Atom.equal rightSort rightLeft rightRight => decide (leftSort = rightSort) && termEq leftLeft rightLeft && termEq leftRight rightRight
    | Atom.boolTerm leftTerm, Atom.boolTerm rightTerm => termEq leftTerm rightTerm
    | _, _ => false
  def literalEq (left right : Literal) : Bool :=
    decide (left.positive = right.positive) && atomEq left.atom right.atom
  def nnfEq : Nnf → Nnf → Bool
    | Nnf.trueE, Nnf.trueE => true
    | Nnf.falseE, Nnf.falseE => true
    | Nnf.lit left, Nnf.lit right => literalEq left right
    | Nnf.conj leftA leftB, Nnf.conj rightA rightB
    | Nnf.disj leftA leftB, Nnf.disj rightA rightB => nnfEq leftA rightA && nnfEq leftB rightB
    | Nnf.forallE leftSort leftBody, Nnf.forallE rightSort rightBody
    | Nnf.existsE leftSort leftBody, Nnf.existsE rightSort rightBody => decide (leftSort = rightSort) && nnfEq leftBody rightBody
    | _, _ => false
  def literalListEq : List Literal → List Literal → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest => literalEq left right && literalListEq leftRest rightRest
    | _, _ => false
end
end SyntaxEq
mutual
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
    | Term.iffE left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Term.quote formula => Formula.occursBVarAt depth formula
    | Term.lam _ _ body => Term.occursBVarAt (depth + 1) body
    | Term.ite _ condition thenTerm elseTerm =>
        Formula.occursBVarAt depth condition ||
          Term.occursBVarAt depth thenTerm ||
            Term.occursBVarAt depth elseTerm
  def Formula.occursBVarAt (depth : Nat) : Formula → Bool
    | Formula.trueE => false
    | Formula.falseE => false
    | Formula.atom _ args => Term.occursBVarListAt depth args
    | Formula.equal _ left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
    | Formula.boolTerm term => Term.occursBVarAt depth term
    | Formula.neg body => Formula.occursBVarAt depth body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => Formula.occursBVarAt depth left || Formula.occursBVarAt depth right
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.occursBVarAt (depth + 1) body
  def Term.occursBVarListAt (depth : Nat) : List Term → Bool
    | [] => false
    | term :: rest => Term.occursBVarAt depth term || Term.occursBVarListAt depth rest
end
mutual
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
    | Term.andE left right => Term.andE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.orE left right => Term.orE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.impE left right => Term.impE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.iffE left right => Term.iffE (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Term.quote formula => Term.quote (Formula.lowerAbove cutoff formula)
    | Term.lam domain codomain body => Term.lam domain codomain (Term.lowerAbove (cutoff + 1) body)
    | Term.ite sort condition thenTerm elseTerm =>
        Term.ite sort (Formula.lowerAbove cutoff condition) (Term.lowerAbove cutoff thenTerm) (Term.lowerAbove cutoff elseTerm)
  def Formula.lowerAbove (cutoff : Nat) : Formula → Formula
    | Formula.trueE => Formula.trueE
    | Formula.falseE => Formula.falseE
    | Formula.atom predicate args => Formula.atom predicate (Term.lowerListAbove cutoff args)
    | Formula.equal sort left right => Formula.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
    | Formula.boolTerm term => Formula.boolTerm (Term.lowerAbove cutoff term)
    | Formula.neg body => Formula.neg (Formula.lowerAbove cutoff body)
    | Formula.imp left right => Formula.imp (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.conj left right => Formula.conj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.disj left right => Formula.disj (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.iffE left right => Formula.iffE (Formula.lowerAbove cutoff left) (Formula.lowerAbove cutoff right)
    | Formula.forallE sort body => Formula.forallE sort (Formula.lowerAbove (cutoff + 1) body)
    | Formula.existsE sort body => Formula.existsE sort (Formula.lowerAbove (cutoff + 1) body)
  def Term.lowerListAbove (cutoff : Nat) : List Term → List Term
    | [] => []
    | term :: rest => Term.lowerAbove cutoff term :: Term.lowerListAbove cutoff rest
end
namespace Atom
def occursBVarAt (depth : Nat) : Atom → Bool
  | Atom.predicate _ args => Term.occursBVarListAt depth args
  | Atom.equal _ left right => Term.occursBVarAt depth left || Term.occursBVarAt depth right
  | Atom.boolTerm term => Term.occursBVarAt depth term
def shiftAbove (amount cutoff : Nat) : Atom → Atom
  | Atom.predicate predSym args => Atom.predicate predSym (Term.shiftListAbove amount cutoff args)
  | Atom.equal sort left right => Atom.equal sort (Term.shiftAbove amount cutoff left) (Term.shiftAbove amount cutoff right)
  | Atom.boolTerm term => Atom.boolTerm (Term.shiftAbove amount cutoff term)
def lowerAbove (cutoff : Nat) : Atom → Atom
  | Atom.predicate predSym args => Atom.predicate predSym (Term.lowerListAbove cutoff args)
  | Atom.equal sort left right => Atom.equal sort (Term.lowerAbove cutoff left) (Term.lowerAbove cutoff right)
  | Atom.boolTerm term => Atom.boolTerm (Term.lowerAbove cutoff term)
end Atom
namespace Literal
def occursBVarAt (depth : Nat) (literal : Literal) : Bool :=
  literal.atom.occursBVarAt depth
def shiftAbove (amount cutoff : Nat) (literal : Literal) : Literal :=
  { literal with atom := literal.atom.shiftAbove amount cutoff }
def lowerAbove (cutoff : Nat) (literal : Literal) : Literal :=
  { literal with atom := literal.atom.lowerAbove cutoff }
end Literal
namespace Nnf
def occursBVarAt (depth : Nat) : Nnf → Bool
  | trueE => false
  | falseE => false
  | lit literal => literal.occursBVarAt depth
  | conj left right => left.occursBVarAt depth || right.occursBVarAt depth
  | disj left right => left.occursBVarAt depth || right.occursBVarAt depth
  | forallE _ body => body.occursBVarAt (depth + 1)
  | existsE _ body => body.occursBVarAt (depth + 1)
def usesCurrentBinder (nnf : Nnf) : Bool :=
  nnf.occursBVarAt 0
def shiftAbove (amount cutoff : Nat) : Nnf → Nnf
  | trueE => trueE
  | falseE => falseE
  | lit literal => lit (literal.shiftAbove amount cutoff)
  | conj left right => conj (left.shiftAbove amount cutoff) (right.shiftAbove amount cutoff)
  | disj left right => disj (left.shiftAbove amount cutoff) (right.shiftAbove amount cutoff)
  | forallE sort body => forallE sort (body.shiftAbove amount (cutoff + 1))
  | existsE sort body => existsE sort (body.shiftAbove amount (cutoff + 1))
def shift (amount : Nat) (nnf : Nnf) : Nnf :=
  nnf.shiftAbove amount 0
def lowerAbove (cutoff : Nat) : Nnf → Nnf
  | trueE => trueE
  | falseE => falseE
  | lit literal => lit (literal.lowerAbove cutoff)
  | conj left right => conj (left.lowerAbove cutoff) (right.lowerAbove cutoff)
  | disj left right => disj (left.lowerAbove cutoff) (right.lowerAbove cutoff)
  | forallE sort body => forallE sort (body.lowerAbove (cutoff + 1))
  | existsE sort body => existsE sort (body.lowerAbove (cutoff + 1))
def dropCurrentBinder (body : Nnf) : Nnf :=
  body.lowerAbove 0
end Nnf
inductive Polarity where
  | positive
  | negative
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace Polarity
def flip : Polarity → Polarity
  | positive => negative
  | negative => positive
def literal (polarity : Polarity) (atom : Atom) : Literal :=
  { positive := polarity == positive, atom := atom }
end Polarity
def toNnfWith : Polarity → Formula → Nnf
  | Polarity.positive, Formula.trueE => Nnf.trueE
  | Polarity.negative, Formula.trueE => Nnf.falseE
  | Polarity.positive, Formula.falseE => Nnf.falseE
  | Polarity.negative, Formula.falseE => Nnf.trueE
  | polarity, Formula.atom predicate args => Nnf.lit (polarity.literal (Atom.predicate predicate args))
  | polarity, Formula.equal sort left right => Nnf.lit (polarity.literal (Atom.equal sort left right))
  | polarity, Formula.boolTerm term => Nnf.lit (polarity.literal (Atom.boolTerm term))
  | polarity, Formula.neg body => toNnfWith polarity.flip body
  | Polarity.positive, Formula.imp left right => Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.imp left right => Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.conj left right => Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.conj left right => Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.disj left right => Nnf.disj (toNnfWith Polarity.positive left) (toNnfWith Polarity.positive right)
  | Polarity.negative, Formula.disj left right => Nnf.conj (toNnfWith Polarity.negative left) (toNnfWith Polarity.negative right)
  | Polarity.positive, Formula.iffE left right =>
      Nnf.conj (Nnf.disj (toNnfWith Polarity.negative left) (toNnfWith Polarity.positive right))
        (Nnf.disj (toNnfWith Polarity.negative right) (toNnfWith Polarity.positive left))
  | Polarity.negative, Formula.iffE left right =>
      Nnf.disj (Nnf.conj (toNnfWith Polarity.positive left) (toNnfWith Polarity.negative right))
        (Nnf.conj (toNnfWith Polarity.positive right) (toNnfWith Polarity.negative left))
  | Polarity.positive, Formula.forallE sort body => Nnf.forallE sort (toNnfWith Polarity.positive body)
  | Polarity.negative, Formula.forallE sort body => Nnf.existsE sort (toNnfWith Polarity.negative body)
  | Polarity.positive, Formula.existsE sort body => Nnf.existsE sort (toNnfWith Polarity.positive body)
  | Polarity.negative, Formula.existsE sort body => Nnf.forallE sort (toNnfWith Polarity.negative body)
def toNnf (formula : Formula) (config : Config := {}) : Nnf :=
  toNnfWith Polarity.positive (normalizeFormula formula (config := config))
inductive Quantifier where
  | forallE (sort : CoreSort)
  | existsE (sort : CoreSort)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace Quantifier
def sort : Quantifier → CoreSort
  | forallE sort => sort
  | existsE sort => sort
def wrap (quantifier : Quantifier) (body : Nnf) : Nnf :=
  match quantifier with
  | forallE sort => Nnf.forallE sort body
  | existsE sort => Nnf.existsE sort body
end Quantifier
abbrev Prefix := List Quantifier
namespace Prefix
def boundSorts (qs : Prefix) : List CoreSort :=
  qs.foldl (fun bound quantifier => quantifier.sort :: bound) []
def wrap : Prefix → Nnf → Nnf
  | [], matrix => matrix
  | quantifier :: rest, matrix => quantifier.wrap (wrap rest matrix)
def eq : Prefix → Prefix → Bool
  | [], [] => true
  | Quantifier.forallE left :: leftRest, Quantifier.forallE right :: rightRest => left == right && eq leftRest rightRest
  | Quantifier.existsE left :: leftRest, Quantifier.existsE right :: rightRest => left == right && eq leftRest rightRest
  | _, _ => false
end Prefix
structure PrenexView where
  quantifiers : Prefix
  matrix : Nnf
  deriving Repr, Inhabited, Lean.ToExpr
namespace PrenexView
def toNnf (view : PrenexView) : Nnf :=
  view.quantifiers.wrap view.matrix
def toFormula (view : PrenexView) : Formula :=
  view.toNnf.toFormula
def eq (left right : PrenexView) : Bool :=
  Prefix.eq left.quantifiers right.quantifiers && SyntaxEq.nnfEq left.matrix right.matrix
def combine (mk : Nnf → Nnf → Nnf) (left right : PrenexView) : PrenexView :=
  let leftDepth := left.quantifiers.length
  let rightDepth := right.quantifiers.length
  {
    quantifiers := left.quantifiers ++ right.quantifiers
    matrix :=
      mk (left.matrix.shift rightDepth) (right.matrix.shiftAbove leftDepth rightDepth)
  }
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
abbrev Clause := Array Literal
abbrev ClauseSet := Array Clause
namespace Clause
def eq (left right : Clause) : Bool :=
  SyntaxEq.literalListEq left.toList right.toList
def literalCount (clause : Clause) : Nat :=
  clause.size
def toFormula (clause : Clause) : Formula :=
  Formula.disjunctionList (clause.toList.map Literal.toFormula)
end Clause
namespace ClauseSet
def eq (left right : ClauseSet) : Bool :=
  let rec go : List Clause → List Clause → Bool
    | [], [] => true
    | leftClause :: leftRest, rightClause :: rightRest => Clause.eq leftClause rightClause && go leftRest rightRest
    | _, _ => false
  go left.toList right.toList
def containsEmpty (clauses : ClauseSet) : Bool :=
  clauses.any (fun clause => clause.isEmpty)
def conj (left right : ClauseSet) : ClauseSet :=
  left ++ right
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
def literalCount (clauses : ClauseSet) : Nat :=
  Id.run do
    let mut count := 0
    for clause in clauses do
      count := count + clause.literalCount
    return count
def toFormula (clauses : ClauseSet) : Formula :=
  let rec go : List Clause → Formula
    | [] => Formula.trueE
    | [clause] => clause.toFormula
    | clause :: rest => Formula.conj clause.toFormula (go rest)
  go clauses.toList
end ClauseSet
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
def cnfOfMatrix (matrix : Nnf) : ClauseSet := (cnfOfMatrix? matrix).getD #[#[]]
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
      PrenexView.eq payload.prenex expected.prenex && (match cnfOfMatrix? payload.prenex.matrix with
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
structure State where
  nextVar : Nat
  nextSkolem : Nat
  auxBase : Nat
  skolemTrace : Array CoreSyntax.Search.Intro := #[]
  deriving Repr, Lean.ToExpr
structure Context where
  bound : List CoreSyntax.Search.Term := []
  universals : List CoreSyntax.Search.Term := []
  deriving Repr, Inhabited, BEq, Lean.ToExpr
abbrev ProjectM := StateT State Option
def fail {α : Type} : ProjectM α :=
  fun _ => none
def lookupList? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => lookupList? tail index
def symbolKindOfRole : FunctionRole → CoreSyntax.Search.SymbolKind
  | FunctionRole.parameter => CoreSyntax.Search.SymbolKind.parameter
  | FunctionRole.skolem => CoreSyntax.Search.SymbolKind.skolem
  | FunctionRole.definition => CoreSyntax.Search.SymbolKind.definition
  | FunctionRole.choice => CoreSyntax.Search.SymbolKind.choice
  | FunctionRole.builtin => CoreSyntax.Search.SymbolKind.builtin
  | FunctionRole.extensionalWitness => CoreSyntax.Search.SymbolKind.extensionalWitness
def functionSymbol (symbol : FunctionSymbol) : CoreSyntax.Search.FunctionSymbol :=
  {
    id := symbol.id
    arity := symbol.arity
    kind := symbolKindOfRole symbol.role
    inputSorts := symbol.inputSorts
    outputSort := symbol.outputSort
  }
namespace Aux
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
def auxOutputSort (offset : Nat) : CoreSort :=
  if offset == Aux.boolFalse || offset == Aux.boolTrue ||
      offset == Aux.notE || offset == Aux.andE || offset == Aux.orE ||
        offset == Aux.impE || offset == Aux.iffE || offset == Aux.boolHolds ||
          offset == Aux.quote then
    CoreSort.bool
  else
    CoreSort.object
def auxSymbol (offset arity : Nat) : ProjectM CoreSyntax.Search.FunctionSymbol := do
  let state ← get
  pure {
    id := state.auxBase + offset
    arity := arity
    kind := CoreSyntax.Search.SymbolKind.builtin
    outputSort := auxOutputSort offset
  }
def auxApp (offset : Nat) (args : List CoreSyntax.Search.Term) : ProjectM CoreSyntax.Search.Term := do
  let symbol ← auxSymbol offset args.length
  pure (CoreSyntax.Search.Term.app symbol args)
def boolConst (value : Bool) : ProjectM CoreSyntax.Search.Term :=
  auxApp (if value then Aux.boolTrue else Aux.boolFalse) []
def tupleTerm (predicate : PredicateSymbol) (args : List CoreSyntax.Search.Term) : CoreSyntax.Search.Term :=
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
  def term : Term → Bool
    | Term.fvar .. => true
    | Term.app _ arguments => termList arguments
    | _ => false
  def termList : List Term → Bool
    | [] => true
    | head :: tail => term head && termList tail
end
def atom : Atom → Bool
  | Atom.predicate _ arguments => termList arguments
  | Atom.equal _ left right => term left && term right
  | Atom.boolTerm input => term input
def literal (input : Literal) : Bool :=
  atom input.atom
def clause (input : Clause) : Bool :=
  input.all literal
def clauseSet (input : ClauseSet) : Bool :=
  input.all clause
end Projectable
mutual
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
        Nat.max (Formula.maxFreeVarSucc condition) (Nat.max (Term.maxFreeVarSucc thenTerm) (Term.maxFreeVarSucc elseTerm))
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
    | Formula.iffE left right => Nat.max (Formula.maxFreeVarSucc left) (Formula.maxFreeVarSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.maxFreeVarSucc body
  def Term.maxFreeVarListSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (Term.maxFreeVarSucc term) (Term.maxFreeVarListSucc rest)
end
mutual
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
        Nat.max (Formula.maxFunctionIdSucc condition) (Nat.max (Term.maxFunctionIdSucc thenTerm) (Term.maxFunctionIdSucc elseTerm))
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
    | Formula.iffE left right => Nat.max (Formula.maxFunctionIdSucc left) (Formula.maxFunctionIdSucc right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.maxFunctionIdSucc body
  def Term.maxFunctionListIdSucc : List Term → Nat
    | [] => 0
    | term :: rest => Nat.max (Term.maxFunctionIdSucc term) (Term.maxFunctionListIdSucc rest)
end
def contextArgsFrom (index : Nat) : List CoreSort → List Term
  | [] => []
  | sort :: rest => Term.bvar sort index :: contextArgsFrom (index + 1) rest
def contextArgs (contextSorts : List CoreSort) : List Term :=
  contextArgsFrom 0 contextSorts
structure FormulaArgumentFreeVarParam where
  sort : CoreSort
  varId : VarId
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Lean.ToExpr
namespace FormulaArgumentFreeVarParam
def term (parameter : FormulaArgumentFreeVarParam) : Term :=
  Term.fvar parameter.sort parameter.varId
def insert (parameter : FormulaArgumentFreeVarParam) (parameters : List FormulaArgumentFreeVarParam) : List FormulaArgumentFreeVarParam :=
  if parameters.contains parameter then parameters else parameters ++ [parameter]
def merge (left right : List FormulaArgumentFreeVarParam) : List FormulaArgumentFreeVarParam :=
  right.foldl (fun parameters parameter => insert parameter parameters) left
def distinct (parameters : List FormulaArgumentFreeVarParam) : Bool :=
  parameters.Pairwise fun left right => left != right
def sorts (parameters : List FormulaArgumentFreeVarParam) : List CoreSort :=
  parameters.map (fun parameter => parameter.sort)
def terms (parameters : List FormulaArgumentFreeVarParam) : List Term :=
  parameters.map term
end FormulaArgumentFreeVarParam
mutual
  def Term.formulaArgumentFreeVarParams : Term → List FormulaArgumentFreeVarParam
    | Term.bvar .. => []
    | Term.fvar sort varId => [{ sort := sort, varId := varId }]
    | Term.app _ args => Term.formulaArgumentFreeVarParamsList args
    | Term.apply fn arg =>
        FormulaArgumentFreeVarParam.merge (Term.formulaArgumentFreeVarParams fn) (Term.formulaArgumentFreeVarParams arg)
    | Term.bool _ => []
    | Term.notE body => Term.formulaArgumentFreeVarParams body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right =>
        FormulaArgumentFreeVarParam.merge (Term.formulaArgumentFreeVarParams left) (Term.formulaArgumentFreeVarParams right)
    | Term.quote formula => Formula.formulaArgumentFreeVarParams formula
    | Term.lam _ _ body => Term.formulaArgumentFreeVarParams body
    | Term.ite _ condition thenTerm elseTerm =>
        FormulaArgumentFreeVarParam.merge (Formula.formulaArgumentFreeVarParams condition)
          (FormulaArgumentFreeVarParam.merge (Term.formulaArgumentFreeVarParams thenTerm) (Term.formulaArgumentFreeVarParams elseTerm))
  def Formula.formulaArgumentFreeVarParams : Formula → List FormulaArgumentFreeVarParam
    | Formula.trueE => []
    | Formula.falseE => []
    | Formula.atom _ args => Term.formulaArgumentFreeVarParamsList args
    | Formula.equal _ left right =>
        FormulaArgumentFreeVarParam.merge (Term.formulaArgumentFreeVarParams left) (Term.formulaArgumentFreeVarParams right)
    | Formula.boolTerm term => Term.formulaArgumentFreeVarParams term
    | Formula.neg body => Formula.formulaArgumentFreeVarParams body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right =>
        FormulaArgumentFreeVarParam.merge (Formula.formulaArgumentFreeVarParams left) (Formula.formulaArgumentFreeVarParams right)
    | Formula.forallE _ body
    | Formula.existsE _ body => Formula.formulaArgumentFreeVarParams body
  def Term.formulaArgumentFreeVarParamsList : List Term → List FormulaArgumentFreeVarParam
    | [] => []
    | term :: rest =>
        FormulaArgumentFreeVarParam.merge (Term.formulaArgumentFreeVarParams term) (Term.formulaArgumentFreeVarParamsList rest)
end
def closeForall (contextSorts : List CoreSort) (body : Formula) : Formula :=
  contextSorts.foldl (fun acc sort => Formula.forallE sort acc) body
structure BoolDefinition where
  index : Nat
  symbol : FunctionSymbol
  contextSorts : List CoreSort
  freeVarParams : List FormulaArgumentFreeVarParam
  sourceFormula : Formula
  formula : Formula
  deriving Repr, Lean.ToExpr
namespace BoolDefinition
def inputSorts (definition : BoolDefinition) : List CoreSort :=
  definition.contextSorts ++
    FormulaArgumentFreeVarParam.sorts definition.freeVarParams
def arguments (definition : BoolDefinition) : List Term :=
  contextArgs definition.contextSorts ++
    FormulaArgumentFreeVarParam.terms definition.freeVarParams
def replacement (definition : BoolDefinition) : Term :=
  Term.app definition.symbol definition.arguments
def definitionFormula (definition : BoolDefinition) : Formula :=
  closeForall definition.contextSorts (Formula.iffE (Formula.boolTerm definition.replacement) definition.formula)
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
                  Formula.checkWith definition.contextSorts definition.formula && (match Term.inferSortWith definition.contextSorts definition.replacement with
                    | some sort => sort == CoreSort.bool
                    | none => false) &&
                      definition.definitionFormula.check?
def eq (left right : BoolDefinition) : Bool :=
  left.index == right.index &&
    left.symbol == right.symbol &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.formulaEq left.sourceFormula right.sourceFormula &&
            SyntaxEq.formulaEq left.formula right.formula
def listEq : List BoolDefinition → List BoolDefinition → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false
def arrayEq (left right : Array BoolDefinition) : Bool :=
  listEq left.toList right.toList
end BoolDefinition
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
def lookupDefinition? : List BoolDefinition → Nat → Option BoolDefinition
  | [], _ => none
  | definition :: _, 0 => some definition
  | _ :: rest, index + 1 => lookupDefinition? rest index
def definitionAt? (definitions : Array BoolDefinition) (index : Nat) : Option BoolDefinition :=
  lookupDefinition? definitions.toList index
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
def eq (left right : FormulaArgumentIntro) : Bool :=
  left.definitionIndex == right.definitionIndex &&
    left.symbol == right.symbol &&
      left.contextSorts == right.contextSorts &&
        left.freeVarParams == right.freeVarParams &&
          SyntaxEq.formulaEq left.sourceFormula right.sourceFormula &&
            SyntaxEq.formulaEq left.formula right.formula &&
              SyntaxEq.termEq left.replacement right.replacement
def listEq : List FormulaArgumentIntro → List FormulaArgumentIntro → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => eq left right && listEq leftRest rightRest
  | _, _ => false
def arrayEq (left right : Array FormulaArgumentIntro) : Bool :=
  listEq left.toList right.toList
end FormulaArgumentIntro
structure FormulaArgumentState where
  nextDefinition : Nat
  intros : Array FormulaArgumentIntro := #[]
  definitions : Array BoolDefinition := #[]
  deriving Repr, Lean.ToExpr
abbrev FormulaArgumentM := StateM FormulaArgumentState
def introBoolDefinition (contextSorts : List CoreSort) (sourceFormula formula : Formula) : FormulaArgumentM Term := do
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
  def introduceFormulaArguments (contextSorts : List CoreSort) : Formula → FormulaArgumentM Formula
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
  def introduceTermFormulaArguments (contextSorts : List CoreSort) : Term → FormulaArgumentM Term
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
  def introduceBoolViewTermFormulaArguments (contextSorts : List CoreSort) : Term → FormulaArgumentM Term
    | Term.quote formula => do
        let formula ← introduceFormulaArguments contextSorts formula
        pure (Term.quote formula)
    | term => introduceTermFormulaArguments contextSorts term
  def introduceTermListFormulaArguments (contextSorts : List CoreSort) : List Term → FormulaArgumentM (List Term)
    | [] => pure []
    | term :: rest => do
        let term ← introduceTermFormulaArguments contextSorts term
        let rest ← introduceTermListFormulaArguments contextSorts rest
        pure (term :: rest)
end
structure FormulaArgumentTrace where
  source : Formula
  targetCore : Formula
  target : Formula
  intros : Array FormulaArgumentIntro
  definitions : Array BoolDefinition
  deriving Repr, Lean.ToExpr
namespace FormulaArgumentTrace
def withDefinitions (targetCore : Formula) (definitions : Array BoolDefinition) : Formula :=
  Formula.conjunctionList (targetCore :: definitions.toList.map BoolDefinition.definitionFormula)
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
def check (payload : FOOLClausePayload) : Bool :=
  let expected := build payload.source (config := payload.config)
  payload.source.check? &&
    Pipeline.check payload.sourcePipeline &&
      SyntaxEq.formulaEq payload.sourcePipeline.source payload.source &&
        SyntaxEq.formulaEq payload.argumentSource (normalizeFormula payload.source (config := { payload.config with fool := false })) &&
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
def initialState (source : Formula) : State :=
  let fnBase := Formula.maxFunctionIdSucc source + 1
  {
    nextVar := Formula.maxFreeVarSucc source
    nextSkolem := fnBase + 32
    auxBase := fnBase
  }
def freshUniversal : ProjectM CoreSyntax.Search.Term := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  pure (CoreSyntax.Search.Term.var state.nextVar)
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
mutual
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
  partial def projectTermList (ctx : Context) : List Term → ProjectM (List CoreSyntax.Search.Term)
    | [] => pure []
    | term :: rest => do
        let term ← projectTerm ctx term
        let rest ← projectTermList ctx rest
        pure (term :: rest)
end
def projectAtom (ctx : Context) (positive : Bool) : Atom → ProjectM CoreSyntax.Search.Literal := fun
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
def projectLiteral (ctx : Context) (literal : Literal) : ProjectM CoreSyntax.Search.Literal :=
  projectAtom ctx literal.positive literal.atom
def projectClause (ctx : Context) (clause : Clause) : ProjectM CoreSyntax.Search.Clause := do
  let literals ←
    clause.toList.foldr (fun literal acc => do
        let literal ← projectLiteral ctx literal
        let rest ← acc
        pure (literal :: rest)) (pure [])
  pure literals.toArray
def projectClauseSet (ctx : Context) (clauses : ClauseSet) : ProjectM (Array CoreSyntax.Search.Clause) := do
  let clauseList ←
    clauses.toList.foldr (fun clause acc => do
        let clause ← projectClause ctx clause
        let rest ← acc
        pure (clause :: rest)) (pure [])
  pure clauseList.toArray
def enterPrefix : Prefix → Context → ProjectM Context
  | [], ctx => pure ctx
  | Quantifier.forallE _ :: rest, ctx => do
      let term ← freshUniversal
      enterPrefix rest { bound := term :: ctx.bound, universals := term :: ctx.universals }
  | Quantifier.existsE _ :: rest, ctx => do
      let term ← freshSkolem ctx
      enterPrefix rest { ctx with bound := term :: ctx.bound }
structure Result where
  foolPayload : FOOLClausePayload
  pipeline : Pipeline
  clausePipeline : Pipeline
  clauses : Array CoreSyntax.Search.Clause
  skolemTrace : Array CoreSyntax.Search.Intro
  auxBase : Nat
  deriving Repr, Lean.ToExpr
def build? (source : Formula) (config : Config := {}) : Option Result := do
  if !source.check? then
    none
  else
  let foolPayload := FOOLClausePayload.build source (config := config)
  let pipeline := foolPayload.sourcePipeline
  let clausePipeline := foolPayload.clausePipeline
  let initial := initialState foolPayload.clauseSource
  let some ((_, clauses), state) := (do
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
structure Payload where
  source : Formula
  projection : FirstOrderProjection.Result
  traceReplayChecked : Bool
  deriving Repr, Lean.ToExpr
namespace Payload
def build (projection : FirstOrderProjection.Result) : Payload :=
  {
    source := projection.pipeline.source
    projection := projection
    traceReplayChecked := FirstOrderProjection.check projection
  }
def check (payload : Payload) : Bool :=
  payload.traceReplayChecked &&
    FirstOrderProjection.check payload.projection &&
      SyntaxEq.formulaEq payload.source payload.projection.pipeline.source &&
        FirstOrderProjection.FOOLClausePayload.check payload.projection.foolPayload &&
          FirstOrderProjection.FormulaArgumentTrace.check
            payload.projection.foolPayload.argumentTrace
def mk? (projection : FirstOrderProjection.Result) : Option (Certificate.Checked Payload Payload.check) :=
  Certificate.Checked.mk? (check := Payload.check) (build projection)
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
def toCoreNode (payload : Payload) (id : Certificate.NodeId := 0) (dependencies : Array Certificate.NodeId := #[])
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
structure ReplayPayload where
  checked : Certificate.Checked Payload Payload.check
  replayChecker : Bool
namespace ReplayPayload
def check (payload : ReplayPayload) : Bool :=
  Payload.check payload.checked.payload && payload.replayChecker
def ofChecked (checked : Certificate.Checked Payload Payload.check) : ReplayPayload :=
  { checked := checked, replayChecker := Payload.check checked.payload }
end ReplayPayload
end FoolClausification
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
