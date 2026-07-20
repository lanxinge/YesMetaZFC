import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Logic.HigherOrder

/-!
# 原生高阶 DAG 的子句边界

本模块先固定 HO 证书直接消费的 atom、literal 与 clause 形状。项语法来自新的
`Logic.HigherOrder`，因此 `apply/lam` 是 checker 可见的一等数据，而不是搜索器附带的
不透明 payload。
-/

namespace YesMetaZFC
namespace Automation
namespace HODAGCertificate

open Logic.HigherOrder

universe u v w x

abbrev Signature := Logic.HigherOrder.Signature
abbrev SimpleType (σ : Signature) := Logic.HigherOrder.SimpleType σ.BaseSort
abbrev Term (σ : Signature) := Logic.HigherOrder.Term σ
abbrev Context (σ : Signature) := Logic.HigherOrder.Context σ
abbrev Structure (σ : Signature) := Logic.HigherOrder.Structure σ

/-! ## 可计算结构相等 -/

namespace StructuralEq

mutual
  /-- 原生高阶项的结构比较。 -/
  def term {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      [DecidableEq σ.FuncSymbol] : Term σ → Term σ → Bool
    | .var (.bvar sort index), .var (.bvar sort' index') =>
        decide (sort = sort') && index == index'
    | .var (.fvar sort id), .var (.fvar sort' id') =>
        decide (sort = sort') && id == id'
    | .app symbol arguments, .app symbol' arguments' =>
        decide (symbol = symbol') && termList arguments arguments'
    | .apply function argument, .apply function' argument' =>
        term function function' && term argument argument'
    | .lam domain codomain body, .lam domain' codomain' body' =>
        decide (domain = domain') && decide (codomain = codomain') && term body body'
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right

  /-- 原生高阶项列表的结构比较。 -/
  def termList {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      [DecidableEq σ.FuncSymbol] : List (Term σ) → List (Term σ) → Bool
    | [], [] => true
    | left :: rest, right :: rest' => term left right && termList rest rest'
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
end

/-- 项结构比较为真时，两侧项实际相等。 -/
theorem term_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] (left : Term σ) :
    ∀ right : Term σ, term left right = true → left = right := by
  refine Logic.HigherOrder.Term.rec
    (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro value right h
    cases right <;> simp [term] at h
    case var other =>
      cases value <;> cases other <;> simp [term] at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro symbol arguments ihArguments right h
    cases right <;> simp [term] at h
    case app otherSymbol otherArguments =>
      rcases h with ⟨hSymbol, hArguments⟩
      cases hSymbol
      exact congrArg (Term.app symbol) (ihArguments _ hArguments)
  · intro function argument ihFunction ihArgument right h
    cases right <;> simp [term] at h
    case apply otherFunction otherArgument =>
      rcases h with ⟨hFunction, hArgument⟩
      cases ihFunction _ hFunction
      cases ihArgument _ hArgument
      rfl
  · intro domain codomain body ihBody right h
    cases right <;> simp [term] at h
    case lam otherDomain otherCodomain otherBody =>
      have hFields :
          (domain = otherDomain ∧ codomain = otherCodomain) ∧
            term body otherBody = true := by
        simpa [term] using h
      rcases hFields with ⟨⟨hDomain, hCodomain⟩, hBody⟩
      have hBodyEq := ihBody _ hBody
      cases hDomain
      cases hCodomain
      cases hBodyEq
      rfl
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      cases ihHead _ hHead
      cases ihTail _ hTail
      rfl

/-- 项列表结构比较为真时，两侧列表实际相等。 -/
theorem termList_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] (left : List (Term σ)) :
    ∀ right : List (Term σ), termList left right = true → left = right := by
  refine Logic.HigherOrder.Term.rec_1
    (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro value right h
    cases right <;> simp [term] at h
    case var other =>
      cases value <;> cases other <;> simp [term] at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro symbol arguments ihArguments right h
    cases right <;> simp [term] at h
    case app otherSymbol otherArguments =>
      rcases h with ⟨hSymbol, hArguments⟩
      cases hSymbol
      exact congrArg (Term.app symbol) (ihArguments _ hArguments)
  · intro function argument ihFunction ihArgument right h
    cases right <;> simp [term] at h
    case apply otherFunction otherArgument =>
      rcases h with ⟨hFunction, hArgument⟩
      cases ihFunction _ hFunction
      cases ihArgument _ hArgument
      rfl
  · intro domain codomain body ihBody right h
    cases right <;> simp [term] at h
    case lam otherDomain otherCodomain otherBody =>
      have hFields :
          (domain = otherDomain ∧ codomain = otherCodomain) ∧
            term body otherBody = true := by
        simpa [term] using h
      rcases hFields with ⟨⟨hDomain, hCodomain⟩, hBody⟩
      have hBodyEq := ihBody _ hBody
      cases hDomain
      cases hCodomain
      cases hBodyEq
      rfl
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      cases ihHead _ hHead
      cases ihTail _ hTail
      rfl

end StructuralEq

/-- 高阶叠加演算直接处理的原子。 -/
inductive Atom (σ : Signature.{u, v, w}) where
  | rel (symbol : σ.RelSymbol) (arguments : List (Term σ))
  | equal (sort : SimpleType σ) (left right : Term σ)

namespace Atom

/-- 将 typed substitution 作用到高阶原子。 -/
def applySubstitution {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (substitution : TermSubstitution σ) : Atom σ → Atom σ
  | .rel symbol arguments =>
      .rel symbol (Term.applySubstitutionList substitution arguments)
  | .equal sort left right =>
      .equal sort (left.applySubstitution substitution)
        (right.applySubstitution substitution)

/-- 将原子中的自由变量编号整体平移。 -/
def renameFreeVars {σ : Signature.{u, v, w}} (offset : Nat) : Atom σ → Atom σ
  | .rel symbol arguments =>
      .rel symbol (Term.renameFreeVarsList offset arguments)
  | .equal sort left right =>
      .equal sort (left.renameFreeVars offset) (right.renameFreeVars offset)

/-- 原子的结构比较。 -/
def eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :
    Atom σ → Atom σ → Bool
  | .rel symbol arguments, .rel symbol' arguments' =>
      decide (symbol = symbol') && StructuralEq.termList arguments arguments'
  | .equal sort left right, .equal sort' left' right' =>
      decide (sort = sort') &&
        StructuralEq.term left left' && StructuralEq.term right right'
  | _, _ => false

/-- 原子结构比较为真时，两侧原子实际相等。 -/
theorem eq_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Atom σ) (hEq : eq left right = true) :
    left = right := by
  cases left with
  | rel symbol arguments =>
      cases right with
      | rel symbol' arguments' =>
          have hFields :
              symbol = symbol' ∧
                StructuralEq.termList arguments arguments' = true := by
            simpa [eq] using hEq
          rcases hFields with ⟨hSymbol, hArguments⟩
          cases hSymbol
          cases StructuralEq.termList_sound _ _ hArguments
          rfl
      | equal otherSort otherLeft otherRight =>
          simp [eq] at hEq
  | equal sort leftTerm rightTerm =>
      cases right with
      | rel otherSymbol otherArguments =>
          simp [eq] at hEq
      | equal sort' left' right' =>
          have hFields :
              (sort = sort' ∧ StructuralEq.term leftTerm left' = true) ∧
                StructuralEq.term rightTerm right' = true := by
            simpa [eq] using hEq
          rcases hFields with ⟨⟨hSort, hLeft⟩, hRight⟩
          have hLeftEq := StructuralEq.term_sound _ _ hLeft
          have hRightEq := StructuralEq.term_sound _ _ hRight
          cases hSort
          cases hLeftEq
          cases hRightEq
          rfl

/-- 把子句原子嵌入高阶公式语法。 -/
def toFormula {σ : Signature.{u, v, w}} : Atom σ → Logic.HigherOrder.Formula σ
  | .rel symbol arguments => .rel symbol arguments
  | .equal sort left right => .equal sort left right

/-- 在绑定上下文中检查原子的 scope 与 simple type。 -/
def checkWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (context : Context σ) (atom : Atom σ) : Bool :=
  atom.toFormula.checkWith context

/-- 原子的归纳良构性。 -/
def WellFormed {σ : Signature.{u, v, w}}
    (context : Context σ) (atom : Atom σ) : Prop :=
  FormulaWellFormed context atom.toFormula

/-- 原子 checker 的正确性。 -/
theorem checkWith_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {context : Context σ} {atom : Atom σ} (hCheck : atom.checkWith context = true) :
    atom.WellFormed context :=
  Logic.HigherOrder.Formula.checkWith_sound hCheck

/-- 原子在高阶结构中的满足关系。 -/
def Satisfies {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Logic.HigherOrder.Env M) : Atom σ → Prop
  | .rel symbol arguments => M.relInterp symbol (arguments.map (Term.eval env))
  | .equal _ left right => Term.eval env left = Term.eval env right

/-- 原子 substitution 的语义等价于更新 typed 自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) :
    ∀ atom : Atom σ,
      Satisfies sourceEnv (applySubstitution substitution atom) ↔
        Satisfies targetEnv atom
  | .rel symbol arguments => by
      change
        M.relInterp symbol
            ((Term.applySubstitutionList substitution arguments).map
              (Term.eval sourceEnv)) ↔
          M.relInterp symbol (arguments.map (Term.eval targetEnv))
      rw [Term.evalList_applySubstitution_eq_of_envMatches
        hAdmissible hEnv arguments]
  | .equal sort left right => by
      simp only [applySubstitution, Satisfies]
      rw [Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv left,
        Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv right]

/-- 原子自由变量平移的语义等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ atom : Atom σ,
      Satisfies sourceEnv (renameFreeVars offset atom) ↔ Satisfies targetEnv atom
  | .rel symbol arguments => by
      change
        M.relInterp symbol
            ((Term.renameFreeVarsList offset arguments).map (Term.eval sourceEnv)) ↔
          M.relInterp symbol (arguments.map (Term.eval targetEnv))
      rw [Term.evalList_renameFreeVars_eq_of_envMatches hEnv arguments]
  | .equal sort left right => by
      simp only [renameFreeVars, Satisfies]
      rw [Term.eval_renameFreeVars_eq_of_envMatches hEnv left,
        Term.eval_renameFreeVars_eq_of_envMatches hEnv right]

end Atom

/-- 带极性的高阶文字。 -/
structure Literal (σ : Signature.{u, v, w}) where
  polarity : Bool
  atom : Atom σ

namespace Literal

/-- 将 typed substitution 作用到高阶文字。 -/
def applySubstitution {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (substitution : TermSubstitution σ) (literal : Literal σ) : Literal σ :=
  { literal with atom := literal.atom.applySubstitution substitution }

/-- 将高阶文字中的自由变量编号整体平移。 -/
def renameFreeVars {σ : Signature.{u, v, w}} (offset : Nat)
    (literal : Literal σ) : Literal σ :=
  { literal with atom := literal.atom.renameFreeVars offset }

/-- literal 的结构比较。 -/
def eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Literal σ) : Bool :=
  decide (left.polarity = right.polarity) && left.atom.eq right.atom

/-- literal 结构比较为真时，两侧 literal 实际相等。 -/
theorem eq_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Literal σ) (hEq : left.eq right = true) :
    left = right := by
  cases left with
  | mk polarity atom =>
      cases right with
      | mk polarity' atom' =>
          simp [eq] at hEq
          rcases hEq with ⟨hPolarity, hAtom⟩
          cases hPolarity
          cases Atom.eq_sound atom atom' hAtom
          rfl

/-- literal checker 只需检查原子；极性不改变 scope 与类型。 -/
def checkWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (context : Context σ) (literal : Literal σ) : Bool :=
  literal.atom.checkWith context

/-- literal 的归纳良构性。 -/
def WellFormed {σ : Signature.{u, v, w}}
    (context : Context σ) (literal : Literal σ) : Prop :=
  literal.atom.WellFormed context

/-- literal checker 的正确性。 -/
theorem checkWith_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {context : Context σ} {literal : Literal σ}
    (hCheck : literal.checkWith context = true) :
    literal.WellFormed context :=
  Atom.checkWith_sound hCheck

/-- literal 的对象层语义。 -/
def Satisfies {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Logic.HigherOrder.Env M) (literal : Literal σ) : Prop :=
  if literal.polarity then literal.atom.Satisfies env else ¬ literal.atom.Satisfies env

/-- 文字是否匹配给定极性和原子。 -/
def matchesAtom {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Atom σ) (literal : Literal σ) : Bool :=
  decide (literal.polarity = polarity) && literal.atom.eq atom

/-- 文字匹配检查通过时，极性和原子都实际相等。 -/
theorem matchesAtom_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {polarity : Bool} {atom : Atom σ} {literal : Literal σ}
    (hMatches : literal.matchesAtom polarity atom = true) :
    literal.polarity = polarity ∧ literal.atom = atom := by
  rcases Bool.and_eq_true_iff.mp hMatches with ⟨hPolarity, hAtom⟩
  exact ⟨of_decide_eq_true hPolarity, Atom.eq_sound literal.atom atom hAtom⟩

/-- 互补 pivot 文字不可能同时为真。 -/
theorem not_satisfies_matchesAtom_complement
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {pivotPolarity : Bool} {atom : Atom σ} {left right : Literal σ}
    (hLeftMatch : left.matchesAtom pivotPolarity atom = true)
    (hRightMatch : right.matchesAtom (!pivotPolarity) atom = true)
    (hLeft : Satisfies env left) (hRight : Satisfies env right) : False := by
  rcases matchesAtom_sound hLeftMatch with ⟨hLeftPolarity, hLeftAtom⟩
  rcases matchesAtom_sound hRightMatch with ⟨hRightPolarity, hRightAtom⟩
  cases left with
  | mk leftPolarity leftAtom =>
      cases right with
      | mk rightPolarity rightAtom =>
          cases hLeftPolarity
          cases hLeftAtom
          cases hRightPolarity
          cases hRightAtom
          cases leftPolarity
          · exact hLeft hRight
          · exact hRight hLeft

/-- 结构相等的负等词文字不可能为真。 -/
theorem not_satisfies_reflexive_negative_equality
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {sort : SimpleType σ} {left right : Term σ} {literal : Literal σ}
    (hTerm : StructuralEq.term left right = true)
    (hMatch : literal.matchesAtom false (.equal sort left right) = true)
    (hLiteral : Satisfies env literal) : False := by
  rcases matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  have hTermEq : left = right := StructuralEq.term_sound left right hTerm
  cases literal
  cases hPolarity
  cases hAtom
  cases hTermEq
  exact hLiteral rfl

/-- 文字 substitution 的语义等价于更新 typed 自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv)
    (literal : Literal σ) :
    Satisfies sourceEnv (applySubstitution substitution literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr
          (Atom.satisfies_applySubstitution_iff_of_envMatches hAdmissible hEnv atom)
      · exact Atom.satisfies_applySubstitution_iff_of_envMatches hAdmissible hEnv atom

/-- 文字自由变量平移的语义等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv)
    (literal : Literal σ) :
    Satisfies sourceEnv (renameFreeVars offset literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr (Atom.satisfies_renameFreeVars_iff_of_envMatches hEnv atom)
      · exact Atom.satisfies_renameFreeVars_iff_of_envMatches hEnv atom

end Literal

/-- 高阶子句。数组表示保持搜索与材料化阶段的稳定次序。 -/
structure Clause (σ : Signature.{u, v, w}) where
  literals : Array (Literal σ)

namespace Clause

/-- 将 typed substitution 逐文字作用到高阶子句。 -/
def applySubstitution {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (substitution : TermSubstitution σ) (clause : Clause σ) : Clause σ where
  literals := clause.literals.map (Literal.applySubstitution substitution)

/-- 将高阶子句中的自由变量编号整体平移。 -/
def renameFreeVars {σ : Signature.{u, v, w}} (offset : Nat)
    (clause : Clause σ) : Clause σ where
  literals := clause.literals.map (Literal.renameFreeVars offset)

private def literalListEq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :
    List (Literal σ) → List (Literal σ) → Bool
  | [], [] => true
  | literal :: rest, literal' :: rest' =>
      literal.eq literal' && literalListEq rest rest'
  | _, _ => false

private theorem literalListEq_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left : List (Literal σ)) :
    ∀ right : List (Literal σ), literalListEq left right = true → left = right := by
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons _ _ => simp [literalListEq] at h
  | cons literal rest ih =>
      intro right h
      cases right <;> simp [literalListEq] at h
      case cons literal' rest' =>
        rcases h with ⟨hLiteral, hRest⟩
        cases Literal.eq_sound literal literal' hLiteral
        cases ih _ hRest
        rfl

/-- 子句的结构比较。 -/
def eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Clause σ) : Bool :=
  literalListEq left.literals.toList right.literals.toList

/-- 子句结构比较为真时，两侧子句实际相等。 -/
theorem eq_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Clause σ) (hEq : left.eq right = true) :
    left = right := by
  cases left with
  | mk leftLiterals =>
      cases right with
      | mk rightLiterals =>
          simp [eq] at hEq
          have hList := literalListEq_sound _ _ hEq
          cases leftLiterals
          cases rightLiterals
          simp at hList
          simp [hList]

/-- 字句列表中过滤掉匹配给定极性和原子的文字。 -/
def filterOutList {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Atom σ) : List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.matchesAtom polarity atom then
        filterOutList polarity atom rest
      else
        literal :: filterOutList polarity atom rest

/-- 从字句中过滤掉匹配给定极性和原子的文字。 -/
def filterOut {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Atom σ) (clause : Clause σ) : Clause σ where
  literals := (filterOutList polarity atom clause.literals.toList).toArray

/-- 列表中存在结构相等的文字。 -/
def containsLiteralList {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle : Literal σ) : List (Literal σ) → Bool
  | [] => false
  | literal :: rest => needle.eq literal || containsLiteralList needle rest

/-- 按索引删除一个文字，并把替换文字追加到列表末尾。 -/
def replaceLiteralAtEndList {σ : Signature.{u, v, w}}
    (replacement : Literal σ) : List (Literal σ) → Nat → List (Literal σ)
  | [], _ => []
  | _ :: rest, 0 => rest ++ [replacement]
  | literal :: rest, index + 1 =>
      literal :: replaceLiteralAtEndList replacement rest index

/-- 去除重复文字并保留每个结构等价类的最后一次出现。 -/
def dedupLiteralList {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if containsLiteralList literal rest then
        dedupLiteralList rest
      else
        literal :: dedupLiteralList rest

/-- 按索引替换后把新文字移到末尾。 -/
def replaceLiteralAtEnd {σ : Signature.{u, v, w}}
    (clause : Clause σ) (index : Nat) (replacement : Literal σ) : Clause σ where
  literals :=
    (replaceLiteralAtEndList replacement clause.literals.toList index).toArray

/-- 原生 HO 子句规范化；当前只执行确定性文字去重。 -/
def normalize {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) : Clause σ where
  literals := (dedupLiteralList clause.literals.toList).toArray

/-- 用一个文字结构替换列表中所有相同文字。 -/
def replaceLiteralList {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle replacement : Literal σ) : List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.eq needle then
        replacement :: replaceLiteralList needle replacement rest
      else
        literal :: replaceLiteralList needle replacement rest

/-- 用一个文字结构替换子句中所有相同文字。 -/
def replaceLiteral {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (needle replacement : Literal σ) : Clause σ where
  literals := (replaceLiteralList needle replacement clause.literals.toList).toArray

/-- 子句是否包含给定结构的文字。 -/
def containsLiteral {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (needle : Literal σ) : Bool :=
  containsLiteralList needle clause.literals.toList

/-- 一个字句的所有文字是否都被另一个字句覆盖。 -/
def allLiteralsCovered {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (source target : Clause σ) : Bool :=
  source.literals.toList.all fun literal => target.containsLiteral literal

/-- component 列表是否在 literal 层双向覆盖 source 字句。 -/
def coversCheck {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (source : Clause σ)
    (components : List (Clause σ)) : Bool :=
  (source.literals.toList.all fun literal =>
    components.any fun component => containsLiteral component literal) &&
    components.all fun component => allLiteralsCovered component source

/-- 字句是否含有匹配给定极性和原子的文字。 -/
def containsMatching {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (polarity : Bool) (atom : Atom σ) : Bool :=
  clause.literals.toList.any fun literal => literal.matchesAtom polarity atom

/-- resolution 结构结果：删去互补 pivot 后连接两个父字句。 -/
def resolutionResult {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (leftPolarity : Bool) (pivot : Atom σ) (left right : Clause σ) : Clause σ where
  literals :=
    (filterOutList leftPolarity pivot left.literals.toList ++
      filterOutList (!leftPolarity) pivot right.literals.toList).toArray

/-- equality-resolution 结构结果：删去结构自等的负等词文字。 -/
def equalityResolutionResult {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (sort : SimpleType σ) (left right : Term σ) (parent : Clause σ) : Clause σ :=
  parent.filterOut false (.equal sort left right)

/-- 未被过滤的列表成员仍在过滤后列表中。 -/
theorem mem_filterOutList_of_mem_of_not_matches
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {polarity : Bool} {atom : Atom σ} {literal : Literal σ} :
    ∀ {literals : List (Literal σ)}, literal ∈ literals →
      literal.matchesAtom polarity atom = false →
        literal ∈ filterOutList polarity atom literals
  | [], hMem, _ => by cases hMem
  | head :: rest, hMem, hNoMatch => by
      by_cases hHead : head.matchesAtom polarity atom = true
      · rw [filterOutList]
        simp [hHead]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst hEq
          simp [hHead] at hNoMatch
        · exact mem_filterOutList_of_mem_of_not_matches hTail hNoMatch
      · have hHeadFalse : head.matchesAtom polarity atom = false := by
          cases hValue : head.matchesAtom polarity atom <;> simp [hValue] at hHead ⊢
        rw [filterOutList]
        simp [hHeadFalse]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · exact Or.inl hEq
        · exact Or.inr (mem_filterOutList_of_mem_of_not_matches hTail hNoMatch)

/-- 左父字句中未被删去的文字会出现在 resolution 结果中。 -/
theorem mem_resolutionResult_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ}
    {literal : Literal σ}
    (hMem : literal ∈ left.literals.toList)
    (hNoMatch : literal.matchesAtom leftPolarity pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inl (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)

/-- 右父字句中未被删去的文字会出现在 resolution 结果中。 -/
theorem mem_resolutionResult_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ}
    {literal : Literal σ}
    (hMem : literal ∈ right.literals.toList)
    (hNoMatch : literal.matchesAtom (!leftPolarity) pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inr (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)

/-- equality-resolution 中未被删去的文字会出现在结果中。 -/
theorem mem_equalityResolutionResult {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {sort : SimpleType σ} {left right : Term σ} {parent : Clause σ}
    {literal : Literal σ}
    (hMem : literal ∈ parent.literals.toList)
    (hNoMatch : literal.matchesAtom false (.equal sort left right) = false) :
    literal ∈
      (equalityResolutionResult sort left right parent).literals.toList := by
  simpa [equalityResolutionResult, filterOut] using
    mem_filterOutList_of_mem_of_not_matches hMem hNoMatch

/-- `containsLiteralList` 通过时，可取出结构相等的成员。 -/
theorem containsLiteralList_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {needle : Literal σ} :
    ∀ {literals : List (Literal σ)}, containsLiteralList needle literals = true →
      ∃ literal, literal ∈ literals ∧ literal = needle
  | [], h => by simp [containsLiteralList] at h
  | head :: rest, h => by
      simp [containsLiteralList] at h
      rcases h with hHead | hRest
      · exact ⟨head, List.mem_cons_self, (Literal.eq_sound needle head hHead).symm⟩
      · rcases containsLiteralList_sound hRest with ⟨literal, hMem, hEq⟩
        exact ⟨literal, List.mem_cons_of_mem head hMem, hEq⟩

/-- 按索引把一个语义蕴含的文字移到末尾后，列表析取仍成立。 -/
private theorem satisfies_replaceLiteralAtEndList
    {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {needle replacement : Literal σ}
    (hReplacement : needle.Satisfies env → replacement.Satisfies env) :
    ∀ (literals : List (Literal σ)) (index : Nat),
      literals[index]? = some needle →
        (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
          ∃ literal,
            literal ∈ replaceLiteralAtEndList replacement literals index ∧
              literal.Satisfies env
  | [], index, hGet, _hSat => by
      simp at hGet
  | head :: rest, 0, hGet, hSat => by
      have hHead : head = needle := by
        simpa using Option.some.inj hGet
      rcases hSat with ⟨literal, hMem, hLiteral⟩
      rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
      · subst literal
        exact ⟨replacement, by simp [replaceLiteralAtEndList],
          hReplacement (by simpa [hHead] using hLiteral)⟩
      · exact ⟨literal, by simp [replaceLiteralAtEndList, hLiteralRest], hLiteral⟩
  | head :: rest, index + 1, hGet, hSat => by
      have hRestGet : rest[index]? = some needle := by
        simpa using hGet
      rcases hSat with ⟨literal, hMem, hLiteral⟩
      rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
      · subst literal
        exact ⟨head, by simp [replaceLiteralAtEndList], hLiteral⟩
      · rcases satisfies_replaceLiteralAtEndList hReplacement rest index hRestGet
            ⟨literal, hLiteralRest, hLiteral⟩ with
          ⟨witness, hWitnessMem, hWitnessSat⟩
        exact ⟨witness, by simp [replaceLiteralAtEndList, hWitnessMem], hWitnessSat⟩

/-- 去重不会丢失列表析取的满足见证。 -/
private theorem satisfies_dedupLiteralList
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} :
    ∀ literals : List (Literal σ),
      (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
        ∃ literal, literal ∈ dedupLiteralList literals ∧ literal.Satisfies env
  | [], hSat => by
      rcases hSat with ⟨literal, hMem, _hLiteral⟩
      cases hMem
  | head :: rest, hSat => by
      cases hDuplicate : containsLiteralList head rest with
      | false =>
          rcases hSat with ⟨literal, hMem, hLiteral⟩
          rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
          · subst literal
            exact ⟨head, by simp [dedupLiteralList, hDuplicate], hLiteral⟩
          · rcases satisfies_dedupLiteralList rest
                ⟨literal, hLiteralRest, hLiteral⟩ with
              ⟨witness, hWitnessMem, hWitnessSat⟩
            exact ⟨witness,
              by simp [dedupLiteralList, hDuplicate, hWitnessMem], hWitnessSat⟩
      | true =>
          rcases hSat with ⟨literal, hMem, hLiteral⟩
          have hRestSat :
              ∃ witness, witness ∈ rest ∧ witness.Satisfies env := by
            rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
            · subst literal
              rcases containsLiteralList_sound hDuplicate with
                ⟨duplicate, hDuplicateMem, hDuplicateEq⟩
              exact ⟨duplicate, hDuplicateMem, by simpa [hDuplicateEq] using hLiteral⟩
            · exact ⟨literal, hLiteralRest, hLiteral⟩
          simpa [dedupLiteralList, hDuplicate] using
            satisfies_dedupLiteralList rest hRestSat

/-- 覆盖检查通过时，source 中任一文字都能在 target 中找到结构相等文字。 -/
theorem allLiteralsCovered_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {source target : Clause σ} (hCovered : allLiteralsCovered source target = true) :
    ∀ {literal : Literal σ}, literal ∈ source.literals.toList →
      ∃ literal', literal' ∈ target.literals.toList ∧ literal' = literal := by
  intro literal hMem
  have hAll := List.all_eq_true.mp hCovered
  have hContains : target.containsLiteral literal = true := hAll literal hMem
  exact containsLiteralList_sound hContains

/-- 文字列表中的满足性可穿过结构替换。 -/
private theorem satisfies_replaceLiteralList {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {needle replacement : Literal σ}
    (hReplacement : needle.Satisfies env → replacement.Satisfies env) :
    ∀ {literals : List (Literal σ)},
      (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
        ∃ literal,
          literal ∈ replaceLiteralList needle replacement literals ∧
            literal.Satisfies env
  | [], h => by
      rcases h with ⟨literal, hMem, _hSat⟩
      cases hMem
  | literal :: rest, h => by
      rcases h with ⟨witness, hMem, hSat⟩
      by_cases hMatch : literal.eq needle = true
      · have hLiteralEq : literal = needle := Literal.eq_sound literal needle hMatch
        rw [replaceLiteralList, hMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : literal.Satisfies env := by
            simpa [hHead] using hSat
          exact ⟨replacement, by simp,
            hReplacement (by simpa [hLiteralEq] using hSatLiteral)⟩
        · rcases satisfies_replaceLiteralList hReplacement
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
      · have hNoMatch : literal.eq needle = false := by
          cases hValue : literal.eq needle <;> simp [hValue] at hMatch ⊢
        rw [replaceLiteralList, hNoMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : literal.Satisfies env := by
            simpa [hHead] using hSat
          exact ⟨literal, by simp, hSatLiteral⟩
        · rcases satisfies_replaceLiteralList hReplacement
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩

/-- 在同一绑定上下文中检查全部 literal。 -/
def checkWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (context : Context σ) (clause : Clause σ) : Bool :=
  clause.literals.all fun literal => literal.checkWith context

/-- 闭子句 checker。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) : Bool :=
  clause.checkWith []

/-- 子句中每个 literal 都在同一上下文中良构。 -/
def WellFormed {σ : Signature.{u, v, w}}
    (context : Context σ) (clause : Clause σ) : Prop :=
  ∀ literal, literal ∈ clause.literals → literal.WellFormed context

/-- 子句 checker 的正确性。 -/
theorem checkWith_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {context : Context σ} {clause : Clause σ}
    (hCheck : clause.checkWith context = true) :
    clause.WellFormed context := by
  intro literal hMember
  rcases Array.mem_iff_getElem.mp hMember with ⟨index, hIndex, hGet⟩
  have hAll := Array.all_eq_true.mp hCheck
  have hAt := hAll index hIndex
  apply Literal.checkWith_sound
  simpa [hGet] using hAt

/-- 高阶子句按析取解释。 -/
def Satisfies {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Logic.HigherOrder.Env M) (clause : Clause σ) : Prop :=
  ∃ literal, literal ∈ clause.literals ∧ literal.Satisfies env

/-- 良构文字在上下文等价环境中的真值保持。 -/
theorem Literal.satisfies_iff_of_wellFormed_env
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env₁ env₂ : Logic.HigherOrder.Env M}
    {literal : Literal σ} (hLiteral : literal.WellFormed context)
    (hBound :
      ∀ index target,
        Context.lookup? context index = some target →
          env₁.boundVal index = env₂.boundVal index)
    (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
    literal.Satisfies env₁ ↔ literal.Satisfies env₂ := by
  cases literal with
  | mk polarity atom =>
      have hAtom :
          atom.Satisfies env₁ ↔ atom.Satisfies env₂ := by
        have hFormula :=
          Logic.HigherOrder.Formula.satisfies_iff_of_wellFormed_env
            hLiteral hBound hFree
        cases atom <;>
          simpa [Atom.Satisfies, Atom.toFormula,
            Logic.HigherOrder.Formula.Satisfies] using hFormula
      cases polarity with
      | false =>
          exact not_congr hAtom
      | true =>
          exact hAtom

/-- 良构子句在上下文等价环境中的满足关系保持。 -/
theorem satisfies_iff_of_wellFormed_env
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env₁ env₂ : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hClause : clause.WellFormed context)
    (hBound :
      ∀ index target,
        Context.lookup? context index = some target →
          env₁.boundVal index = env₂.boundVal index)
    (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
    clause.Satisfies env₁ ↔ clause.Satisfies env₂ := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    exact ⟨literal, hMem,
      (Literal.satisfies_iff_of_wellFormed_env
        (hClause literal hMem) hBound hFree).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    exact ⟨literal, hMem,
      (Literal.satisfies_iff_of_wellFormed_env
        (hClause literal hMem) hBound hFree).mpr hLiteral⟩

/-- 按索引替换为语义蕴含文字后，子句满足性保持。 -/
theorem satisfies_replaceLiteralAtEnd {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {index : Nat} {needle replacement : Literal σ}
    (hGet : clause.literals[index]? = some needle)
    (hReplacement : needle.Satisfies env → replacement.Satisfies env)
    (hClause : clause.Satisfies env) :
    (clause.replaceLiteralAtEnd index replacement).Satisfies env := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  rcases satisfies_replaceLiteralAtEndList hReplacement clause.literals.toList
      index (by simpa using hGet)
      ⟨literal, Array.mem_def.mp hMem, hLiteral⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness,
    Array.mem_def.mpr (by simpa [replaceLiteralAtEnd] using hWitnessMem),
    hWitnessSat⟩

/-- 子句去重保持满足性。 -/
theorem satisfies_normalize {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hClause : clause.Satisfies env) :
    clause.normalize.Satisfies env := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  rcases satisfies_dedupLiteralList clause.literals.toList
      ⟨literal, Array.mem_def.mp hMem, hLiteral⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness,
    Array.mem_def.mpr (by simpa [normalize] using hWitnessMem),
    hWitnessSat⟩

/-- 字句中的真文字给出字句满足性。 -/
theorem satisfies_of_literal_mem {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {literal : Literal σ}
    (hMem : literal ∈ clause.literals.toList) (hLiteral : literal.Satisfies env) :
    clause.Satisfies env :=
  ⟨literal, Array.mem_def.mpr hMem, hLiteral⟩

/-- resolution 结构结果的语义 soundness。 -/
theorem satisfies_resolutionResult {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ}
    (hLeft : left.Satisfies env) (hRight : right.Satisfies env) :
    (resolutionResult leftPolarity pivot left right).Satisfies env := by
  rcases hLeft with ⟨leftLiteral, hLeftMem, hLeftLiteral⟩
  cases hLeftMatch : leftLiteral.matchesAtom leftPolarity pivot with
  | false =>
      exact satisfies_of_literal_mem
        (mem_resolutionResult_left (Array.mem_def.mp hLeftMem) hLeftMatch)
        hLeftLiteral
  | true =>
      rcases hRight with ⟨rightLiteral, hRightMem, hRightLiteral⟩
      cases hRightMatch : rightLiteral.matchesAtom (!leftPolarity) pivot with
      | false =>
          exact satisfies_of_literal_mem
            (mem_resolutionResult_right (Array.mem_def.mp hRightMem) hRightMatch)
            hRightLiteral
      | true =>
          exact False.elim
            (Literal.not_satisfies_matchesAtom_complement
              hLeftMatch hRightMatch hLeftLiteral hRightLiteral)

/-- 父字句所有文字被结论覆盖时，父字句满足性可传递到结论。 -/
theorem satisfies_of_allLiteralsCovered {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {source target : Clause σ}
    (hCovered : source.allLiteralsCovered target = true)
    (hSource : source.Satisfies env) :
    target.Satisfies env := by
  rcases hSource with ⟨literal, hMem, hLiteral⟩
  rcases allLiteralsCovered_sound hCovered (Array.mem_def.mp hMem) with
    ⟨literal', hTargetMem, hEq⟩
  cases hEq
  exact satisfies_of_literal_mem hTargetMem hLiteral

/-- equality-resolution 结构结果的语义 soundness。 -/
theorem satisfies_equalityResolutionResult {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {sort : SimpleType σ} {left right : Term σ} {parent : Clause σ}
    (hTerm : StructuralEq.term left right = true)
    (hParent : parent.Satisfies env) :
    (equalityResolutionResult sort left right parent).Satisfies env := by
  rcases hParent with ⟨literal, hMem, hLiteral⟩
  cases hMatch : literal.matchesAtom false (.equal sort left right) with
  | false =>
      exact satisfies_of_literal_mem
        (mem_equalityResolutionResult (Array.mem_def.mp hMem) hMatch) hLiteral
  | true =>
      exact False.elim
        (Literal.not_satisfies_reflexive_negative_equality hTerm hMatch hLiteral)

/-- 闭子句在模型的任意类型正确自由变量环境中成立。 -/
def Valid {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ)
    (clause : Clause σ) : Prop :=
  ∀ env : Logic.HigherOrder.Env M, env.WellSorted [] → clause.Satisfies env

/-- 子句 substitution 的语义等价于更新 typed 自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv)
    (clause : Clause σ) :
    Satisfies sourceEnv (applySubstitution substitution clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.applySubstitution substitution) := by
      simpa [applySubstitution, Array.toList_map] using Array.mem_def.mp hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, rfl⟩
    exact ⟨sourceLiteral, Array.mem_def.mpr hSourceMem,
      (Literal.satisfies_applySubstitution_iff_of_envMatches
        hAdmissible hEnv sourceLiteral).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    refine ⟨Literal.applySubstitution substitution literal, ?_, ?_⟩
    · apply Array.mem_def.mpr
      simpa [applySubstitution, Array.toList_map] using
        (List.mem_map.mpr ⟨literal, Array.mem_def.mp hMem, rfl⟩)
    · exact (Literal.satisfies_applySubstitution_iff_of_envMatches
        hAdmissible hEnv literal).mpr hLiteral

/-- 子句自由变量平移的语义等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv)
    (clause : Clause σ) :
    Satisfies sourceEnv (renameFreeVars offset clause) ↔ Satisfies targetEnv clause := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.renameFreeVars offset) := by
      simpa [renameFreeVars, Array.toList_map] using Array.mem_def.mp hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, rfl⟩
    exact ⟨sourceLiteral, Array.mem_def.mpr hSourceMem,
      (Literal.satisfies_renameFreeVars_iff_of_envMatches hEnv sourceLiteral).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    refine ⟨Literal.renameFreeVars offset literal, ?_, ?_⟩
    · apply Array.mem_def.mpr
      simpa [renameFreeVars, Array.toList_map] using
        (List.mem_map.mpr ⟨literal, Array.mem_def.mp hMem, rfl⟩)
    · exact (Literal.satisfies_renameFreeVars_iff_of_envMatches hEnv literal).mpr hLiteral

/-- 满足父字句时，语义保持的文字替换结果仍被满足。 -/
theorem satisfies_replaceLiteral {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {needle replacement : Literal σ}
    (hReplacement : needle.Satisfies env → replacement.Satisfies env)
    (hClause : clause.Satisfies env) :
    (clause.replaceLiteral needle replacement).Satisfies env := by
  rcases hClause with ⟨literal, hMem, hSat⟩
  have hMemList : literal ∈ clause.literals.toList :=
    Array.mem_def.mp hMem
  rcases satisfies_replaceLiteralList hReplacement
      ⟨literal, hMemList, hSat⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness, Array.mem_def.mpr (by simpa [replaceLiteral] using hWitnessMem),
    hWitnessSat⟩

/-- 字句是否为空。 -/
def isEmpty {σ : Signature.{u, v, w}} (clause : Clause σ) : Bool :=
  clause.literals.size == 0

/-- `isEmpty` 检查通过时，底层文字数组为空。 -/
theorem literals_eq_empty_of_isEmpty {σ : Signature.{u, v, w}} {clause : Clause σ}
    (hEmpty : clause.isEmpty = true) :
    clause.literals = #[] := by
  cases clause with
  | mk literals =>
      have hSize : literals.size = 0 := by
        have hBool : (literals.size == 0) = true := by
          simpa [isEmpty] using hEmpty
        cases h : literals.size with
        | zero => rfl
        | succ n =>
            have hFalse : (literals.size == 0) = false := by
              simp [h]
            rw [hFalse] at hBool
            cases hBool
      exact Array.eq_empty_of_size_eq_zero hSize

/-- 空字句在任意高阶环境中都不可能满足。 -/
theorem not_satisfies_of_isEmpty {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hEmpty : clause.isEmpty = true)
    (hSat : clause.Satisfies env) : False := by
  rcases hSat with ⟨literal, hMem, _hLiteral⟩
  rw [literals_eq_empty_of_isEmpty hEmpty] at hMem
  simp at hMem

end Clause

/-! ## AVATAR guard 与命题链接 -/

/-- AVATAR/CDCL 使用的 guard literal。 -/
abbrev GuardLit := PropResolution.Lit

/-- guard 集按合取解释。 -/
abbrev GuardSet := PropResolution.Clause

/-- guard 集的稳定规范化。 -/
def canonicalGuards (guards : GuardSet) : GuardSet :=
  PropResolution.canonicalClause guards

/-- 合并两个 guard 集。 -/
def mergeGuards (left right : GuardSet) : GuardSet :=
  canonicalGuards (left ++ right)

/-- guard 集的规范结构比较。 -/
def guardSetEq (left right : GuardSet) : Bool :=
  PropResolution.clauseEq (canonicalGuards left) (canonicalGuards right)

/-- theory conflict `Γ ⟹ ⊥` 对应的 learned clause `¬Γ`。 -/
def learnedClauseOfGuards (guards : GuardSet) : PropResolution.Clause :=
  canonicalGuards (guards.map PropResolution.Lit.neg)

/-- 规范插入不会产生输入之外的文字。 -/
private theorem mem_of_mem_propInsertCanonicalLitList {old lit : PropResolution.Lit} :
    ∀ {lits : List PropResolution.Lit},
      old ∈ PropResolution.insertCanonicalLitList lits lit → old = lit ∨ old ∈ lits
  | [], hMem => by
      simp [PropResolution.insertCanonicalLitList] at hMem
      exact Or.inl hMem
  | current :: rest, hMem => by
      by_cases hEq : current = lit
      · rw [PropResolution.insertCanonicalLitList] at hMem
        simp [hEq] at hMem
        rcases hMem with hOld | hRest
        · exact Or.inl hOld
        · exact Or.inr (List.mem_cons.mpr (Or.inr hRest))
      · by_cases hLe : PropResolution.Lit.le lit current
        · rw [PropResolution.insertCanonicalLitList] at hMem
          simp [hEq, hLe] at hMem ⊢
          exact hMem
        · rw [PropResolution.insertCanonicalLitList] at hMem
          simp [hEq, hLe] at hMem ⊢
          rcases hMem with hHead | hTail
          · exact Or.inr (Or.inl hHead)
          · rcases mem_of_mem_propInsertCanonicalLitList hTail with hOld | hRest
            · exact Or.inl hOld
            · exact Or.inr (Or.inr hRest)

/-- 规范化不会产生输入之外的文字。 -/
private theorem mem_of_mem_propCanonicalClauseList {lit : PropResolution.Lit} :
    ∀ {lits : List PropResolution.Lit},
      lit ∈ PropResolution.canonicalClauseList lits → lit ∈ lits
  | [], hMem => by
      simp [PropResolution.canonicalClauseList] at hMem
  | current :: rest, hMem => by
      rw [PropResolution.canonicalClauseList] at hMem
      rcases mem_of_mem_propInsertCanonicalLitList hMem with hCurrent | hRest
      · exact List.mem_cons.mpr (Or.inl hCurrent)
      · exact List.mem_cons.mpr
          (Or.inr (mem_of_mem_propCanonicalClauseList (lits := rest) hRest))

/-- 规范 guard 集中的文字来自原 guard 数组。 -/
private theorem mem_of_mem_propCanonicalClause {clause : PropResolution.Clause}
    {lit : PropResolution.Lit}
    (hMem : lit ∈ (PropResolution.canonicalClause clause).toList) :
    lit ∈ clause.toList := by
  simpa [PropResolution.canonicalClause] using
    mem_of_mem_propCanonicalClauseList hMem

/-- 带 AVATAR guard 的高阶字句。 -/
structure GuardedClause (σ : Signature.{u, v, w}) where
  guards : GuardSet := #[]
  clause : Clause σ

namespace GuardedClause

/-- 普通无 guard 字句。 -/
def plain {σ : Signature.{u, v, w}} (clause : Clause σ) : GuardedClause σ :=
  { clause := clause }

/-- guard 集是否为空。 -/
def unguarded {σ : Signature.{u, v, w}} (gclause : GuardedClause σ) : Bool :=
  gclause.guards.isEmpty

/-- 是否为无 guard 的全局空字句。 -/
def globallyEmpty {σ : Signature.{u, v, w}} (gclause : GuardedClause σ) : Bool :=
  gclause.unguarded && gclause.clause.isEmpty

/-- 是否为带 guard 的 theory conflict。 -/
def theoryConflict {σ : Signature.{u, v, w}} (gclause : GuardedClause σ) : Bool :=
  !gclause.unguarded && gclause.clause.isEmpty

end GuardedClause

/-- 通过闭子句 checker 的 proof-carrying 数据。 -/
structure CheckedClause (σ : Signature.{u, v, w}) [DecidableEq σ.BaseSort] where
  clause : Clause σ
  checked : clause.check = true

namespace CheckedClause

/-- 解包 checker 后得到闭子句良构性。 -/
theorem wellFormed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (checkedClause : CheckedClause σ) :
    checkedClause.clause.WellFormed [] :=
  Clause.checkWith_sound checkedClause.checked

end CheckedClause

namespace Beta

/-- β 归约节点的自包含 payload。结论由 payload 机械计算，不接收外部 result clause。 -/
structure Payload (σ : Signature.{u, v, w}) where
  domain : SimpleType σ
  codomain : SimpleType σ
  body : Term σ
  argument : Term σ

namespace Payload

/-- β payload 计算出的单位等词子句。 -/
def conclusion {σ : Signature.{u, v, w}} (payload : Payload σ) : Clause σ where
  literals := #[{
    polarity := true
    atom := .equal payload.codomain
      (.apply (.lam payload.domain payload.codomain payload.body) payload.argument)
      (Term.instantiate payload.argument payload.body)
  }]

/-- β payload 的可信边界直接复核计算结论的闭项类型。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (payload : Payload σ) : Bool :=
  payload.body.inferSortWith [payload.domain] == some payload.codomain &&
    payload.argument.inferSort? == some payload.domain &&
      payload.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {payload : Payload σ} (hCheck : payload.check = true) :
    payload.body.inferSortWith [payload.domain] = some payload.codomain ∧
      payload.argument.inferSort? = some payload.domain ∧
        payload.conclusion.check = true := by
  simpa [check, and_assoc] using hCheck

/-- checker 成功时，β 结论是良构闭子句。 -/
theorem wellFormed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {payload : Payload σ} (hCheck : payload.check = true) :
    payload.conclusion.WellFormed [] :=
  Clause.checkWith_sound (check_fields hCheck).2.2

/-- β 单位等词在任意满足 β 合同的高阶结构中成立。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (payload : Payload σ) (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted []) (hCheck : payload.check = true) :
    payload.conclusion.Satisfies env := by
  have hFields := check_fields hCheck
  let literal : Literal σ := {
    polarity := true
    atom := .equal payload.codomain
      (.apply (.lam payload.domain payload.codomain payload.body) payload.argument)
      (Term.instantiate payload.argument payload.body)
  }
  refine ⟨literal, ?_, ?_⟩
  · simp [Payload.conclusion, literal]
  · simp only [Literal.Satisfies, if_true, Atom.Satisfies, literal]
    rw [Logic.HigherOrder.ExtensionalContract.eval_beta contract,
      Logic.HigherOrder.Term.eval_instantiate]
    · intro value hValue
      exact
        Logic.HigherOrder.Term.eval_sort_of_inferSortWith
          (Logic.HigherOrder.Env.wellSorted_push hEnv hValue) hFields.1
    · exact
        Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
          (by simpa [Term.inferSort?] using hFields.2.1)

end Payload

/-- 已通过 β payload checker 的 proof-carrying 节点。 -/
structure CheckedPayload (σ : Signature.{u, v, w}) [DecidableEq σ.BaseSort] where
  payload : Payload σ
  checked : payload.check = true

namespace CheckedPayload

/-- checked β 节点解包后的结论良构性。 -/
theorem wellFormed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (checkedPayload : CheckedPayload σ) :
    checkedPayload.payload.conclusion.WellFormed [] :=
  Payload.wellFormed checkedPayload.checked

/-- checked β 节点的对象层 soundness。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    (checkedPayload : CheckedPayload σ) (env : Logic.HigherOrder.Env M) :
    env.WellSorted [] →
      checkedPayload.payload.conclusion.Satisfies env :=
  fun hEnv => Payload.sound contract checkedPayload.payload env hEnv checkedPayload.checked

end CheckedPayload

end Beta

namespace Eta

/-- η 展开节点只保存函数项与箭头类型。 -/
structure Payload (σ : Signature.{u, v, w}) where
  domain : SimpleType σ
  codomain : SimpleType σ
  function : Term σ

namespace Payload

/-- η payload 计算出的规范单位等词子句。 -/
def conclusion {σ : Signature.{u, v, w}} (payload : Payload σ) : Clause σ where
  literals := #[{
    polarity := true
    atom := .equal (.arrow payload.domain payload.codomain)
      (.lam payload.domain payload.codomain
        (.apply (Term.shiftAbove 1 0 payload.function)
          (.var (.bvar payload.domain 0))))
      payload.function
  }]

/-- η payload 的闭项类型检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (payload : Payload σ) : Bool :=
  payload.function.inferSort? ==
      some (.arrow payload.domain payload.codomain) &&
    payload.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {payload : Payload σ} (hCheck : payload.check = true) :
    payload.function.inferSort? =
        some (.arrow payload.domain payload.codomain) ∧
      payload.conclusion.check = true := by
  simpa [check] using hCheck

/-- checker 成功时，η 结论是良构闭子句。 -/
theorem wellFormed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {payload : Payload σ} (hCheck : payload.check = true) :
    payload.conclusion.WellFormed [] :=
  Clause.checkWith_sound (check_fields hCheck).2

/-- η 单位等词在任意外延高阶结构中成立。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (payload : Payload σ) (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted []) (hCheck : payload.check = true) :
    payload.conclusion.Satisfies env := by
  have hFields := check_fields hCheck
  let literal : Literal σ := {
    polarity := true
    atom := .equal (.arrow payload.domain payload.codomain)
      (.lam payload.domain payload.codomain
        (.apply (Term.shiftAbove 1 0 payload.function)
          (.var (.bvar payload.domain 0))))
      payload.function
  }
  refine ⟨literal, ?_, ?_⟩
  · simp [Payload.conclusion, literal]
  · simp only [Literal.Satisfies, if_true, Atom.Satisfies, literal]
    exact Logic.HigherOrder.ExtensionalContract.eval_eta contract env
      payload.domain payload.codomain payload.function <|
        Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
          (by simpa [Term.inferSort?] using hFields.1)

end Payload

/-- 已通过 η payload checker 的 proof-carrying 节点。 -/
structure CheckedPayload (σ : Signature.{u, v, w}) [DecidableEq σ.BaseSort] where
  payload : Payload σ
  checked : payload.check = true

namespace CheckedPayload

/-- checked η 节点解包后的结论良构性。 -/
theorem wellFormed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (checkedPayload : CheckedPayload σ) :
    checkedPayload.payload.conclusion.WellFormed [] :=
  Payload.wellFormed checkedPayload.checked

/-- checked η 节点的对象层 soundness。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    (checkedPayload : CheckedPayload σ) (env : Logic.HigherOrder.Env M) :
    env.WellSorted [] →
      checkedPayload.payload.conclusion.Satisfies env :=
  fun hEnv => Payload.sound contract checkedPayload.payload env hEnv checkedPayload.checked

end CheckedPayload

end Eta

namespace BetaEta

/--
βη 等价的原生可回放轨迹。

同余构造每次只改写一个直接子项；`trans` 的中间项由 checker 做结构对齐，
因此材料化器可以组合任意深度的归约而无需信任外部 normalized term。
-/
inductive Trace (σ : Signature.{u, v, w}) where
  | refl (term : Term σ)
  | appArgument (symbol : σ.FuncSymbol) (before : List (Term σ))
      (argument : Trace σ) (suffix : List (Term σ))
  | applyFunction (function : Trace σ) (argument : Term σ)
  | applyArgument (function : Term σ) (argument : Trace σ)
  | lam (domain codomain : SimpleType σ) (body : Trace σ)
  | beta (domain codomain : SimpleType σ) (body argument : Term σ)
  | eta (domain codomain : SimpleType σ) (function : Term σ)
  | trans (first second : Trace σ)

namespace Trace

/-- βη 轨迹的起点项。 -/
def source {σ : Signature.{u, v, w}} : Trace σ → Term σ
  | .refl term => term
  | .appArgument symbol before argument suffix =>
      .app symbol (before ++ [argument.source] ++ suffix)
  | .applyFunction function argument => .apply function.source argument
  | .applyArgument function argument => .apply function argument.source
  | .lam domain codomain body => .lam domain codomain body.source
  | .beta domain codomain body argument =>
      .apply (.lam domain codomain body) argument
  | .eta domain codomain function =>
      .lam domain codomain
        (.apply (Term.shiftAbove 1 0 function) (.var (.bvar domain 0)))
  | .trans first _second => first.source

/-- βη 轨迹的终点项。 -/
def target {σ : Signature.{u, v, w}} : Trace σ → Term σ
  | .refl term => term
  | .appArgument symbol before argument suffix =>
      .app symbol (before ++ [argument.target] ++ suffix)
  | .applyFunction function argument => .apply function.target argument
  | .applyArgument function argument => .apply function argument.target
  | .lam domain codomain body => .lam domain codomain body.target
  | .beta _domain _codomain body argument => Term.instantiate argument body
  | .eta _domain _codomain function => function
  | .trans _first second => second.target

/-- βη 轨迹在当前绑定上下文中的局部可信边界。 -/
def checkWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] (context : Context σ) : Trace σ → Bool
  | .refl _ => true
  | .appArgument _ _ argument _ => argument.checkWith context
  | .applyFunction function _ => function.checkWith context
  | .applyArgument _ argument => argument.checkWith context
  | .lam domain _ body => body.checkWith (domain :: context)
  | .beta domain codomain body argument =>
      body.inferSortWith (domain :: context) == some codomain &&
        argument.inferSortWith context == some domain
  | .eta domain codomain function =>
      function.inferSortWith context == some (.arrow domain codomain)
  | .trans first second =>
      first.checkWith context && second.checkWith context &&
        StructuralEq.term first.target second.source

/-- 闭项 βη 轨迹的可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] (trace : Trace σ) : Bool :=
  trace.checkWith []

/-- checked βη 轨迹在任意外延高阶结构中保持项解释。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol]
    {M : Structure.{u, v, w, x} σ}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (trace : Trace σ) (context : Context σ)
    (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted context)
    (hCheck : trace.checkWith context = true) :
    Term.eval env trace.source = Term.eval env trace.target := by
  induction trace generalizing context env with
  | refl term =>
      rfl
  | appArgument symbol before argument suffix ih =>
      simp only [source, target, Term.eval]
      congr 1
      simp [List.map_append, ih context env hEnv hCheck]
  | applyFunction function argument ih =>
      simp only [source, target, Term.eval]
      exact congrArg (fun value => M.applyInterp value (Term.eval env argument))
        (ih context env hEnv hCheck)
  | applyArgument function argument ih =>
      simp only [source, target, Term.eval]
      exact congrArg (M.applyInterp (Term.eval env function))
        (ih context env hEnv hCheck)
  | lam domain codomain body ih =>
      simp only [source, target, Term.eval]
      apply contract.lambdaCongr
      intro value hValue
      exact ih (domain :: context) (env.push value)
        (Logic.HigherOrder.Env.wellSorted_push hEnv hValue) hCheck
  | beta domain codomain body argument =>
      have hFields :
          body.inferSortWith (domain :: context) = some codomain ∧
            argument.inferSortWith context = some domain := by
        simpa [checkWith] using hCheck
      rw [source, target, Logic.HigherOrder.ExtensionalContract.eval_beta contract,
        Logic.HigherOrder.Term.eval_instantiate]
      · intro value hValue
        exact
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith
            (Logic.HigherOrder.Env.wellSorted_push hEnv hValue) hFields.1
      · exact
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
            hFields.2
  | eta domain codomain function =>
      have hFunction :
          function.inferSortWith context = some (.arrow domain codomain) := by
        simpa [checkWith] using hCheck
      exact Logic.HigherOrder.ExtensionalContract.eval_eta contract env
        domain codomain function <|
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
            hFunction
  | trans first second ihFirst ihSecond =>
      have hFields :
          (first.checkWith context = true ∧ second.checkWith context = true) ∧
            StructuralEq.term first.target second.source = true := by
        simpa [checkWith] using hCheck
      have hMiddle : first.target = second.source :=
        StructuralEq.term_sound first.target second.source hFields.2
      calc
        Term.eval env first.source = Term.eval env first.target :=
          ihFirst context env hEnv hFields.1.1
        _ = Term.eval env second.source := congrArg (Term.eval env) hMiddle
        _ = Term.eval env second.target := ihSecond context env hEnv hFields.1.2

end Trace

end BetaEta

/-! ## 父节点局部规则 -/

/-- 局部规则引用父节点时携带的机械结论快照。 -/
structure ParentClause (σ : Signature.{u, v, w}) where
  id : Nat
  clause : Clause σ

namespace ParentClause

/-- 父节点编号必须出现在当前节点的父边数组中。 -/
def idIn {σ : Signature.{u, v, w}} (parents : Array Nat)
    (parent : ParentClause σ) : Bool :=
  parents.contains parent.id

/-- `idIn` 检查通过时，父节点编号出现在父边列表中。 -/
theorem mem_toList_of_idIn {σ : Signature.{u, v, w}} {parents : Array Nat}
    {parent : ParentClause σ} (hIn : parent.idIn parents = true) :
    parent.id ∈ parents.toList := by
  have hArray : parent.id ∈ parents := by
    simpa [idIn] using hIn
  exact Array.mem_def.mp hArray

end ParentClause

/-! ## HO-AVATAR component 描述 -/

namespace Avatar

/-- HO component 分解使用的带类型自由变量。 -/
structure FreeVariable (σ : Signature.{u, v, w}) where
  sort : SimpleType σ
  id : Nat

namespace FreeVariable

/-- 带类型自由变量的可计算结构比较。 -/
def eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (left right : FreeVariable σ) : Bool :=
  decide (left.sort = right.sort) && left.id == right.id

end FreeVariable

/-- 向有限支持中插入尚未出现的带类型自由变量。 -/
def pushFreeVariableUnique {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] (support : Array (FreeVariable σ))
    (candidate : FreeVariable σ) : Array (FreeVariable σ) :=
  if support.any fun existing => FreeVariable.eq existing candidate then
    support
  else
    support.push candidate

/-- 合并两个带类型自由变量支持。 -/
def mergeFreeSupport {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] (left right : Array (FreeVariable σ)) :
    Array (FreeVariable σ) :=
  right.toList.foldl pushFreeVariableUnique left

mutual
  /-- 原生 HO 项的 typed 自由变量支持；`apply/lam` 递归透明。 -/
  def termFreeSupport {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] :
      Term σ → Array (FreeVariable σ)
    | .var (.bvar _ _) => #[]
    | .var (.fvar sort id) => #[{ sort := sort, id := id }]
    | .app _ arguments => termListFreeSupport arguments
    | .apply function argument =>
        mergeFreeSupport (termFreeSupport function) (termFreeSupport argument)
    | .lam _ _ body => termFreeSupport body

  /-- 原生 HO 项列表的 typed 自由变量支持。 -/
  def termListFreeSupport {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] :
      List (Term σ) → Array (FreeVariable σ)
    | [] => #[]
    | term :: rest =>
        mergeFreeSupport (termFreeSupport term) (termListFreeSupport rest)
end

/-- 原生 HO 原子的 typed 自由变量支持。 -/
def atomFreeSupport {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] :
    Atom σ → Array (FreeVariable σ)
  | .rel _ arguments => termListFreeSupport arguments
  | .equal _ left right =>
      mergeFreeSupport (termFreeSupport left) (termFreeSupport right)

/-- 原生 HO literal 的 typed 自由变量支持。 -/
def literalFreeSupport {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (literal : Literal σ) : Array (FreeVariable σ) :=
  atomFreeSupport literal.atom

/-- 原生 HO clause 的 typed 自由变量支持。 -/
def clauseFreeSupport {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) : Array (FreeVariable σ) :=
  clause.literals.toList.foldl
    (fun support literal => mergeFreeSupport support (literalFreeSupport literal)) #[]

/-- 两个 typed 自由变量支持是否相交。 -/
def supportsOverlap {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (left right : Array (FreeVariable σ)) : Bool :=
  left.any fun candidate =>
    right.any fun existing => FreeVariable.eq candidate existing

/-- 按 literal 索引抽取一个原生 HO component clause。 -/
def clauseAtIndices {σ : Signature.{u, v, w}} (clause : Clause σ)
    (indices : Array Nat) : Clause σ := {
  literals := indices.filterMap fun index => clause.literals[index]?
}

/-- 一组 component clause 的 typed 自由变量支持是否两两不交。 -/
def pairwiseSupportDisjoint {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] : List (Clause σ) → Bool
  | [] => true
  | head :: rest =>
      rest.all
        (fun other =>
          !supportsOverlap (clauseFreeSupport head) (clauseFreeSupport other)) &&
        pairwiseSupportDisjoint rest

/-- 一轮 component 闭包扫描的纯状态。 -/
private structure ComponentScanState (σ : Signature.{u, v, w}) where
  seen : Array Bool
  indices : Array Nat
  support : Array (FreeVariable σ)
  changed : Bool := false

/-- 扫描全部 literal，把与当前支持相交的尚未访问文字加入 component。 -/
private def scanComponent {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) : List Nat → ComponentScanState σ → ComponentScanState σ
  | [], state => state
  | index :: rest, state =>
      if hIndex : index < clause.literals.size then
        if Array.getD state.seen index false then
          scanComponent clause rest state
        else
          let candidate := literalFreeSupport clause.literals[index]
          if supportsOverlap state.support candidate then
            scanComponent clause rest {
              seen := Array.set! state.seen index true
              indices := Array.push state.indices index
              support := mergeFreeSupport state.support candidate
              changed := true
            }
          else
            scanComponent clause rest state
      else
        scanComponent clause rest state

/-- 有限次扫描计算 typed 自由变量连通闭包。 -/
private def closeComponent {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) :
    Nat → ComponentScanState σ → ComponentScanState σ
  | 0, state => state
  | fuel + 1, state =>
      let next := scanComponent clause (List.range clause.literals.size)
        { state with changed := false }
      if next.changed then
        closeComponent clause fuel next
      else
        next

/-- 依次选取尚未访问的 literal，生成全部 component。 -/
private def splitClauseLoop {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) :
    List Nat → Array Bool → Array (Array Nat × Clause σ) →
      Array (Array Nat × Clause σ)
  | [], _seen, components => components
  | start :: rest, seen, components =>
      if hStart : start < clause.literals.size then
        if Array.getD seen start false then
          splitClauseLoop clause rest seen components
        else
          let closed := closeComponent clause (clause.literals.size + 1) {
            seen := Array.set! seen start true
            indices := #[start]
            support := literalFreeSupport clause.literals[start]
          }
          splitClauseLoop clause rest closed.seen
            (components.push
              (closed.indices, clauseAtIndices clause closed.indices))
      else
        splitClauseLoop clause rest seen components

/-- 按 typed 自由变量连通性拆分一个原生 HO clause。 -/
def splitClause {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (clause : Clause σ) : Array (Array Nat × Clause σ) :=
  splitClauseLoop clause (List.range clause.literals.size)
    (List.replicate clause.literals.size false).toArray #[]

end Avatar

namespace Substitution

/-- typed substitution 图节点的显式证据。 -/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  substitution : TermSubstitution σ

namespace Evidence

/-- substitution 节点的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.applySubstitution evidence.substitution

/-- substitution 节点的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.substitution.check &&
        evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    (((evidence.parent.idIn parents = true ∧ evidence.parent.clause.check = true) ∧
      evidence.substitution.check = true) ∧ evidence.conclusion.check = true) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边数组中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true :=
  (check_fields hCheck).1.1.1

/-- typed substitution 保持父字句的全环境有效性。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hAdmissible : evidence.substitution.Admissible :=
    TermSubstitution.check_sound (check_fields hCheck).1.2
  intro sourceEnv hSource
  let targetEnv :=
    TermSubstitution.semanticEnv evidence.substitution sourceEnv
  have hTarget : targetEnv.WellSorted [] :=
    TermSubstitution.semanticEnv_wellSorted hAdmissible hSource
  have hParentSat : evidence.parent.clause.Satisfies targetEnv :=
    hParent targetEnv hTarget
  exact
    (Clause.satisfies_applySubstitution_iff_of_envMatches hAdmissible
      (TermSubstitution.semanticEnv_matches
        (substitution := evidence.substitution) (sourceEnv := sourceEnv))
      evidence.parent.clause).mpr hParentSat

end Evidence

end Substitution

namespace StandardizeApart

/-- 自由变量平移图节点的显式证据。 -/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  offset : Nat

namespace Evidence

/-- standardize-apart 节点的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.renameFreeVars evidence.offset

/-- standardize-apart 节点的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    ((evidence.parent.idIn parents = true ∧ evidence.parent.clause.check = true) ∧
      evidence.conclusion.check = true) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边数组中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true :=
  (check_fields hCheck).1.1

/-- 自由变量标准化分离保持父字句的全环境有效性。 -/
theorem sound {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (evidence : Evidence σ) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  intro sourceEnv hSource
  let targetEnv := FreeVarRenaming.semanticEnv evidence.offset sourceEnv
  have hTarget : targetEnv.WellSorted [] :=
    FreeVarRenaming.semanticEnv_wellSorted hSource
  have hParentSat : evidence.parent.clause.Satisfies targetEnv :=
    hParent targetEnv hTarget
  exact
    (Clause.satisfies_renameFreeVars_iff_of_envMatches
      (FreeVarRenaming.semanticEnv_matches
        (offset := evidence.offset) (sourceEnv := sourceEnv))
      evidence.parent.clause).mpr hParentSat

end Evidence

end StandardizeApart

namespace Resolution

/-- 已经完成改名与 typed substitution 后的原生 HO resolution 证据。 -/
structure Evidence (σ : Signature.{u, v, w}) where
  left : ParentClause σ
  right : ParentClause σ
  pivot : Atom σ
  leftPolarity : Bool := true

namespace Evidence

/-- resolution 节点的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ :=
  Clause.resolutionResult evidence.leftPolarity evidence.pivot
    evidence.left.clause evidence.right.clause

/-- resolution 节点的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  (evidence.left.idIn parents && evidence.right.idIn parents) &&
    (evidence.left.clause.check && evidence.right.clause.check) &&
      (evidence.left.clause.containsMatching evidence.leftPolarity evidence.pivot &&
        evidence.right.clause.containsMatching (!evidence.leftPolarity) evidence.pivot) &&
        evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    (((evidence.left.idIn parents = true ∧ evidence.right.idIn parents = true) ∧
      (evidence.left.clause.check = true ∧ evidence.right.clause.check = true)) ∧
        (evidence.left.clause.containsMatching evidence.leftPolarity evidence.pivot = true ∧
          evidence.right.clause.containsMatching (!evidence.leftPolarity)
            evidence.pivot = true)) ∧
              evidence.conclusion.check = true := by
  simpa [check] using hCheck

/-- checker 成功时，左父节点编号确实出现在父边列表中。 -/
theorem leftIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.left.idIn parents = true :=
  (check_fields hCheck).1.1.1.1

/-- checker 成功时，右父节点编号确实出现在父边列表中。 -/
theorem rightIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.right.idIn parents = true :=
  (check_fields hCheck).1.1.1.2

/-- resolution 把两个父字句的全环境有效性传递到机械结果。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    (hLeft : evidence.left.clause.Valid M)
    (hRight : evidence.right.clause.Valid M) :
    evidence.conclusion.Valid M :=
  fun env hEnv => Clause.satisfies_resolutionResult (hLeft env hEnv) (hRight env hEnv)

end Evidence

end Resolution

namespace Factoring

/-- factoring 证据显式保存结果，以兼容搜索器的去重与稳定重排。 -/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  conclusion : Clause σ

namespace Evidence

/-- factoring 的可信边界检查父子句文字集合等价且结果不增大。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  (evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (evidence.conclusion.check &&
      evidence.parent.clause.allLiteralsCovered evidence.conclusion) &&
        (evidence.conclusion.allLiteralsCovered evidence.parent.clause &&
          decide (evidence.conclusion.literals.size <= evidence.parent.clause.literals.size))

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    (((evidence.parent.idIn parents = true ∧ evidence.parent.clause.check = true) ∧
      (evidence.conclusion.check = true ∧
        evidence.parent.clause.allLiteralsCovered evidence.conclusion = true)) ∧
          (evidence.conclusion.allLiteralsCovered evidence.parent.clause = true ∧
            decide
              (evidence.conclusion.literals.size <=
                evidence.parent.clause.literals.size) = true)) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边列表中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true :=
  (check_fields hCheck).1.1.1

/-- factoring 把父字句的全环境有效性传递到显式结果。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hCovered :
      evidence.parent.clause.allLiteralsCovered evidence.conclusion = true :=
    (check_fields hCheck).1.2.2
  intro env hEnv
  exact Clause.satisfies_of_allLiteralsCovered hCovered (hParent env hEnv)

end Evidence

end Factoring

namespace EqualityResolution

/-- 已经完成 typed substitution 后的原生 HO equality-resolution 证据。 -/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  sort : SimpleType σ
  left : Term σ
  right : Term σ

namespace Evidence

/-- equality-resolution 节点的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ :=
  Clause.equalityResolutionResult evidence.sort evidence.left evidence.right
    evidence.parent.clause

/-- equality-resolution 节点的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  (evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (StructuralEq.term evidence.left evidence.right &&
      evidence.parent.clause.containsMatching false
        (.equal evidence.sort evidence.left evidence.right)) &&
        evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    (((evidence.parent.idIn parents = true ∧ evidence.parent.clause.check = true) ∧
      (StructuralEq.term evidence.left evidence.right = true ∧
        evidence.parent.clause.containsMatching false
          (.equal evidence.sort evidence.left evidence.right) = true)) ∧
            evidence.conclusion.check = true) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边列表中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true :=
  (check_fields hCheck).1.1.1

/-- equality-resolution 把父字句全环境有效性传递到机械结果。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hTerm : StructuralEq.term evidence.left evidence.right = true :=
    (check_fields hCheck).1.2.1
  intro env hEnv
  exact Clause.satisfies_equalityResolutionResult hTerm (hParent env hEnv)

end Evidence

end EqualityResolution

namespace BooleanExtensionality

/--
布尔等词 βη 归一化证据。

证书核实际证明任意 simple type 上的等词归一化；搜索材料化层再把该规则收紧到
`bool`，从而把语义复用与搜索策略边界分离。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  literalIndex : Nat
  sort : SimpleType σ
  polarity : Bool
  left : BetaEta.Trace σ
  right : BetaEta.Trace σ

namespace Evidence

/-- 父字句中被归一化的等词文字。 -/
def needle {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := evidence.polarity
  atom := .equal evidence.sort evidence.left.source evidence.right.source

/-- βη 归一化后的等词文字。 -/
def replacement {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := evidence.polarity
  atom := .equal evidence.sort evidence.left.target evidence.right.target

/-- 选中文字必须精确等于两条 βη 轨迹的起点等词。 -/
def selectedCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Bool :=
  match evidence.parent.clause.literals[evidence.literalIndex]? with
  | some literal => literal.eq evidence.needle
  | none => false

/-- Boolean Extensionality 的机械结果：索引替换、移到末尾并确定性去重。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ :=
  (evidence.parent.clause.replaceLiteralAtEnd evidence.literalIndex
    evidence.replacement).normalize

/-- Boolean Extensionality 的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  ((evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (evidence.selectedCheck && (evidence.left.check && evidence.right.check))) &&
      (((decide (evidence.left.source.inferSort? = some evidence.sort) &&
        decide (evidence.right.source.inferSort? = some evidence.sort)) &&
          (decide (evidence.left.target.inferSort? = some evidence.sort) &&
            decide (evidence.right.target.inferSort? = some evidence.sort))) &&
        evidence.conclusion.check)

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    (((evidence.parent.idIn parents = true ∧
      evidence.parent.clause.check = true) ∧
        (evidence.selectedCheck = true ∧
          (evidence.left.check = true ∧ evidence.right.check = true))) ∧
      (((decide (evidence.left.source.inferSort? = some evidence.sort) = true ∧
        decide (evidence.right.source.inferSort? = some evidence.sort) = true) ∧
          (decide (evidence.left.target.inferSort? = some evidence.sort) = true ∧
            decide (evidence.right.target.inferSort? = some evidence.sort) = true)) ∧
        evidence.conclusion.check = true)) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边数组中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true :=
  (check_fields hCheck).1.1.1

/-- checker 成功时，索引指向的文字就是轨迹起点等词。 -/
theorem selected_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.clause.literals[evidence.literalIndex]? =
      some evidence.needle := by
  have hSelected : evidence.selectedCheck = true :=
    (check_fields hCheck).1.2.1
  unfold selectedCheck at hSelected
  cases hLiteral :
      evidence.parent.clause.literals[evidence.literalIndex]? with
  | none =>
      simp [hLiteral] at hSelected
  | some literal =>
      have hEq : literal.eq evidence.needle = true := by
        simpa [hLiteral] using hSelected
      exact congrArg some (Literal.eq_sound literal evidence.needle hEq)

/-- βη 轨迹把选中文字满足性双向传递到归一化文字。 -/
theorem satisfies_iff_replacement {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted []) :
    evidence.needle.Satisfies env ↔ evidence.replacement.Satisfies env := by
  have hFields := check_fields hCheck
  have hLeft :
      Term.eval env evidence.left.source = Term.eval env evidence.left.target :=
    evidence.left.sound contract [] env hEnv hFields.1.2.2.1
  have hRight :
      Term.eval env evidence.right.source = Term.eval env evidence.right.target :=
    evidence.right.sound contract [] env hEnv hFields.1.2.2.2
  have hAtom :
      (Term.eval env evidence.left.source =
        Term.eval env evidence.right.source) ↔
      (Term.eval env evidence.left.target =
        Term.eval env evidence.right.target) := by
    rw [hLeft, hRight]
  cases hPolarity : evidence.polarity with
  | false =>
      simpa [needle, replacement, Literal.Satisfies, Atom.Satisfies, hPolarity]
        using not_congr hAtom
  | true =>
      simpa [needle, replacement, Literal.Satisfies, Atom.Satisfies, hPolarity]
        using hAtom

/-- Boolean Extensionality 把父字句全环境有效性传递到机械结果。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  intro env hEnv
  apply Clause.satisfies_normalize
  exact Clause.satisfies_replaceLiteralAtEnd
    (evidence.selected_of_check hCheck)
    ((evidence.satisfies_iff_replacement contract hCheck env hEnv).mp)
    (hParent env hEnv)

end Evidence

end BooleanExtensionality

/-! ## 高阶上下文重写与 superposition -/

/--
原生高阶项的一孔上下文。

`app` 处理签名函数的未柯里化参数，两个 `apply` 分支分别进入函数位与实参位；
`lam` 直接进入局部无名 body，不经过 lambda lifting。
-/
inductive TermContext (σ : Signature.{u, v, w}) where
  | hole
  | app (symbol : σ.FuncSymbol) (before : List (Term σ))
      (context : TermContext σ) (suffix : List (Term σ))
  | applyFunction (context : TermContext σ) (argument : Term σ)
  | applyArgument (function : Term σ) (context : TermContext σ)
  | lam (domain codomain : SimpleType σ) (context : TermContext σ)

namespace TermContext

/-- 用一个项填充唯一洞位。 -/
def fill {σ : Signature.{u, v, w}} : TermContext σ → Term σ → Term σ
  | .hole, term => term
  | .app symbol before context suffix, term =>
      .app symbol (before ++ [context.fill term] ++ suffix)
  | .applyFunction context argument, term =>
      .apply (context.fill term) argument
  | .applyArgument function context, term =>
      .apply function (context.fill term)
  | .lam domain codomain context, term =>
      .lam domain codomain (context.fill term)

/--
空绑定上下文中的同类型等值项可在任意原生 HO 项上下文中替换。

`lam` 分支先用闭项的环境不变性把等式搬到 `env.push value`，再由
`ExtensionalContract.lambdaCongr` 封装函数值同余；这也是排除变量捕获的语义边界。
-/
theorem eval_fill_eq_of_eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    {env : Logic.HigherOrder.Env M} {context : TermContext σ}
    {lhs rhs : Term σ} {sort : SimpleType σ}
    (hLhs : TermWellSorted [] lhs sort) (hRhs : TermWellSorted [] rhs sort)
    (hEq : Term.eval env lhs = Term.eval env rhs) :
    Term.eval env (context.fill lhs) = Term.eval env (context.fill rhs) := by
  induction context generalizing env lhs rhs sort with
  | hole =>
      simpa [fill] using hEq
  | app symbol before context suffix ih =>
      simp only [fill, Term.eval]
      congr 1
      simp [List.map_append, ih hLhs hRhs hEq]
  | applyFunction context argument ih =>
      simp only [fill, Term.eval]
      rw [ih hLhs hRhs hEq]
  | applyArgument function context ih =>
      simp only [fill, Term.eval]
      rw [ih hLhs hRhs hEq]
  | lam domain codomain context ih =>
      simp only [fill, Term.eval]
      apply contract.lambdaCongr
      intro value _hValue
      have hLhsPush : Term.eval (env.push value) lhs = Term.eval env lhs := by
        apply Term.eval_eq_of_wellSorted_env hLhs
        · intro index target hLookup
          simp [Context.lookup?] at hLookup
        · intro target id
          rfl
      have hRhsPush : Term.eval (env.push value) rhs = Term.eval env rhs := by
        apply Term.eval_eq_of_wellSorted_env hRhs
        · intro index target hLookup
          simp [Context.lookup?] at hLookup
        · intro target id
          rfl
      exact ih hLhs hRhs (hLhsPush.trans (hEq.trans hRhsPush.symm))

end TermContext

/-- 原子的一孔项上下文；等词上下文显式保存被改写项的 simple type。 -/
inductive AtomContext (σ : Signature.{u, v, w}) where
  | rel (symbol : σ.RelSymbol) (before : List (Term σ))
      (context : TermContext σ) (suffix : List (Term σ))
  | equalLeft (sort : SimpleType σ) (context : TermContext σ) (right : Term σ)
  | equalRight (sort : SimpleType σ) (left : Term σ) (context : TermContext σ)

namespace AtomContext

/-- 原子上下文是否位于等词两侧。 -/
def isEquality {σ : Signature.{u, v, w}} : AtomContext σ → Bool
  | .rel _ _ _ _ => false
  | .equalLeft _ _ _ => true
  | .equalRight _ _ _ => true

/-- 用一个项填充原子上下文。 -/
def fill {σ : Signature.{u, v, w}} : AtomContext σ → Term σ → Atom σ
  | .rel symbol before context suffix, term =>
      .rel symbol (before ++ [context.fill term] ++ suffix)
  | .equalLeft sort context right, term =>
      .equal sort (context.fill term) right
  | .equalRight sort left context, term =>
      .equal sort left (context.fill term)

/-- 等值项填入同一个原子上下文后，原子满足性保持等价。 -/
theorem satisfies_iff_of_eval_eq {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    {env : Logic.HigherOrder.Env M} {context : AtomContext σ}
    {lhs rhs : Term σ} {sort : SimpleType σ}
    (hLhs : TermWellSorted [] lhs sort) (hRhs : TermWellSorted [] rhs sort)
    (hEq : Term.eval env lhs = Term.eval env rhs) :
    (context.fill lhs).Satisfies env ↔ (context.fill rhs).Satisfies env := by
  cases context with
  | rel symbol before context suffix =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      have hArguments :
          (before ++ [context.fill lhs] ++ suffix).map (Term.eval env) =
            (before ++ [context.fill rhs] ++ suffix).map (Term.eval env) := by
        simp [List.map_append, hTerm]
      change
        M.relInterp symbol
            ((before ++ [context.fill lhs] ++ suffix).map (Term.eval env)) ↔
          M.relInterp symbol
            ((before ++ [context.fill rhs] ++ suffix).map (Term.eval env))
      rw [hArguments]
  | equalLeft atomSort context right =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      simp only [fill, Atom.Satisfies]
      rw [hTerm]
  | equalRight atomSort left context =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      simp only [fill, Atom.Satisfies]
      rw [hTerm]

end AtomContext

/-- 原生 HO 上下文重写规则的类别。 -/
inductive RewriteKind where
  | demodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, DecidableEq

namespace Rewrite

/--
正等词驱动的原生 HO 上下文重写证据。

父节点应先完成 standardize-apart 与 typed substitution；这里保存的上下文、方向和类型
全部由 checker 重新核对。规则类别只增加专用边界，不改变机械结论与语义证明。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  equality : ParentClause σ
  target : ParentClause σ
  context : AtomContext σ
  sort : SimpleType σ
  lhs : Term σ
  rhs : Term σ
  /-- true 表示父字句按 `rhs = lhs` 保存，但实际重写方向仍为 `lhs ↦ rhs`。 -/
  equalityReversed : Bool := false
  targetPolarity : Bool := true

namespace Evidence

/-- 等词父字句中实际保存的原子方向。 -/
def equalityAtom {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Atom σ :=
  if evidence.equalityReversed then
    .equal evidence.sort evidence.rhs evidence.lhs
  else
    .equal evidence.sort evidence.lhs evidence.rhs

/-- 被上下文重写命中的目标文字。 -/
def needle {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := evidence.targetPolarity
  atom := evidence.context.fill evidence.lhs

/-- 用右侧项填洞后的替换文字。 -/
def replacement {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := evidence.targetPolarity
  atom := evidence.context.fill evidence.rhs

/-- 重写的机械结果：删除选中等词并改写目标字句中的全部相同文字。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ where
  literals :=
    (Clause.filterOutList true evidence.equalityAtom
        evidence.equality.clause.literals.toList ++
      (evidence.target.clause.replaceLiteral evidence.needle
        evidence.replacement).literals.toList).toArray

/-- 各重写规则在公共证据之外的专用可信边界。 -/
def kindCheck {σ : Signature.{u, v, w}} (kind : RewriteKind)
    (evidence : Evidence σ) : Bool :=
  match kind with
  | .demodulation =>
      decide (evidence.equality.clause.literals.size = 1)
  | .positiveSuperposition =>
      evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality
  | .extensionalParamodulation =>
      evidence.targetPolarity &&
        (match evidence.sort with
        | .arrow .. => true
        | .base _ =>
            match evidence.lhs with
            | .apply .. => true
            | .lam .. => true
            | _ => false)

/-- 原生 HO 上下文重写的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (kind : RewriteKind) (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  (((((((evidence.equality.idIn parents && evidence.target.idIn parents) &&
    (evidence.equality.clause.check && evidence.target.clause.check)) &&
      evidence.equality.clause.containsMatching true
        evidence.equalityAtom) &&
        evidence.target.clause.containsLiteral evidence.needle) &&
          decide (evidence.lhs.inferSort? = some evidence.sort)) &&
            decide (evidence.rhs.inferSort? = some evidence.sort)) &&
              kindCheck kind evidence) &&
                evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check kind parents = true) :
    ((((((((evidence.equality.idIn parents = true ∧
      evidence.target.idIn parents = true) ∧
        (evidence.equality.clause.check = true ∧
          evidence.target.clause.check = true)) ∧
            evidence.equality.clause.containsMatching true
              evidence.equalityAtom = true) ∧
              evidence.target.clause.containsLiteral evidence.needle = true) ∧
                decide (evidence.lhs.inferSort? = some evidence.sort) = true) ∧
                  decide (evidence.rhs.inferSort? = some evidence.sort) = true) ∧
                    kindCheck kind evidence = true) ∧
                      evidence.conclusion.check = true) := by
  simpa [check] using hCheck

/-- checker 成功时，等词父节点编号位于父边数组中。 -/
theorem equalityIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check kind parents = true) :
    evidence.equality.idIn parents = true :=
  (check_fields hCheck).1.1.1.1.1.1.1.1

/-- checker 成功时，目标父节点编号位于父边数组中。 -/
theorem targetIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check kind parents = true) :
    evidence.target.idIn parents = true :=
  (check_fields hCheck).1.1.1.1.1.1.1.2

/-- 满足被选中正等词的文字给出两端项解释相等。 -/
private theorem eval_eq_of_parent {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {evidence : Evidence σ} {literal : Literal σ}
    (hMatch :
      literal.matchesAtom true evidence.equalityAtom = true)
    (hLiteral : literal.Satisfies env) :
    Term.eval env evidence.lhs = Term.eval env evidence.rhs := by
  rcases Literal.matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  cases literal with
  | mk polarity atom =>
      cases hPolarity
      cases hReversed : evidence.equalityReversed with
      | false =>
          have hAtom' :
              atom = (.equal evidence.sort evidence.lhs evidence.rhs : Atom σ) := by
            simpa [equalityAtom, hReversed] using hAtom
          cases hAtom'
          simpa [Literal.Satisfies, Atom.Satisfies] using hLiteral
      | true =>
          have hAtom' :
              atom = (.equal evidence.sort evidence.rhs evidence.lhs : Atom σ) := by
            simpa [equalityAtom, hReversed] using hAtom
          cases hAtom'
          have hReverse :
              Term.eval env evidence.rhs = Term.eval env evidence.lhs := by
            simpa [Literal.Satisfies, Atom.Satisfies] using hLiteral
          exact hReverse.symm

/-- 等式在目标原子上下文中诱导重写前后文字满足性等价。 -/
private theorem satisfies_iff_replacement {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    {evidence : Evidence σ} {kind : RewriteKind} {parents : Array Nat}
    (hCheck : evidence.check kind parents = true)
    (hEq : Term.eval env evidence.lhs = Term.eval env evidence.rhs) :
    evidence.needle.Satisfies env ↔ evidence.replacement.Satisfies env := by
  have hLhsCheck : evidence.lhs.inferSort? = some evidence.sort :=
    of_decide_eq_true (check_fields hCheck).1.1.1.2
  have hRhsCheck : evidence.rhs.inferSort? = some evidence.sort :=
    of_decide_eq_true (check_fields hCheck).1.1.2
  have hLhs : TermWellSorted [] evidence.lhs evidence.sort :=
    Term.inferSortWith_sound hLhsCheck
  have hRhs : TermWellSorted [] evidence.rhs evidence.sort :=
    Term.inferSortWith_sound hRhsCheck
  have hAtom :=
    AtomContext.satisfies_iff_of_eval_eq contract
      (context := evidence.context) hLhs hRhs hEq
  cases hPolarity : evidence.targetPolarity with
  | false =>
      simpa [needle, replacement, Literal.Satisfies, hPolarity] using not_congr hAtom
  | true =>
      simpa [needle, replacement, Literal.Satisfies, hPolarity] using hAtom

/-- 上下文重写把两个父字句的满足性传递到机械结果。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (evidence : Evidence σ) {kind : RewriteKind} {parents : Array Nat}
    (hCheck : evidence.check kind parents = true)
    (hEquality : evidence.equality.clause.Satisfies env)
    (hTarget : evidence.target.clause.Satisfies env) :
    evidence.conclusion.Satisfies env := by
  rcases hEquality with ⟨equalityLiteral, hEqualityMem, hEqualitySat⟩
  cases hMatch :
      equalityLiteral.matchesAtom true evidence.equalityAtom with
  | false =>
      exact Clause.satisfies_of_literal_mem
        (by
          simp [conclusion]
          exact Or.inl
            (Clause.mem_filterOutList_of_mem_of_not_matches
              (Array.mem_def.mp hEqualityMem) hMatch))
        hEqualitySat
  | true =>
      have hEq : Term.eval env evidence.lhs = Term.eval env evidence.rhs :=
        eval_eq_of_parent hMatch hEqualitySat
      have hTarget' :
          (evidence.target.clause.replaceLiteral evidence.needle
            evidence.replacement).Satisfies env :=
        Clause.satisfies_replaceLiteral
          ((satisfies_iff_replacement contract hCheck hEq).mp) hTarget
      rcases hTarget' with ⟨literal, hMem, hLiteral⟩
      exact Clause.satisfies_of_literal_mem
        (by
          simp [conclusion]
          exact Or.inr hMem)
        hLiteral

end Evidence

end Rewrite

namespace ArgumentCongruence

/--
一参数 Argument Congruence 证据。

多参数版本由重复应用本规则得到；函数等式与实参都显式保存，结果字句由证据机械复算。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  domain : SimpleType σ
  codomain : SimpleType σ
  left : Term σ
  right : Term σ
  argument : Term σ

namespace Evidence

/-- 父字句中被扩展的正函数等式。 -/
def needle {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := true
  atom := .equal (.arrow evidence.domain evidence.codomain)
    evidence.left evidence.right

/-- 对函数等式两侧应用同一实参后的正等词。 -/
def replacement {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := true
  atom := .equal evidence.codomain
    (.apply evidence.left evidence.argument)
    (.apply evidence.right evidence.argument)

/-- Argument Congruence 的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.replaceLiteral evidence.needle evidence.replacement

/-- Argument Congruence 的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.parent.clause.containsLiteral evidence.needle &&
        decide (evidence.argument.inferSort? = some evidence.domain) &&
          evidence.conclusion.check

/-- checker 成功时，父节点编号确实出现在父边列表中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true := by
  have hFields :
      ((((evidence.parent.idIn parents = true ∧
        evidence.parent.clause.check = true) ∧
          evidence.parent.clause.containsLiteral evidence.needle = true) ∧
            decide (evidence.argument.inferSort? = some evidence.domain) = true) ∧
              evidence.conclusion.check = true) := by
    simpa [check] using hCheck
  exact hFields.1.1.1.1

/-- 满足函数等式时，对两侧应用同一实参后的等词仍成立。 -/
theorem replacement_satisfies {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (evidence : Evidence σ) (hNeedle : evidence.needle.Satisfies env) :
    evidence.replacement.Satisfies env := by
  simp only [needle, replacement, Literal.Satisfies, if_true, Atom.Satisfies,
    Logic.HigherOrder.Term.eval] at hNeedle ⊢
  exact congrArg
    (fun functionValue =>
      M.applyInterp functionValue (Logic.HigherOrder.Term.eval env evidence.argument))
    hNeedle

/-- Argument Congruence 把父字句满足性传递到机械结果字句。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (evidence : Evidence σ) (hParent : evidence.parent.clause.Satisfies env) :
    evidence.conclusion.Satisfies env :=
  Clause.satisfies_replaceLiteral (evidence.replacement_satisfies) hParent

end Evidence

end ArgumentCongruence

namespace FunctionExtensionality

/--
函数外延负规则的显式差异见证。

见证项固定为 `witnessSymbol(left, right)`；checker 同时复核符号角色、二元函数参数
类型和结果类型，不能由搜索器交付任意实参替代。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  domain : SimpleType σ
  codomain : SimpleType σ
  left : Term σ
  right : Term σ
  witnessSymbol : σ.FuncSymbol

namespace Evidence

/-- 父字句中被外延展开的负函数等式。 -/
def needle {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := false
  atom := .equal (.arrow evidence.domain evidence.codomain)
    evidence.left evidence.right

/-- 由显式符号构造的差异见证项。 -/
def witness {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Term σ :=
  .app evidence.witnessSymbol [evidence.left, evidence.right]

/-- 在差异见证上比较函数应用所得的负等词。 -/
def replacement {σ : Signature.{u, v, w}} (evidence : Evidence σ) : Literal σ where
  polarity := false
  atom := .equal evidence.codomain
    (.apply evidence.left evidence.witness)
    (.apply evidence.right evidence.witness)

/-- Function Extensionality 的机械结果字句。 -/
def conclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.replaceLiteral evidence.needle evidence.replacement

/-- Function Extensionality 的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.parent.clause.containsLiteral evidence.needle &&
        σ.isFunctionExtensionalityWitness evidence.witnessSymbol &&
          decide
            (σ.funcDomain evidence.witnessSymbol =
              [.arrow evidence.domain evidence.codomain,
                .arrow evidence.domain evidence.codomain]) &&
            decide (σ.funcCodomain evidence.witnessSymbol = evidence.domain) &&
              decide
                (evidence.left.inferSort? =
                  some (.arrow evidence.domain evidence.codomain)) &&
                decide
                  (evidence.right.inferSort? =
                    some (.arrow evidence.domain evidence.codomain)) &&
                  evidence.conclusion.check

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    ((((((((evidence.parent.idIn parents = true ∧
      evidence.parent.clause.check = true) ∧
        evidence.parent.clause.containsLiteral evidence.needle = true) ∧
          σ.isFunctionExtensionalityWitness evidence.witnessSymbol = true) ∧
            decide
              (σ.funcDomain evidence.witnessSymbol =
                [.arrow evidence.domain evidence.codomain,
                  .arrow evidence.domain evidence.codomain]) = true) ∧
              decide
                (σ.funcCodomain evidence.witnessSymbol = evidence.domain) = true) ∧
                decide
                  (evidence.left.inferSort? =
                    some (.arrow evidence.domain evidence.codomain)) = true) ∧
                  decide
                    (evidence.right.inferSort? =
                      some (.arrow evidence.domain evidence.codomain)) = true) ∧
                    evidence.conclusion.check = true) := by
  simpa [check] using hCheck

/-- checker 成功时，父节点编号确实出现在父边列表中。 -/
theorem parentIdIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {evidence : Evidence σ}
    (hCheck : evidence.check parents = true) :
    evidence.parent.idIn parents = true := by
  rcases check_fields hCheck with
    ⟨⟨⟨⟨⟨⟨⟨⟨hParent, _hParentCheck⟩, _hContains⟩, _hWitness⟩,
      _hDomain⟩, _hCodomain⟩, _hLeft⟩, _hRight⟩, _hConclusion⟩
  exact hParent

/-- 函数不等时，显式 `diff` 项把父负等词传递到应用后的负等词。 -/
theorem replacement_satisfies {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (contract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hEnv : env.WellSorted []) (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true)
    (hNeedle : evidence.needle.Satisfies env) :
    evidence.replacement.Satisfies env := by
  rcases check_fields hCheck with
    ⟨⟨⟨⟨⟨⟨⟨⟨_hParent, _hParentCheck⟩, _hContains⟩, hWitness⟩,
      hDomain⟩, hCodomain⟩, hLeft⟩, hRight⟩, _hConclusion⟩
  simp only [needle, replacement, witness, Literal.Satisfies, Atom.Satisfies]
    at hNeedle ⊢
  exact Logic.HigherOrder.ExtensionalWitnessContract.eval_distinguishes
    contract env hEnv evidence.witnessSymbol evidence.domain evidence.codomain
    evidence.left evidence.right hWitness (of_decide_eq_true hDomain)
    (of_decide_eq_true hCodomain) (of_decide_eq_true hLeft)
    (of_decide_eq_true hRight) hNeedle

/-- Function Extensionality 把父字句满足性传递到机械结果字句。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    (contract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hEnv : env.WellSorted []) (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Satisfies env) :
    evidence.conclusion.Satisfies env :=
  Clause.satisfies_replaceLiteral
    (evidence.replacement_satisfies contract hEnv hCheck) hParent

end Evidence

end FunctionExtensionality

/-! ## 原生高阶整图证书 -/

/-- 原生高阶反证问题；P0 阶段只保存搜索器交付的初始子句。 -/
structure Problem (σ : Signature.{u, v, w}) where
  initialClauses : Array (Clause σ)

namespace Problem

/-- 一个环境满足问题，指它满足全部初始子句。 -/
def Satisfies {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (problem : Problem σ) (env : Logic.HigherOrder.Env M) : Prop :=
  ∀ (index : Nat) (clause : Clause σ),
    problem.initialClauses[index]? = some clause → clause.Satisfies env

/-- 问题在模型的任意类型正确自由变量环境中成立。 -/
def Valid {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ)
    (problem : Problem σ) : Prop :=
  ∀ env : Logic.HigherOrder.Env M, env.WellSorted [] → problem.Satisfies env

end Problem

/-! ## Residual CDCL 证书 -/

/-- 命题文字到原生高阶文字的链接。 -/
structure PropLiteralLink (σ : Signature.{u, v, w}) where
  prop : PropResolution.Lit
  object : Literal σ

namespace PropLiteralLink

/-- HO atom map 与外部 guard valuation 组成的混合命题 valuation。 -/
def valuation {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (base : PropResolution.Valuation) (atomMap : Array (Atom σ))
    (env : Logic.HigherOrder.Env M) : PropResolution.Valuation :=
  fun var =>
    match atomMap[var]? with
    | some atom => atom.Satisfies env
    | none => base var

/-- guard/CDCL 专用变量必须位于对象 atom map 之外。 -/
def outsideAtomMap {σ : Signature.{u, v, w}} (atomMap : Array (Atom σ))
    (lit : PropResolution.Lit) : Bool :=
  match atomMap[lit.var]? with
  | some _ => false
  | none => true

/-- 命题文字链接与全局 HO atom map 是否一致。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (atomMap : Array (Atom σ)) (link : PropLiteralLink σ) : Bool :=
  link.prop.positive == link.object.polarity &&
    match atomMap[link.prop.var]? with
    | some atom => atom.eq link.object.atom
    | none => false

/-- 已检查的文字链接把 HO 文字满足性传递到混合命题 valuation。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropLiteralLink σ} (hCheck : link.check atomMap = true)
    (hObject : link.object.Satisfies env) :
    link.prop.Holds (valuation base atomMap env) := by
  cases link with
  | mk prop object =>
    cases prop with
    | mk var positive =>
      cases object with
      | mk objectPolarity objectAtom =>
        unfold check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPolarity, hAtomCheck⟩
        have hPolarityEq : positive = objectPolarity :=
          beq_iff_eq.mp hPolarity
        cases hLookup : atomMap[var]? with
        | none =>
            simp [hLookup] at hAtomCheck
        | some atom =>
            have hAtomEq : atom = objectAtom :=
              Atom.eq_sound atom objectAtom (by simpa [hLookup] using hAtomCheck)
            cases hPolarityEq
            cases positive <;>
              simpa [PropResolution.Lit.Holds, valuation, Literal.Satisfies,
                hLookup, hAtomEq] using hObject

/-- atom map 外部的变量在混合 valuation 中仍按 base valuation 解释。 -/
theorem holds_valuation_iff_of_outsideAtomMap
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Atom σ)}
    {env : Logic.HigherOrder.Env M} {lit : PropResolution.Lit}
    (hOutside : outsideAtomMap atomMap lit = true) :
    lit.Holds (valuation base atomMap env) ↔ lit.Holds base := by
  cases lit with
  | mk var positive =>
      unfold outsideAtomMap at hOutside
      cases hLookup : atomMap[var]? with
      | some atom =>
          simp [hLookup] at hOutside
      | none =>
          cases positive <;>
            simp [PropResolution.Lit.Holds, valuation, hLookup]

/-- atom map 外部性对文字取反保持。 -/
theorem outsideAtomMap_neg {σ : Signature.{u, v, w}}
    {atomMap : Array (Atom σ)} {lit : PropResolution.Lit}
    (hOutside : outsideAtomMap atomMap lit = true) :
    outsideAtomMap atomMap lit.neg = true := by
  cases lit
  simpa [outsideAtomMap, PropResolution.Lit.neg] using hOutside

end PropLiteralLink

/-- 无 guard 父对象字句命题化为 initial clause 的证据。 -/
structure PropParentClauseLink (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  literalLinks : Array (PropLiteralLink σ)

namespace PropParentClauseLink

/-- 由文字链接计算命题字句。 -/
def encodedClause {σ : Signature.{u, v, w}} (link : PropParentClauseLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause (link.literalLinks.map fun literal => literal.prop)

/-- 由文字链接恢复 HO 对象字句。 -/
def objectClause {σ : Signature.{u, v, w}} (link : PropParentClauseLink σ) :
    Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }

/-- 普通 parent initial 的局部检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (atomMap : Array (Atom σ))
    (initial : PropResolution.InitialClause) (link : PropParentClauseLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.literalLinks.all fun literal => literal.check atomMap

/-- 父 HO 字句的满足性传递到命题化字句。 -/
theorem encodedClause_satisfies_of_object
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropParentClauseLink σ}
    (hLiteralChecks :
      (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObject : link.objectClause.Satisfies env) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  rcases hObject with ⟨objectLiteral, hObjectMem, hObjectSat⟩
  have hMapped :
      objectLiteral ∈ (link.literalLinks.map fun literal => literal.object).toList := by
    simpa [objectClause] using Array.mem_def.mp hObjectMem
  have hMappedList :
      objectLiteral ∈
        List.map (fun literal => literal.object) link.literalLinks.toList := by
    simpa [Array.toList_map] using hMapped
  rcases List.mem_map.mp hMappedList with
    ⟨literalLink, hLinkMem, hObjectEq⟩
  have hCheck : literalLink.check atomMap = true := by
    have hArrayMem : literalLink ∈ link.literalLinks :=
      Array.mem_def.mpr hLinkMem
    rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
    simpa [hGet] using (Array.all_eq_true.mp hLiteralChecks) i hLt
  have hPropMem : literalLink.prop ∈ link.encodedClause.toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    have hRaw :
        literalLink.prop ∈
          List.map (fun literal => literal.prop) link.literalLinks.toList :=
      List.mem_map_of_mem hLinkMem
    simpa [Array.toList_map] using hRaw
  have hPropHolds :
      literalLink.prop.Holds (PropLiteralLink.valuation base atomMap env) :=
    PropLiteralLink.sound hCheck (by simpa [hObjectEq] using hObjectSat)
  exact PropResolution.Clause.satisfies_of_mem hPropMem hPropHolds

end PropParentClauseLink

/-- guarded HO 字句对应 activation initial `¬Γ ∨ prop(C)` 的证据。 -/
structure PropGuardActivationLink (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  guards : GuardSet
  literalLinks : Array (PropLiteralLink σ)

namespace PropGuardActivationLink

/-- 计算 activation clause `¬Γ ∨ prop(C)`。 -/
def encodedClause {σ : Signature.{u, v, w}} (link : PropGuardActivationLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause
    (link.guards.map PropResolution.Lit.neg ++
      link.literalLinks.map fun literal => literal.prop)

/-- 由文字链接恢复 HO 对象字句。 -/
def objectClause {σ : Signature.{u, v, w}} (link : PropGuardActivationLink σ) :
    Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }

/-- guarded activation initial 的局部检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (atomMap : Array (Atom σ))
    (initial : PropResolution.InitialClause)
    (link : PropGuardActivationLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.guards.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
          link.literalLinks.all fun literal => literal.check atomMap

/-- 若 guard 全真则对象字句成立；否则 activation 中某个负 guard 成立。 -/
theorem encodedClause_satisfies
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropGuardActivationLink σ}
    (hGuardChecks :
      (link.guards.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true)
    (hLiteralChecks :
      (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObjectOfGuards :
      (∀ lit, lit ∈ (canonicalGuards link.guards).toList → lit.Holds base) →
        link.objectClause.Satisfies env) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  classical
  by_cases hGuards :
      ∀ lit, lit ∈ (canonicalGuards link.guards).toList → lit.Holds base
  · rcases hObjectOfGuards hGuards with
      ⟨objectLiteral, hObjectMem, hObjectSat⟩
    have hMapped :
        objectLiteral ∈ (link.literalLinks.map fun literal => literal.object).toList := by
      simpa [objectClause] using Array.mem_def.mp hObjectMem
    have hMappedList :
        objectLiteral ∈
          List.map (fun literal => literal.object) link.literalLinks.toList := by
      simpa [Array.toList_map] using hMapped
    rcases List.mem_map.mp hMappedList with
      ⟨literalLink, hLinkMem, hObjectEq⟩
    have hCheck : literalLink.check atomMap = true := by
      have hArrayMem : literalLink ∈ link.literalLinks :=
        Array.mem_def.mpr hLinkMem
      rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
      simpa [hGet] using (Array.all_eq_true.mp hLiteralChecks) i hLt
    have hPropMem : literalLink.prop ∈ link.encodedClause.toList := by
      apply PropResolution.mem_canonicalClause_of_mem
      simp
      exact Or.inr ⟨literalLink, Array.mem_def.mpr hLinkMem, rfl⟩
    exact PropResolution.Clause.satisfies_of_mem hPropMem
      (PropLiteralLink.sound hCheck (by simpa [hObjectEq] using hObjectSat))
  · rcases Classical.not_forall.mp hGuards with ⟨guardLit, hNotGuard⟩
    have hGuardMem : guardLit ∈ (canonicalGuards link.guards).toList := by
      by_cases hMem : guardLit ∈ (canonicalGuards link.guards).toList
      · exact hMem
      · exact False.elim (hNotGuard (by intro h; exact False.elim (hMem h)))
    have hGuardFalse : ¬ guardLit.Holds base := by
      intro hHold
      exact hNotGuard (by intro _hMem; exact hHold)
    have hRawGuardMem : guardLit ∈ link.guards.toList :=
      mem_of_mem_propCanonicalClause hGuardMem
    have hOutside : PropLiteralLink.outsideAtomMap atomMap guardLit = true := by
      have hArrayMem : guardLit ∈ link.guards :=
        Array.mem_def.mpr hRawGuardMem
      rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
      simpa [hGet] using (Array.all_eq_true.mp hGuardChecks) i hLt
    have hNegBase : guardLit.neg.Holds base := by
      cases guardLit with
      | mk var positive =>
          cases positive <;>
            simpa [PropResolution.Lit.Holds, PropResolution.Lit.neg] using hGuardFalse
    have hNegMem : guardLit.neg ∈ link.encodedClause.toList := by
      apply PropResolution.mem_canonicalClause_of_mem
      simp
      exact Or.inl ⟨guardLit, Array.mem_def.mpr hRawGuardMem, rfl⟩
    exact PropResolution.Clause.satisfies_of_mem hNegMem
      ((PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
        (base := base) (env := env)
        (PropLiteralLink.outsideAtomMap_neg hOutside)).2 hNegBase)

end PropGuardActivationLink

/-- CDCL initial 引用一个已经物化的 learned-clause 节点。 -/
structure PropLearnedClauseLink where
  parent : Nat
  guards : GuardSet
  clause : PropResolution.Clause

namespace PropLearnedClauseLink

/-- learned-clause initial 的局部检查。 -/
def check {σ : Signature.{u, v, w}} (parents : Array Nat)
    (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause)
    (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    link.clause.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq link.clause (learnedClauseOfGuards link.guards) &&
        PropResolution.clauseEq initial.clause link.clause

/-- 当 conflict guards 不全真时，`¬Γ` 在混合 valuation 中成立。 -/
theorem satisfies_of_not_guards
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Atom σ)}
    {env : Logic.HigherOrder.Env M} {link : PropLearnedClauseLink}
    {guards : GuardSet} (hClause : link.clause = learnedClauseOfGuards guards)
    (hOutside :
      (link.clause.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true)
    (hNotGuards :
      ¬ ∀ lit, lit ∈ (canonicalGuards guards).toList → lit.Holds base) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.clause := by
  classical
  rcases Classical.not_forall.mp hNotGuards with ⟨guardLit, hNotGuard⟩
  have hGuardMem : guardLit ∈ (canonicalGuards guards).toList := by
    by_cases hMem : guardLit ∈ (canonicalGuards guards).toList
    · exact hMem
    · exact False.elim (hNotGuard (by intro h; exact False.elim (hMem h)))
  have hGuardFalse : ¬ guardLit.Holds base := by
    intro hHold
    exact hNotGuard (by intro _hMem; exact hHold)
  have hRawGuardMem : guardLit ∈ guards.toList :=
    mem_of_mem_propCanonicalClause hGuardMem
  have hNegMemLearned :
      guardLit.neg ∈ (learnedClauseOfGuards guards).toList := by
    have hMapMem :
        guardLit.neg ∈ (guards.map PropResolution.Lit.neg).toList := by
      simpa [Array.toList_map] using
        (List.mem_map_of_mem (f := PropResolution.Lit.neg) hRawGuardMem)
    simpa [learnedClauseOfGuards] using
      PropResolution.mem_canonicalClause_of_mem hMapMem
  have hNegMemClause : guardLit.neg ∈ link.clause.toList := by
    simpa [hClause] using hNegMemLearned
  have hNegOutside :
      PropLiteralLink.outsideAtomMap atomMap guardLit.neg = true := by
    have hArrayMem : guardLit.neg ∈ link.clause :=
      Array.mem_def.mpr hNegMemClause
    rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
    simpa [hGet] using (Array.all_eq_true.mp hOutside) i hLt
  have hNegBase : guardLit.neg.Holds base := by
    cases guardLit with
    | mk var positive =>
        cases positive <;>
          simpa [PropResolution.Lit.Holds, PropResolution.Lit.neg] using hGuardFalse
  exact PropResolution.Clause.satisfies_of_mem hNegMemClause
    ((PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (base := base) (env := env) hNegOutside).2 hNegBase)

end PropLearnedClauseLink

/-- CDCL initial clause 对应一个 HO AVATAR split descriptor 的 selector skeleton。 -/
structure PropAvatarSkeletonLink where
  parent : Nat
  skeleton : PropResolution.Clause

namespace PropAvatarSkeletonLink

/-- skeleton initial 的局部检查；split 与 skeleton 的整图对应由 DAG checker 复核。 -/
def check {σ : Signature.{u, v, w}} (parents : Array Nat)
    (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause)
    (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    link.skeleton.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.skeleton

end PropAvatarSkeletonLink

/-- residual CDCL initial 的四种可信来源。 -/
inductive PropInitialJustification (σ : Signature.{u, v, w}) where
  | parentClause (link : PropParentClauseLink σ)
  | guardActivationClause (link : PropGuardActivationLink σ)
  | propLearnedClause (link : PropLearnedClauseLink)
  | avatarSkeleton (link : PropAvatarSkeletonLink)

namespace PropInitialJustification

/-- initial justification 中引用的父字句快照。 -/
def parentClause? {σ : Signature.{u, v, w}} :
    PropInitialJustification σ → Option (ParentClause σ)
  | .parentClause link => some link.parent
  | .guardActivationClause link => some link.parent
  | .propLearnedClause _ | .avatarSkeleton _ => none

/-- initial justification 的局部检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (atomMap : Array (Atom σ))
    (initial : PropResolution.InitialClause) : PropInitialJustification σ → Bool
  | .parentClause link => link.check parents atomMap initial
  | .guardActivationClause link => link.check parents atomMap initial
  | .propLearnedClause link => link.check parents atomMap initial
  | .avatarSkeleton link => link.check parents atomMap initial

/-- 通用 guarded residual 暂不消费 HO selector skeleton。 -/
def guardedSoundnessSupported {σ : Signature.{u, v, w}} :
    PropInitialJustification σ → Bool
  | .parentClause _ | .guardActivationClause _ | .propLearnedClause _ => true
  | .avatarSkeleton _ => false

end PropInitialJustification

/-- residual CDCL 的 checked UNSAT payload 与对象来源链接。 -/
structure PropositionalClosurePayload (σ : Signature.{u, v, w}) where
  atomMap : Array (Atom σ) := #[]
  initialClauses : Array PropResolution.InitialClause
  initialJustifications : Array (PropInitialJustification σ)
  proof : PropResolution.CdclProof

namespace PropositionalClosurePayload

/-- residual CDCL 引用的父对象字句快照。 -/
def parentClauses {σ : Signature.{u, v, w}}
    (payload : PropositionalClosurePayload σ) : Array (ParentClause σ) :=
  payload.initialJustifications.filterMap PropInitialJustification.parentClause?

/-- 每个 initial 槽位必须有同位置 justification。 -/
def justificationsCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialClauses.size == payload.initialJustifications.size &&
    (payload.initialClauses.mapIdx fun index initial =>
      match payload.initialJustifications[index]? with
      | some justification => justification.check parents payload.atomMap initial
      | none => false).all fun ok => ok

/-- 通用 guarded residual 的 initial 来源支持检查。 -/
def guardedSoundnessSupported {σ : Signature.{u, v, w}}
    (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all PropInitialJustification.guardedSoundnessSupported

/-- residual CDCL payload 的可计算检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (payload : PropositionalClosurePayload σ) : Bool :=
  PropResolution.checkedUnsat payload.initialClauses payload.proof &&
    payload.justificationsCheck parents

/-- 从 checked UNSAT 证书组装 residual payload。 -/
def ofCheckedUnsat {σ : Signature.{u, v, w}}
    (cert : PropResolution.CheckedUnsatCertificate)
    (atomMap : Array (Atom σ))
    (initialJustifications : Array (PropInitialJustification σ)) :
    PropositionalClosurePayload σ := {
  atomMap := atomMap
  initialClauses := cert.initialClauses
  initialJustifications := initialJustifications
  proof := cert.proof
}

end PropositionalClosurePayload

/-- HO-AVATAR source split descriptor。 -/
structure AvatarSplitPayload (σ : Signature.{u, v, w}) where
  source : ParentClause σ
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause

namespace AvatarSplitPayload

/-- split descriptor 引用的 canonical source 快照。 -/
def parentClauses {σ : Signature.{u, v, w}} (payload : AvatarSplitPayload σ) :
    Array (ParentClause σ) :=
  #[payload.source]

/-- 从 partition 表机械复算全部 component clauses。 -/
def componentClauses {σ : Signature.{u, v, w}} (payload : AvatarSplitPayload σ) :
    List (Clause σ) :=
  payload.partitions.toList.map (Avatar.clauseAtIndices payload.source.clause)

/-- split descriptor 的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array Nat) (payload : AvatarSplitPayload σ) : Bool :=
  parents.size == 1 &&
    payload.source.idIn parents &&
      payload.source.clause.check &&
        Automation.AvatarSplit.indexPartitionOk payload.source.clause.literals.size
          payload.partitions &&
          Automation.AvatarSplit.selectorsOk payload.partitions payload.selectors &&
            Avatar.pairwiseSupportDisjoint payload.componentClauses &&
              Clause.coversCheck payload.source.clause payload.componentClauses

end AvatarSplitPayload

/-- HO-AVATAR component 节点。结论与 singleton guard 均由 split 槽位复核。 -/
structure AvatarComponentPayload (σ : Signature.{u, v, w}) where
  split : ParentClause σ
  componentIndex : Nat
  component : Clause σ
  selector : GuardLit

namespace AvatarComponentPayload

/-- component 节点引用的 split descriptor 快照。 -/
def parentClauses {σ : Signature.{u, v, w}}
    (payload : AvatarComponentPayload σ) : Array (ParentClause σ) :=
  #[payload.split]

/-- component payload 的局部可信边界。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (parents : Array Nat) (payload : AvatarComponentPayload σ) : Bool :=
  parents.size == 1 &&
    payload.split.idIn parents &&
      payload.component.check &&
        payload.selector.positive

end AvatarComponentPayload

/-- 全局 selector registry 中的一条 HO component 登记。 -/
structure AvatarSelectorComponent (σ : Signature.{u, v, w}) where
  selector : GuardLit
  component : Clause σ

namespace AvatarSelectorComponent

/-- 把等长 selector/component 列表按槽位稳定配对。 -/
def ofLists {σ : Signature.{u, v, w}} :
    List GuardLit → List (Clause σ) → List (AvatarSelectorComponent σ)
  | selector :: selectors, component :: components =>
      ⟨selector, component⟩ :: ofLists selectors components
  | _, _ => []

/-- 同一个 selector 变量必须在整图中始终表示同一个 HO component。 -/
def compatibleCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (entries : List (AvatarSelectorComponent σ)) : Bool :=
  entries.all fun left =>
    entries.all fun right =>
      if left.selector.var == right.selector.var then
        left.component.eq right.component
      else
        true

end AvatarSelectorComponent

namespace AvatarSplitPayload

/-- split descriptor 按槽位配对出的稳定 selector/component 登记表。 -/
def selectorComponents {σ : Signature.{u, v, w}}
    (payload : AvatarSplitPayload σ) : List (AvatarSelectorComponent σ) :=
  AvatarSelectorComponent.ofLists payload.selectors.toList payload.componentClauses

end AvatarSplitPayload

/-- 显式 theory conflict：某组 guard 下的对象空字句。 -/
structure TheoryConflictPayload (σ : Signature.{u, v, w}) where
  conflict : ParentClause σ

namespace TheoryConflictPayload

/-- theory conflict 引用的父快照。 -/
def parentClauses {σ : Signature.{u, v, w}} (payload : TheoryConflictPayload σ) :
    Array (ParentClause σ) :=
  #[payload.conflict]

/-- theory conflict 的局部检查。 -/
def check {σ : Signature.{u, v, w}} (parents : Array Nat)
    (payload : TheoryConflictPayload σ) : Bool :=
  payload.conflict.idIn parents && payload.conflict.clause.isEmpty

end TheoryConflictPayload

/-- theory conflict `Γ ⟹ ⊥` 产生的命题 learned clause `¬Γ`。 -/
structure PropositionalLearnedClausePayload where
  conflict : Nat
  learned : PropResolution.Clause

namespace PropositionalLearnedClausePayload

/-- learned 节点必须引用 conflict 父边。 -/
def check (parents : Array Nat) (payload : PropositionalLearnedClausePayload) : Bool :=
  parents.contains payload.conflict

end PropositionalLearnedClausePayload

/--
原生高阶整图 payload。

source、β、η 直接计算公理结论；substitution、standardize-apart 与局部高阶规则
从已检查父快照机械计算结论。
-/
inductive Payload (σ : Signature.{u, v, w}) where
  | source (initialIndex : Nat)
  | avatarSplit (payload : AvatarSplitPayload σ)
  | avatarComponent (payload : AvatarComponentPayload σ)
  | beta (payload : Beta.Payload σ)
  | eta (payload : Eta.Payload σ)
  | substitution (evidence : Substitution.Evidence σ)
  | standardizeApart (evidence : StandardizeApart.Evidence σ)
  | resolution (evidence : Resolution.Evidence σ)
  | factoring (evidence : Factoring.Evidence σ)
  | equalityResolution (evidence : EqualityResolution.Evidence σ)
  | booleanExtensionality (evidence : BooleanExtensionality.Evidence σ)
  | demodulation (evidence : Rewrite.Evidence σ)
  | positiveSuperposition (evidence : Rewrite.Evidence σ)
  | negativeSuperposition (evidence : Rewrite.Evidence σ)
  | extensionalParamodulation (evidence : Rewrite.Evidence σ)
  | argumentCongruence (evidence : ArgumentCongruence.Evidence σ)
  | functionExtensionality (evidence : FunctionExtensionality.Evidence σ)
  | theoryConflict (payload : TheoryConflictPayload σ)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : PropositionalClosurePayload σ)

namespace Payload

/-- 从问题与 payload 机械计算节点结论。 -/
def conclusion? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (problem : Problem σ) :
    Payload σ → Option (Clause σ)
  | .source initialIndex => problem.initialClauses[initialIndex]?
  | .avatarSplit payload => some payload.source.clause
  | .avatarComponent payload => some payload.component
  | .beta payload => some payload.conclusion
  | .eta payload => some payload.conclusion
  | .substitution evidence => some evidence.conclusion
  | .standardizeApart evidence => some evidence.conclusion
  | .resolution evidence => some evidence.conclusion
  | .factoring evidence => some evidence.conclusion
  | .equalityResolution evidence => some evidence.conclusion
  | .booleanExtensionality evidence => some evidence.conclusion
  | .demodulation evidence => some evidence.conclusion
  | .positiveSuperposition evidence => some evidence.conclusion
  | .negativeSuperposition evidence => some evidence.conclusion
  | .extensionalParamodulation evidence => some evidence.conclusion
  | .argumentCongruence evidence => some evidence.conclusion
  | .functionExtensionality evidence => some evidence.conclusion
  | .theoryConflict _ => some { literals := #[] }
  | .propositionalLearnedClause _ => some { literals := #[] }
  | .residualCdcl _ => some { literals := #[] }

/-- payload 中显式携带的父字句快照。 -/
def parentClauses {σ : Signature.{u, v, w}} : Payload σ → Array (ParentClause σ)
  | .substitution evidence => #[evidence.parent]
  | .avatarSplit payload => payload.parentClauses
  | .avatarComponent payload => payload.parentClauses
  | .standardizeApart evidence => #[evidence.parent]
  | .resolution evidence => #[evidence.left, evidence.right]
  | .factoring evidence => #[evidence.parent]
  | .equalityResolution evidence => #[evidence.parent]
  | .booleanExtensionality evidence => #[evidence.parent]
  | .demodulation evidence => #[evidence.equality, evidence.target]
  | .positiveSuperposition evidence => #[evidence.equality, evidence.target]
  | .negativeSuperposition evidence => #[evidence.equality, evidence.target]
  | .extensionalParamodulation evidence => #[evidence.equality, evidence.target]
  | .argumentCongruence evidence => #[evidence.parent]
  | .functionExtensionality evidence => #[evidence.parent]
  | .theoryConflict payload => payload.parentClauses
  | .residualCdcl payload => payload.parentClauses
  | _ => #[]

/-- 当前可进入无 guard 对象 soundness 的 payload。 -/
def soundnessSupported {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .avatarSplit _ => false
  | .avatarComponent _ => false
  | .theoryConflict _ => false
  | .propositionalLearnedClause _ => false
  | .residualCdcl _ => false
  | _ => true

/--
无需显式差异见证合同即可消费的无 guard payload。

`functionExtensionality` 的负等式规则依赖签名内显式 `diff` 符号；直接 HO 搜索主线
尚未生成这种资源，因此必须在可信边界上拒绝，而不是伪造 witness contract。
-/
def witnessFreeSoundnessSupported {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .avatarSplit _ => false
  | .avatarComponent _ => false
  | .functionExtensionality _ => false
  | .theoryConflict _ => false
  | .propositionalLearnedClause _ => false
  | .residualCdcl _ => false
  | _ => true

/-- 当前可进入 guarded soundness 的 payload。 -/
def guardedSoundnessSupported {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .avatarSplit _ => false
  | .avatarComponent _ => false
  | .residualCdcl payload => payload.guardedSoundnessSupported
  | _ => true

/--
payload checker。

source、β、η 是零父边公理节点；其余节点检查父边引用、规则专用 witness 与机械结果。
-/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : Problem σ) (parents : Array Nat) : Payload σ → Bool
  | .source initialIndex =>
      parents.isEmpty &&
        match problem.initialClauses[initialIndex]? with
        | some clause => clause.check
        | none => false
  | .avatarSplit payload => payload.check parents
  | .avatarComponent payload => payload.check parents
  | .beta payload => parents.isEmpty && payload.check
  | .eta payload => parents.isEmpty && payload.check
  | .substitution evidence => evidence.check parents
  | .standardizeApart evidence => evidence.check parents
  | .resolution evidence => evidence.check parents
  | .factoring evidence => evidence.check parents
  | .equalityResolution evidence => evidence.check parents
  | .booleanExtensionality evidence => evidence.check parents
  | .demodulation evidence => evidence.check .demodulation parents
  | .positiveSuperposition evidence => evidence.check .positiveSuperposition parents
  | .negativeSuperposition evidence => evidence.check .negativeSuperposition parents
  | .extensionalParamodulation evidence =>
      evidence.check .extensionalParamodulation parents
  | .argumentCongruence evidence => evidence.check parents
  | .functionExtensionality evidence => evidence.check parents
  | .theoryConflict payload => payload.check parents
  | .propositionalLearnedClause payload => payload.check parents
  | .residualCdcl payload => !parents.isEmpty && payload.check parents

/-- payload checker 成功时，每个父快照编号都出现在父边数组中。 -/
theorem parentIdsIn_of_check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : Problem σ} {parents : Array Nat} {payload : Payload σ}
    (hCheck : payload.check problem parents = true) :
    ∀ parent, parent ∈ payload.parentClauses.toList → parent.id ∈ parents.toList := by
  intro parent hParent
  cases payload with
  | source initialIndex =>
      simp [parentClauses] at hParent
  | avatarSplit payload =>
      have hEq : parent = payload.source := by
        simpa [Payload.parentClauses, AvatarSplitPayload.parentClauses] using hParent
      subst parent
      have hPayloadCheck : payload.check parents = true := by
        simpa [check] using hCheck
      simp only [AvatarSplitPayload.check, Bool.and_eq_true_iff] at hPayloadCheck
      rcases hPayloadCheck with
        ⟨⟨⟨⟨⟨⟨_hSize, hParent⟩, _hClause⟩, _hPartition⟩,
          _hSelectors⟩, _hDisjoint⟩, _hCovers⟩
      exact ParentClause.mem_toList_of_idIn hParent
  | avatarComponent payload =>
      have hEq : parent = payload.split := by
        simpa [Payload.parentClauses, AvatarComponentPayload.parentClauses] using hParent
      subst parent
      have hPayloadCheck : payload.check parents = true := by
        simpa [check] using hCheck
      exact ParentClause.mem_toList_of_idIn
        (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp
              (show
                ((parents.size == 1 && payload.split.idIn parents) &&
                  payload.component.check) &&
                  payload.selector.positive = true by
                simpa [AvatarComponentPayload.check] using hPayloadCheck)).1).1).2
  | beta betaPayload =>
      simp [parentClauses] at hParent
  | eta etaPayload =>
      simp [parentClauses] at hParent
  | substitution evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (Substitution.Evidence.parentIdIn_of_check hCheck)
  | standardizeApart evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (StandardizeApart.Evidence.parentIdIn_of_check hCheck)
  | resolution evidence =>
      have hEq : parent = evidence.left ∨ parent = evidence.right := by
        simpa [parentClauses] using hParent
      rcases hEq with hLeft | hRight
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Resolution.Evidence.leftIdIn_of_check hCheck)
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Resolution.Evidence.rightIdIn_of_check hCheck)
  | factoring evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (Factoring.Evidence.parentIdIn_of_check hCheck)
  | equalityResolution evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (EqualityResolution.Evidence.parentIdIn_of_check hCheck)
  | booleanExtensionality evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (BooleanExtensionality.Evidence.parentIdIn_of_check hCheck)
  | demodulation evidence =>
      have hEq : parent = evidence.equality ∨ parent = evidence.target := by
        simpa [parentClauses] using hParent
      rcases hEq with hEquality | hTarget
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.equalityIdIn_of_check hCheck)
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.targetIdIn_of_check hCheck)
  | positiveSuperposition evidence =>
      have hEq : parent = evidence.equality ∨ parent = evidence.target := by
        simpa [parentClauses] using hParent
      rcases hEq with hEquality | hTarget
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.equalityIdIn_of_check hCheck)
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.targetIdIn_of_check hCheck)
  | negativeSuperposition evidence =>
      have hEq : parent = evidence.equality ∨ parent = evidence.target := by
        simpa [parentClauses] using hParent
      rcases hEq with hEquality | hTarget
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.equalityIdIn_of_check hCheck)
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.targetIdIn_of_check hCheck)
  | extensionalParamodulation evidence =>
      have hEq : parent = evidence.equality ∨ parent = evidence.target := by
        simpa [parentClauses] using hParent
      rcases hEq with hEquality | hTarget
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.equalityIdIn_of_check hCheck)
      · subst parent
        exact ParentClause.mem_toList_of_idIn
          (Rewrite.Evidence.targetIdIn_of_check hCheck)
  | argumentCongruence evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (ArgumentCongruence.Evidence.parentIdIn_of_check hCheck)
  | functionExtensionality evidence =>
      have hEq : parent = evidence.parent := by
        simpa [parentClauses] using hParent
      subst parent
      exact ParentClause.mem_toList_of_idIn
        (FunctionExtensionality.Evidence.parentIdIn_of_check hCheck)
  | theoryConflict payload =>
      have hEq : parent = payload.conflict := by
        simpa [parentClauses, TheoryConflictPayload.parentClauses] using hParent
      subst parent
      have hParentIn : payload.conflict.idIn parents = true := by
        simpa [check, TheoryConflictPayload.check] using
          (Bool.and_eq_true_iff.mp hCheck).1
      exact ParentClause.mem_toList_of_idIn hParentIn
  | propositionalLearnedClause payload =>
      simp [parentClauses] at hParent
  | residualCdcl closure =>
      have hClosureCheck : closure.check parents = true := by
        exact (Bool.and_eq_true_iff.mp hCheck).2
      have hJustifications : closure.justificationsCheck parents = true :=
        (Bool.and_eq_true_iff.mp hClosureCheck).2
      simp only [parentClauses, PropositionalClosurePayload.parentClauses] at hParent
      simp only [Array.toList_filterMap] at hParent
      rcases List.mem_filterMap.mp hParent with
        ⟨justification, hJustificationMem, hParentClause⟩
      have hSize : closure.initialClauses.size = closure.initialJustifications.size := by
        unfold PropositionalClosurePayload.justificationsCheck at hJustifications
        exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hJustifications).1
      have hJustificationArray : justification ∈ closure.initialJustifications :=
        Array.mem_def.mpr hJustificationMem
      rcases Array.mem_iff_getElem.mp hJustificationArray with ⟨slot, hSlot, hGet⟩
      have hInitialSlot : slot < closure.initialClauses.size := by
        simpa [hSize] using hSlot
      have hAll :=
        (Bool.and_eq_true_iff.mp hJustifications).2
      have hAt :=
        (Array.all_eq_true.mp hAll) slot (by
          simpa [Array.size_mapIdx] using hInitialSlot)
      have hJustGet :
          closure.initialJustifications[slot]? =
            some closure.initialJustifications[slot] :=
        Array.getElem?_eq_some_iff.mpr ⟨hSlot, rfl⟩
      simp [Array.getElem_mapIdx, hJustGet] at hAt
      rw [hGet] at hAt
      cases justification with
      | parentClause link =>
          simp [PropInitialJustification.parentClause?] at hParentClause
          cases hParentClause
          exact ParentClause.mem_toList_of_idIn
            (Bool.and_eq_true_iff.mp
              (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp hAt).1).1).1
      | guardActivationClause link =>
          simp [PropInitialJustification.parentClause?] at hParentClause
          cases hParentClause
          exact ParentClause.mem_toList_of_idIn
            (Bool.and_eq_true_iff.mp
              (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp
                  (Bool.and_eq_true_iff.mp hAt).1).1).1).1
      | propLearnedClause link =>
          simp [PropInitialJustification.parentClause?] at hParentClause
      | avatarSkeleton link =>
          simp [PropInitialJustification.parentClause?] at hParentClause

/-- 当前支持 payload 的结论在相应高阶模型中成立。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    {problem : Problem σ} (hProblem : problem.Valid M)
    (payload : Payload σ) (parents : Array Nat)
    (hSupported : payload.soundnessSupported = true)
    (hCheck : payload.check problem parents = true)
    (hParents :
      ∀ parent, parent ∈ payload.parentClauses.toList → parent.clause.Valid M) :
    ∃ conclusion,
      payload.conclusion? problem = some conclusion ∧ conclusion.Valid M := by
  cases payload with
  | source initialIndex =>
      cases hConclusion : problem.initialClauses[initialIndex]? with
      | none =>
          simp [check, hConclusion] at hCheck
      | some conclusion =>
          exact ⟨conclusion, by simp [conclusion?, hConclusion],
            fun env hEnv => hProblem env hEnv initialIndex conclusion hConclusion⟩
  | avatarSplit payload =>
      simp [soundnessSupported] at hSupported
  | avatarComponent payload =>
      simp [soundnessSupported] at hSupported
  | beta payload =>
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hCheck).2
      exact ⟨payload.conclusion, by simp [conclusion?],
        fun env hEnv => Beta.Payload.sound contract payload env hEnv hPayloadCheck⟩
  | eta payload =>
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hCheck).2
      exact ⟨payload.conclusion, by simp [conclusion?],
        fun env hEnv => Eta.Payload.sound contract payload env hEnv hPayloadCheck⟩
  | substitution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | standardizeApart evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound (hParents evidence.parent (by simp [parentClauses]))⟩
  | resolution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound
          (hParents evidence.left (by simp [parentClauses]))
          (hParents evidence.right (by simp [parentClauses]))⟩
  | factoring evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | equalityResolution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | booleanExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound contract hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | demodulation evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | positiveSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | negativeSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | extensionalParamodulation evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | argumentCongruence evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound
            (hParents evidence.parent (by simp [parentClauses]) env hEnv)⟩
  | functionExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound witnessContract hEnv hCheck
            (hParents evidence.parent (by simp [parentClauses]) env hEnv)⟩
  | theoryConflict payload =>
      simp [soundnessSupported] at hSupported
  | propositionalLearnedClause payload =>
      simp [soundnessSupported] at hSupported
  | residualCdcl payload =>
      simp [soundnessSupported] at hSupported

/-- 无显式差异见证合同的受支持 payload soundness。 -/
theorem soundWitnessFree {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    {problem : Problem σ} (hProblem : problem.Valid M)
    (payload : Payload σ) (parents : Array Nat)
    (hSupported : payload.witnessFreeSoundnessSupported = true)
    (hCheck : payload.check problem parents = true)
    (hParents :
      ∀ parent, parent ∈ payload.parentClauses.toList → parent.clause.Valid M) :
    ∃ conclusion,
      payload.conclusion? problem = some conclusion ∧ conclusion.Valid M := by
  cases payload with
  | source initialIndex =>
      cases hConclusion : problem.initialClauses[initialIndex]? with
      | none =>
          simp [check, hConclusion] at hCheck
      | some conclusion =>
          exact ⟨conclusion, by simp [conclusion?, hConclusion],
            fun env hEnv => hProblem env hEnv initialIndex conclusion hConclusion⟩
  | avatarSplit payload =>
      simp [witnessFreeSoundnessSupported] at hSupported
  | avatarComponent payload =>
      simp [witnessFreeSoundnessSupported] at hSupported
  | beta payload =>
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hCheck).2
      exact ⟨payload.conclusion, by simp [conclusion?],
        fun env hEnv => Beta.Payload.sound contract payload env hEnv hPayloadCheck⟩
  | eta payload =>
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hCheck).2
      exact ⟨payload.conclusion, by simp [conclusion?],
        fun env hEnv => Eta.Payload.sound contract payload env hEnv hPayloadCheck⟩
  | substitution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | standardizeApart evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound (hParents evidence.parent (by simp [parentClauses]))⟩
  | resolution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound
          (hParents evidence.left (by simp [parentClauses]))
          (hParents evidence.right (by simp [parentClauses]))⟩
  | factoring evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | equalityResolution evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | booleanExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        evidence.sound contract hCheck
          (hParents evidence.parent (by simp [parentClauses]))⟩
  | demodulation evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | positiveSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | negativeSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | extensionalParamodulation evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound contract hCheck
            (hParents evidence.equality (by simp [parentClauses]) env hEnv)
            (hParents evidence.target (by simp [parentClauses]) env hEnv)⟩
  | argumentCongruence evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?],
        fun env hEnv =>
          evidence.sound
            (hParents evidence.parent (by simp [parentClauses]) env hEnv)⟩
  | functionExtensionality evidence =>
      simp [witnessFreeSoundnessSupported] at hSupported
  | theoryConflict payload =>
      simp [witnessFreeSoundnessSupported] at hSupported
  | propositionalLearnedClause payload =>
      simp [witnessFreeSoundnessSupported] at hSupported
  | residualCdcl payload =>
      simp [witnessFreeSoundnessSupported] at hSupported

/-- payload checker 通过时，机械结论一定存在。 -/
theorem conclusion_exists_of_check
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : Problem σ} {parents : Array Nat} {payload : Payload σ}
    (hCheck : payload.check problem parents = true) :
    ∃ conclusion, payload.conclusion? problem = some conclusion := by
  cases payload with
  | source initialIndex =>
      cases hConclusion : problem.initialClauses[initialIndex]? with
      | none =>
          simp [check, hConclusion] at hCheck
      | some conclusion =>
          exact ⟨conclusion, by simp [conclusion?, hConclusion]⟩
  | avatarSplit payload =>
      exact ⟨payload.source.clause, by simp [conclusion?]⟩
  | avatarComponent payload =>
      exact ⟨payload.component, by simp [conclusion?]⟩
  | beta payload => exact ⟨payload.conclusion, by simp [conclusion?]⟩
  | eta payload => exact ⟨payload.conclusion, by simp [conclusion?]⟩
  | substitution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | standardizeApart evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | resolution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | factoring evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | equalityResolution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | booleanExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | demodulation evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | positiveSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | negativeSuperposition evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | extensionalParamodulation evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | argumentCongruence evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | functionExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | theoryConflict payload => exact ⟨{ literals := #[] }, by simp [conclusion?]⟩
  | propositionalLearnedClause payload =>
      exact ⟨{ literals := #[] }, by simp [conclusion?]⟩
  | residualCdcl payload => exact ⟨{ literals := #[] }, by simp [conclusion?]⟩

end Payload

/-- 原生高阶 DAG 节点；结论不作为不可信快照存储。 -/
structure Node (σ : Signature.{u, v, w}) where
  id : Nat
  parents : Array Nat
  guards : GuardSet := #[]
  payload : Payload σ

namespace Node

/-- 机械计算节点结论。 -/
def conclusion? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (problem : Problem σ)
    (node : Node σ) : Option (Clause σ) :=
  node.payload.conclusion? problem

/-- 当前节点的 guarded conclusion。 -/
def guardedConclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : Problem σ) (node : Node σ) : Option (GuardedClause σ) := do
  let conclusion ← node.conclusion? problem
  some { guards := node.guards, clause := conclusion }

/-- 当前节点是否没有 guard。 -/
def unguarded {σ : Signature.{u, v, w}} (node : Node σ) : Bool :=
  node.guards.isEmpty

/-- 当前节点是否是全局空根。 -/
def globallyClosed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : Problem σ) (node : Node σ) : Bool :=
  match node.conclusion? problem with
  | some conclusion => node.unguarded && conclusion.isEmpty
  | none => false

/-- 当前节点是否是 AVATAR theory conflict。 -/
def theoryConflict {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : Problem σ) (node : Node σ) : Bool :=
  match node.conclusion? problem with
  | some conclusion => !node.unguarded && conclusion.isEmpty
  | none => false

/-- 节点局部 checker。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : Problem σ) (node : Node σ) : Bool :=
  node.payload.check problem node.parents

/-- 当前节点是否落在无 guard soundness 支持片段。 -/
def soundnessSupported {σ : Signature.{u, v, w}} (node : Node σ) : Bool :=
  node.unguarded && node.payload.soundnessSupported

/-- 当前节点是否落在无需显式差异见证合同的无 guard 支持片段。 -/
def witnessFreeSoundnessSupported {σ : Signature.{u, v, w}} (node : Node σ) : Bool :=
  node.unguarded && node.payload.witnessFreeSoundnessSupported

/-- 当前节点是否落在 guarded soundness 支持片段。 -/
def guardedSoundnessSupported {σ : Signature.{u, v, w}} (node : Node σ) : Bool :=
  node.payload.guardedSoundnessSupported

/-- 节点语义不变量：机械结论存在并在任意类型正确环境下成立。 -/
def Invariant {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ}
    (problem : Problem σ) (node : Node σ) : Prop :=
  ∃ conclusion, node.conclusion? problem = some conclusion ∧ conclusion.Valid M

/-- guard 集在命题 valuation 下全部成立。 -/
def GuardsHold (valuation : PropResolution.Valuation) (guards : GuardSet) : Prop :=
  ∀ lit, lit ∈ (canonicalGuards guards).toList → lit.Holds valuation

/-- guard 集结构相等保持满足性。 -/
theorem GuardsHold.of_guardSetEq {valuation : PropResolution.Valuation}
    {left right : GuardSet} (hEq : guardSetEq left right = true)
    (hGuards : GuardsHold valuation left) :
    GuardsHold valuation right := by
  intro lit hLit
  have hCanonical : canonicalGuards left = canonicalGuards right :=
    PropResolution.clauseEq_eq.mp (by simpa [guardSetEq] using hEq)
  exact hGuards lit (by simpa [hCanonical] using hLit)

/-- 空 guard 集总是成立。 -/
theorem GuardsHold.empty (valuation : PropResolution.Valuation) :
    GuardsHold valuation (#[] : GuardSet) := by
  intro lit hLit
  have hRaw : lit ∈ (#[] : GuardSet).toList :=
    mem_of_mem_propCanonicalClause hLit
  simp at hRaw

/-- `isEmpty` 检查通过的 guard 集总是成立。 -/
theorem GuardsHold.of_isEmpty {valuation : PropResolution.Valuation}
    {guards : GuardSet} (hEmpty : guards.isEmpty = true) :
    GuardsHold valuation guards := by
  have hGuards : guards = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    have hBool : (guards.size == 0) = true := by
      simpa [Array.isEmpty] using hEmpty
    exact beq_iff_eq.mp hBool
  subst guards
  exact GuardsHold.empty valuation

/-- guarded 节点不变量：当前 guards 全真时机械结论成立。 -/
def GuardedInvariant {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (valuation : PropResolution.Valuation)
    (problem : Problem σ) (node : Node σ) : Prop :=
  ∃ conclusion, node.conclusion? problem = some conclusion ∧
    ∀ env : Logic.HigherOrder.Env M, env.WellSorted [] →
      GuardsHold valuation node.guards → conclusion.Satisfies env

end Node

/-- 原生高阶整图证书。 -/
structure DAG (σ : Signature.{u, v, w}) where
  problem : Problem σ
  root : Nat
  nodes : Array (Node σ)

namespace DAG

/-- 通过 dense id 读取节点。 -/
def node? {σ : Signature.{u, v, w}} (dag : DAG σ) (id : Nat) : Option (Node σ) :=
  dag.nodes[id]?

/-- 带边界证明读取节点。 -/
def nodeAt {σ : Signature.{u, v, w}} (dag : DAG σ) (index : Nat)
    (hIndex : index < dag.nodes.size) : Node σ :=
  dag.nodes[index]'hIndex

@[simp]
theorem node?_eq_some_nodeAt {σ : Signature.{u, v, w}} (dag : DAG σ) {index : Nat}
    (hIndex : index < dag.nodes.size) :
    dag.node? index = some (dag.nodeAt index hIndex) := by
  simp [node?, nodeAt]

/-- 单个父字句快照是否与整图中的真实父节点机械结论一致。 -/
def parentSnapshotChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (parent : ParentClause σ) : Bool :=
  match dag.node? parent.id with
  | some node =>
      match node.conclusion? dag.problem with
      | some conclusion => parent.clause.eq conclusion
      | none => false
  | none => false

/-- 父字句快照检查成功时，可取出真实父节点及其机械结论。 -/
theorem parentSnapshotChecked_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {parent : ParentClause σ}
    (hChecked : dag.parentSnapshotChecked parent = true) :
    ∃ node conclusion,
      dag.node? parent.id = some node ∧
        node.conclusion? dag.problem = some conclusion ∧
          parent.clause = conclusion := by
  unfold parentSnapshotChecked at hChecked
  cases hNode : dag.node? parent.id with
  | none =>
      simp [hNode] at hChecked
  | some node =>
      cases hConclusion : node.conclusion? dag.problem with
      | none =>
          simp [hNode, hConclusion] at hChecked
      | some conclusion =>
          have hClause : parent.clause.eq conclusion = true := by
            simpa [hNode, hConclusion] using hChecked
          exact ⟨node, conclusion, rfl, hConclusion,
            Clause.eq_sound parent.clause conclusion hClause⟩

/-- 所有 payload 父字句快照都必须与整图中的真实父节点一致。 -/
def parentSnapshotsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all fun node =>
    node.payload.parentClauses.all fun parent => dag.parentSnapshotChecked parent

/-- 整图父快照 checker 成功时，可取出任一节点 payload 中父快照的检查结果。 -/
theorem parentSnapshotChecked_of_eq_true {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hSnapshots : dag.parentSnapshotsChecked = true)
    (index : Nat) (hIndex : index < dag.nodes.size)
    (parent : ParentClause σ)
    (hParent : parent ∈ (dag.nodeAt index hIndex).payload.parentClauses.toList) :
    dag.parentSnapshotChecked parent = true := by
  have hNodes := Array.all_eq_true.mp hSnapshots
  have hNode :
      ((dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        dag.parentSnapshotChecked parent) = true := by
    simpa [parentSnapshotsChecked, nodeAt] using hNodes index hIndex
  have hParents := Array.all_eq_true.mp hNode
  have hArray : parent ∈ (dag.nodeAt index hIndex).payload.parentClauses :=
    Array.mem_def.mpr hParent
  rcases Array.mem_iff_getElem.mp hArray with ⟨parentIndex, hParentIndex, hGet⟩
  have hAt := hParents parentIndex hParentIndex
  simpa [hGet] using hAt

/-- 读取父节点 guard 集。 -/
def parentGuards? {σ : Signature.{u, v, w}} (dag : DAG σ)
    (id : Nat) : Option GuardSet :=
  (dag.node? id).map Node.guards

/-- list 版父节点 guard 规范并集。 -/
def parentGuardUnionList? {σ : Signature.{u, v, w}} (dag : DAG σ) :
    List Nat → Option GuardSet
  | [] => some #[]
  | parent :: rest => do
      let parentGuards ← dag.parentGuards? parent
      let restGuards ← dag.parentGuardUnionList? rest
      some (mergeGuards parentGuards restGuards)

/-- 计算全部父节点 guard 的规范并集。 -/
def parentGuardUnion? {σ : Signature.{u, v, w}} (dag : DAG σ)
    (parents : Array Nat) : Option GuardSet :=
  dag.parentGuardUnionList? parents.toList

/-- 左侧 guard 在并集规范化后仍然出现。 -/
theorem mem_canonical_mergeGuards_left {left right : GuardSet} {lit : GuardLit}
    (hMem : lit ∈ (canonicalGuards left).toList) :
    lit ∈ (canonicalGuards (mergeGuards left right)).toList := by
  have hRaw : lit ∈ left.toList :=
    mem_of_mem_propCanonicalClause hMem
  have hAppend : lit ∈ (left ++ right).toList := by
    simp [hRaw]
  have hMerged : lit ∈ (mergeGuards left right).toList := by
    simpa [mergeGuards, canonicalGuards] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged

/-- 右侧 guard 在并集规范化后仍然出现。 -/
theorem mem_canonical_mergeGuards_right {left right : GuardSet} {lit : GuardLit}
    (hMem : lit ∈ (canonicalGuards right).toList) :
    lit ∈ (canonicalGuards (mergeGuards left right)).toList := by
  have hRaw : lit ∈ right.toList :=
    mem_of_mem_propCanonicalClause hMem
  have hAppend : lit ∈ (left ++ right).toList := by
    simp [hRaw]
  have hMerged : lit ∈ (mergeGuards left right).toList := by
    simpa [mergeGuards, canonicalGuards] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged

/-- 父节点的 guard 会进入父 guard 并集。 -/
theorem mem_parentGuardUnionList_of_parent_mem
    {σ : Signature.{u, v, w}} {dag : DAG σ}
    {parents : List Nat} {parent : Nat} {parentNode : Node σ}
    {guards : GuardSet} {lit : GuardLit}
    (hUnion : dag.parentGuardUnionList? parents = some guards)
    (hParentMem : parent ∈ parents)
    (hParentNode : dag.node? parent = some parentNode)
    (hLit : lit ∈ (canonicalGuards parentNode.guards).toList) :
    lit ∈ (canonicalGuards guards).toList := by
  induction parents generalizing guards with
  | nil =>
      cases hParentMem
  | cons head rest ih =>
      simp [parentGuardUnionList?] at hUnion
      cases hHeadNode : dag.parentGuards? head with
      | none =>
          simp [hHeadNode] at hUnion
      | some headGuards =>
          cases hRestUnion : dag.parentGuardUnionList? rest with
          | none =>
              simp [hHeadNode, hRestUnion] at hUnion
          | some restGuards =>
              have hGuardsEq : guards = mergeGuards headGuards restGuards := by
                simpa [hHeadNode, hRestUnion] using hUnion.symm
              rcases List.mem_cons.mp hParentMem with hHead | hRest
              · subst hHead
                have hHeadGuards : headGuards = parentNode.guards := by
                  unfold parentGuards? at hHeadNode
                  rw [hParentNode] at hHeadNode
                  cases hHeadNode
                  rfl
                subst guards
                simpa [hHeadGuards] using
                  mem_canonical_mergeGuards_left
                    (left := parentNode.guards) (right := restGuards) hLit
              · subst guards
                exact mem_canonical_mergeGuards_right
                  (left := headGuards) (right := restGuards)
                  (ih hRestUnion hRest)

/-- 普通 parent initial 只能引用无 guard 的真实父节点。 -/
def propParentInitialLinkOk {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (parents : Array Nat)
    (link : PropParentClauseLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
      match dag.node? link.parent.id with
      | some parentNode => parentNode.unguarded
      | none => false

/-- activation initial 必须引用真实父节点及其 guard。 -/
def propGuardActivationInitialLinkOk {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (parents : Array Nat)
    (link : PropGuardActivationLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
      match dag.node? link.parent.id with
      | some parentNode =>
          !parentNode.unguarded && guardSetEq link.guards parentNode.guards
      | none => false

/-- learned initial 必须引用真实 learned 节点。 -/
def propLearnedInitialLinkOk {σ : Signature.{u, v, w}} (dag : DAG σ)
    (parents : Array Nat) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        match parentNode.payload with
        | .propositionalLearnedClause payload =>
            guardSetEq link.guards parentNode.guards &&
              PropResolution.clauseEq link.clause payload.learned
        | _ => false
    | none => false

/-- AVATAR skeleton initial 必须精确引用真实 split descriptor 的 selector skeleton。 -/
def propAvatarSkeletonInitialLinkOk {σ : Signature.{u, v, w}}
    (dag : DAG σ) (parents : Array Nat) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        parentNode.unguarded &&
          match parentNode.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq link.skeleton
                (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false

/-- initial justification 中依赖整图信息的检查。 -/
def propInitialJustificationDagOk {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (parents : Array Nat) :
    PropInitialJustification σ → Bool
  | .parentClause link => dag.propParentInitialLinkOk parents link
  | .guardActivationClause link => dag.propGuardActivationInitialLinkOk parents link
  | .propLearnedClause link => dag.propLearnedInitialLinkOk parents link
  | .avatarSkeleton link => dag.propAvatarSkeletonInitialLinkOk parents link

/-- residual CDCL 节点的所有 initial 链接都必须经过整图复核。 -/
def propInitialLinksOk {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .residualCdcl payload =>
      payload.initialJustifications.all fun justification =>
        dag.propInitialJustificationDagOk node.parents justification
  | _ => true

/-- split payload 对 HO selector registry 的局部贡献。 -/
def avatarSelectorComponents {σ : Signature.{u, v, w}} :
    Payload σ → List (AvatarSelectorComponent σ)
  | .avatarSplit payload =>
      payload.selectorComponents
  | _ => []

/-- 按 DAG 节点顺序收集全部 HO selector/component 登记。 -/
def avatarSelectorRegistry {σ : Signature.{u, v, w}} (dag : DAG σ) :
    List (AvatarSelectorComponent σ) :=
  dag.nodes.toList.flatMap fun node => avatarSelectorComponents node.payload

/-- 整图 HO selector registry 的可计算一致性检查。 -/
def avatarSelectorRegistryChecked {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  AvatarSelectorComponent.compatibleCheck dag.avatarSelectorRegistry

/-- 判断 payload 是否属于普通 guard-union 本地步骤。 -/
def payloadMergesParentGuards {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .substitution _ | .standardizeApart _ | .resolution _ | .factoring _
  | .equalityResolution _ | .booleanExtensionality _ | .demodulation _
  | .positiveSuperposition _ | .negativeSuperposition _
  | .extensionalParamodulation _ | .argumentCongruence _
  | .functionExtensionality _ | .theoryConflict _ => true
  | _ => false

/-- payload 是否是显式 theory-conflict artifact。 -/
def payloadIsTheoryConflict {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .theoryConflict _ => true
  | _ => false

/-- split descriptor 必须直接引用真实、无 guard 的 canonical source 节点。 -/
def avatarSplitNodeOk {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) (payload : AvatarSplitPayload σ) : Bool :=
  node.unguarded &&
    dag.parentSnapshotChecked payload.source &&
      match dag.node? payload.source.id with
      | some sourceNode =>
          sourceNode.unguarded &&
            match sourceNode.payload with
            | .source _ => true
            | _ => false
      | none => false

/-- component 必须由父 split descriptor 的 partition 与 selector 槽位机械复算。 -/
def avatarComponentNodeOk {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) (node : Node σ)
    (payload : AvatarComponentPayload σ) : Bool :=
  dag.parentSnapshotChecked payload.split &&
    match dag.node? payload.split.id with
    | some splitNode =>
        splitNode.unguarded &&
          match splitNode.payload with
          | .avatarSplit splitPayload =>
              match splitPayload.partitions[payload.componentIndex]?,
                  Automation.AvatarSplit.selectorAt? splitPayload.selectors
                    payload.componentIndex with
              | some indices, some selector =>
                  payload.component.eq
                      (Avatar.clauseAtIndices splitPayload.source.clause indices) &&
                    payload.selector == selector &&
                      guardSetEq node.guards #[selector]
              | _, _ => false
          | _ => false
    | none => false

/-- 单个节点的 DAG 级 guard 检查。 -/
def localNodeGuardsOk {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) : Bool :=
  if payloadMergesParentGuards node.payload then
    match dag.parentGuardUnion? node.parents with
    | some guards => guardSetEq node.guards guards
    | none => false
  else
    match node.payload with
    | .avatarSplit payload =>
        dag.avatarSplitNodeOk node payload
    | .avatarComponent payload =>
        dag.avatarComponentNodeOk node payload
    | .propositionalLearnedClause payload =>
        match dag.node? payload.conflict with
        | some conflictNode =>
            payloadIsTheoryConflict conflictNode.payload &&
              conflictNode.theoryConflict dag.problem &&
                guardSetEq node.guards conflictNode.guards &&
                  PropResolution.clauseEq payload.learned
                    (learnedClauseOfGuards conflictNode.guards)
        | none => false
    | .residualCdcl _ => node.unguarded
    | _ => true

/-- 整图的 guard 合并与 CDCL 来源检查。 -/
def guardsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all fun node =>
    dag.localNodeGuardsOk node && dag.propInitialLinksOk node

/-- `guardsChecked` 解包到单节点 guard 检查。 -/
theorem guardsChecked_of_eq_true {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAt := (Array.all_eq_true.mp hGuards) index hIndex
  exact (Bool.and_eq_true_iff.mp (by
    simpa [guardsChecked, nodeAt] using hAt)).1

/-- `guardsChecked` 解包到单节点 residual initial 链接检查。 -/
theorem propInitialLinksChecked_of_eq_true {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAt := (Array.all_eq_true.mp hGuards) index hIndex
  exact (Bool.and_eq_true_iff.mp (by
    simpa [guardsChecked, nodeAt] using hAt)).2

/-- 根节点是否存在。 -/
def rootExists {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  dag.root < dag.nodes.size

/-- 根节点是否机械计算为空字句。 -/
def rootClosed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  match dag.node? dag.root with
  | some node => node.globallyClosed dag.problem
  | none => false

/-- 节点编号是否与数组位置一致。 -/
def denseIds {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  (dag.nodes.mapIdx fun index node => node.id == index).all fun ok => ok

private theorem nat_eq_of_beq_eq_true {left right : Nat} (h : (left == right) = true) :
    left = right := by
  by_cases hEq : left = right
  · exact hEq
  · have hFalse : (left == right) = false := by
      simp [hEq]
    simp [hFalse] at h

/-- dense-id checker 为真时，每个节点的 id 等于数组位置。 -/
theorem denseIds_of_eq_true {σ : Signature.{u, v, w}} {dag : DAG σ}
    (hDense : dag.denseIds = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).id = index := by
  intro index hIndex
  let checks := dag.nodes.mapIdx fun index node => node.id == index
  have hAll : ∀ index (hIndex : index < checks.size), checks[index] = true := by
    simpa [denseIds, checks] using (Array.all_eq_true.mp hDense)
  have hMapIndex : index < checks.size := by
    simpa [checks, Array.size_mapIdx] using hIndex
  have hCheck := hAll index hMapIndex
  have hGet : checks[index] = ((dag.nodeAt index hIndex).id == index) := by
    simp [checks, nodeAt, Array.getElem_mapIdx]
  rw [hGet] at hCheck
  exact nat_eq_of_beq_eq_true hCheck

private def parentsAllBefore (bound : Nat) : List Nat → Bool
  | [] => true
  | parent :: rest => decide (parent < bound) && parentsAllBefore bound rest

private theorem parentsAllBefore_sound {bound : Nat} {parents : List Nat}
    (hParents : parentsAllBefore bound parents = true) :
    ∀ parent, parent ∈ parents → parent < bound := by
  induction parents with
  | nil =>
      intro parent hMem
      cases hMem
  | cons head tail ih =>
      simp [parentsAllBefore] at hParents
      intro parent hMem
      simp at hMem
      rcases hMem with rfl | hTail
      · exact hParents.1
      · exact ih hParents.2 parent hTail

private def parentsBeforeLoop {σ : Signature.{u, v, w}}
    (dag : DAG σ) (index remaining : Nat) : Bool :=
  match remaining with
  | 0 => true
  | remaining + 1 =>
      match dag.node? index with
      | some node =>
          parentsAllBefore index node.parents.toList &&
            parentsBeforeLoop dag (index + 1) remaining
      | none => false

private theorem parentsBeforeLoop_sound {σ : Signature.{u, v, w}} {dag : DAG σ}
    {start remaining : Nat} (hLoop : parentsBeforeLoop dag start remaining = true) :
    ∀ index node, start ≤ index → index < start + remaining →
      dag.node? index = some node →
        ∀ parent, parent ∈ node.parents.toList → parent < index := by
  induction remaining generalizing start with
  | zero =>
      intro index node hStart hLt hNode parent hParent
      have hLtStart : index < start := by
        simpa using hLt
      exact False.elim ((Nat.not_lt_of_ge hStart) hLtStart)
  | succ remaining ih =>
      intro index node hStart hLt hNode parent hParent
      cases hCurrent : dag.node? start with
      | none =>
          simp [parentsBeforeLoop, hCurrent] at hLoop
      | some currentNode =>
          simp [parentsBeforeLoop, hCurrent] at hLoop
          rcases hLoop with ⟨hCurrentParents, hRest⟩
          rcases Nat.eq_or_lt_of_le hStart with hEq | hAfter
          · subst hEq
            rw [hCurrent] at hNode
            cases hNode
            exact parentsAllBefore_sound hCurrentParents parent hParent
          · exact ih hRest index node (Nat.succ_le_of_lt hAfter)
              (by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLt)
              hNode parent hParent

/-- 每条父边是否指向更早的 dense 节点。 -/
def parentsBefore {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  parentsBeforeLoop dag 0 dag.nodes.size

/-- Prop 版父边拓扑条件。 -/
def ParentsBefore {σ : Signature.{u, v, w}} (dag : DAG σ) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    ∀ parent, parent ∈ (dag.nodeAt index hIndex).parents.toList → parent < index

/-- 可计算父边 checker 推出 Prop 版拓扑条件。 -/
theorem parentsBefore_of_eq_true {σ : Signature.{u, v, w}} {dag : DAG σ}
    (hParents : dag.parentsBefore = true) : dag.ParentsBefore :=
  fun index hIndex parent hParent =>
    parentsBeforeLoop_sound (dag := dag) (start := 0)
    (remaining := dag.nodes.size) hParents index (dag.nodeAt index hIndex)
    (Nat.zero_le index) (by simpa using hIndex)
    (dag.node?_eq_some_nodeAt hIndex) parent hParent

/-- 所有节点 payload 是否通过局部检查。 -/
def payloadsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.check dag.problem

/-- payload checker 为真时，每个节点的局部检查都为真。 -/
theorem payloadsChecked_of_eq_true {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hPayloads : dag.payloadsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).check dag.problem = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hPayloads
  simpa [payloadsChecked, nodeAt] using hAll index hIndex

/-- 整图是否只包含无 guard soundness 已支持节点。 -/
def soundnessSupported {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  dag.nodes.all Node.soundnessSupported

/-- 整图是否只包含无需显式差异见证合同的无 guard 节点。 -/
def witnessFreeSoundnessSupported {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  dag.nodes.all Node.witnessFreeSoundnessSupported

/-- 整图是否只包含 guarded soundness 已支持节点。 -/
def guardedSoundnessSupported {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  dag.nodes.all Node.guardedSoundnessSupported

/-- 原生高阶 DAG 的组合 checker。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) : Bool :=
  dag.rootExists && dag.rootClosed && dag.denseIds && dag.parentsBefore &&
    dag.payloadsChecked && dag.parentSnapshotsChecked && dag.guardsChecked

/--
拓扑归纳骨架。

节点性质只依赖父节点性质时，`ParentsBefore` 允许按 dense 数组顺序推广到整张图。
-/
theorem topologicalInduction {σ : Signature.{u, v, w}}
    (dag : DAG σ) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < dag.nodes.size),
        (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < dag.nodes.size),
      P index hIndex (dag.nodeAt index hIndex) := by
  have hAll :
      ∀ index (hIndex : index < dag.nodes.size),
        P index hIndex (dag.nodeAt index hIndex) := by
    intro index
    refine Nat.strongRecOn index ?_
    intro index ih hIndex
    exact hStep index hIndex (fun parent hParent =>
      let hParentLt := hParents index hIndex parent hParent
      let hParentSize := Nat.lt_trans hParentLt hIndex
      ih parent hParentLt hParentSize)
  exact hAll

/-- 根节点版本的拓扑归纳骨架。 -/
theorem rootByTopologicalInduction {σ : Signature.{u, v, w}}
    (dag : DAG σ) (hRoot : dag.root < dag.nodes.size) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < dag.nodes.size),
        (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    P dag.root hRoot (dag.nodeAt dag.root hRoot) :=
  dag.topologicalInduction hParents hStep dag.root hRoot

end DAG

/-- 已通过整图 checker 的原生高阶 DAG。 -/
structure CheckedDAG {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] where
  dag : DAG σ
  checked : dag.check = true

/-! ## HO-AVATAR 全局 registry 包装 -/

/-- 通过基础 DAG checker 且 selector registry 全局一致的 HO-DAG。 -/
structure CheckedAvatarDAG {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] where
  checked : CheckedDAG (σ := σ)
  registryChecked : checked.dag.avatarSelectorRegistryChecked = true

namespace CheckedAvatarDAG

/-- 从 checked HO-DAG 计算全局 selector registry 合同。 -/
def mk? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (checked : CheckedDAG (σ := σ)) : Option (CheckedAvatarDAG (σ := σ)) :=
  if hRegistry : checked.dag.avatarSelectorRegistryChecked = true then
    some { checked := checked, registryChecked := hRegistry }
  else
    none

end CheckedAvatarDAG

namespace CheckedDAG

/-- 从未检查 DAG 计算式构造 checked DAG。 -/
def mk? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) : Option (CheckedDAG (σ := σ)) :=
  if h : dag.check = true then
    some { dag := dag, checked := h }
  else
    none

private theorem check_fields {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) :
    ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
      dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
        dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) := by
  simpa [DAG.check] using hCheck

/-- checked DAG 的根节点存在性。 -/
theorem rootExists {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.root < cert.dag.nodes.size := by
  have hRoot := (check_fields cert.checked).1.1.1.1.1.1
  simpa [DAG.rootExists] using hRoot

/-- checked DAG 的根节点闭合检查。 -/
theorem rootClosed {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.rootClosed = true :=
  (check_fields cert.checked).1.1.1.1.1.2

/-- checked DAG 的 dense-id 检查。 -/
theorem denseIds {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.denseIds = true :=
  (check_fields cert.checked).1.1.1.1.2

/-- checked DAG 的 Prop 版父边拓扑条件。 -/
theorem parentsBefore {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.ParentsBefore :=
  DAG.parentsBefore_of_eq_true (check_fields cert.checked).1.1.1.2

/-- checked DAG 的 payload 全检布尔条件。 -/
theorem payloadsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.payloadsChecked = true :=
  (check_fields cert.checked).1.1.2

/-- checked DAG 的父字句快照全检布尔条件。 -/
theorem parentSnapshotsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.parentSnapshotsChecked = true :=
  (check_fields cert.checked).1.2

/-- checked DAG 的 guard 与 residual 链接检查。 -/
theorem guardsChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    cert.dag.guardsChecked = true :=
  (check_fields cert.checked).2

/-- checked DAG 中每个节点的 id 等于数组位置。 -/
theorem nodeId {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (index : Nat)
    (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).id = index :=
  DAG.denseIds_of_eq_true cert.denseIds index hIndex

/-- checked DAG 中每个节点的局部 payload 检查都通过。 -/
theorem nodeChecked {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (index : Nat)
    (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).check cert.dag.problem = true :=
  DAG.payloadsChecked_of_eq_true cert.payloadsChecked index hIndex

/-- checked DAG 中每个节点的 guard 局部检查都通过。 -/
theorem nodeGuardsChecked {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    cert.dag.localNodeGuardsOk (cert.dag.nodeAt index hIndex) = true :=
  DAG.guardsChecked_of_eq_true cert.guardsChecked index hIndex

/-- checked DAG 中 residual initial 的整图链接都通过。 -/
theorem nodePropInitialLinksChecked {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    cert.dag.propInitialLinksOk (cert.dag.nodeAt index hIndex) = true :=
  DAG.propInitialLinksChecked_of_eq_true cert.guardsChecked index hIndex

/-- 从整图支持检查读取单个节点的无 guard 支持。 -/
theorem nodeSoundnessSupported {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).soundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [DAG.soundnessSupported, DAG.nodeAt] using hAll index hIndex

/-- 从整图支持检查读取单个节点的 witness-free 支持。 -/
theorem nodeWitnessFreeSoundnessSupported {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.witnessFreeSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).witnessFreeSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [DAG.witnessFreeSoundnessSupported, DAG.nodeAt] using hAll index hIndex

/-- 从整图支持检查读取单个节点的 guarded 支持。 -/
theorem nodeGuardedSoundnessSupported {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).guardedSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [DAG.guardedSoundnessSupported, DAG.nodeAt] using hAll index hIndex

/-- guard-union 节点的当前 guards 蕴含任一父节点 guards。 -/
theorem parentGuardsHold_of_localNodeGuardsOk
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hMerge :
      DAG.payloadMergesParentGuards
        (cert.dag.nodeAt index hIndex).payload = true)
    (parent : Nat)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation
        (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [if_pos hMerge] at hGuardCheck
  cases hUnion :
      cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hGuardCheck
  | some unionGuards =>
      have hEq :
          guardSetEq (cert.dag.nodeAt index hIndex).guards unionGuards = true := by
        simpa [hUnion] using hGuardCheck
      intro hCurrentGuards
      have hUnionGuards : Node.GuardsHold valuation unionGuards :=
        Node.GuardsHold.of_guardSetEq hEq hCurrentGuards
      intro lit hLit
      exact hUnionGuards lit
        (DAG.mem_parentGuardUnionList_of_parent_mem
          (dag := cert.dag)
          (parents := (cert.dag.nodeAt index hIndex).parents.toList)
          (parent := parent)
          (parentNode := cert.dag.nodeAt parent hParentSize)
          (guards := unionGuards)
          (lit := lit)
          (by simpa [DAG.parentGuardUnion?] using hUnion)
          hParentMem
          (cert.dag.node?_eq_some_nodeAt hParentSize)
          hLit)

/-- guarded 拓扑父不变量与 guard-union checker 给出父快照全环境有效性。 -/
theorem parentClauseValidOfGuards
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hMerge :
      DAG.payloadMergesParentGuards
        (cert.dag.nodeAt index hIndex).payload = true)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (hCurrentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards)
    (parent : ParentClause σ)
    (hParent : parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList) :
    parent.clause.Valid M := by
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    Payload.parentIdsIn_of_check (cert.nodeChecked index hIndex) parent hParent
  have hParentLt := cert.parentsBefore index hIndex parent.id hParentMem
  have hParentSize : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans hParentLt hIndex
  have hInvariant := hParents parent.id hParentMem
  have hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex hMerge
      parent.id hParentMem hParentSize hCurrentGuards
  have hSnapshotCheck :
      cert.dag.parentSnapshotChecked parent = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.parentSnapshotsChecked
      index hIndex parent hParent
  rcases DAG.parentSnapshotChecked_sound hSnapshotCheck with
    ⟨snapshotNode, snapshotConclusion, hNodeLookup, hSnapshotConclusion, hClauseEq⟩
  have hActualLookup :
      cert.dag.node? parent.id =
        some (cert.dag.nodeAt parent.id hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  have hNodeEq :
      snapshotNode = cert.dag.nodeAt parent.id hParentSize :=
    Option.some.inj (hNodeLookup.symm.trans hActualLookup)
  subst snapshotNode
  rcases hInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = snapshotConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hSnapshotConclusion)
  subst invariantConclusion
  intro env hEnv
  simpa [hClauseEq] using hSatisfies env hEnv hParentGuards

/-- 拓扑父节点不变量与整图快照检查共同给出父快照的全环境有效性。 -/
theorem parentClauseValid {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.Invariant (M := M) cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (parent : ParentClause σ)
    (hParent : parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList) :
    parent.clause.Valid M := by
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    Payload.parentIdsIn_of_check (cert.nodeChecked index hIndex) parent hParent
  have hParentLt := cert.parentsBefore index hIndex parent.id hParentMem
  have hParentSize : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans hParentLt hIndex
  have hInvariant := hParents parent.id hParentMem
  have hSnapshotCheck :
      cert.dag.parentSnapshotChecked parent = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.parentSnapshotsChecked
      index hIndex parent hParent
  rcases DAG.parentSnapshotChecked_sound hSnapshotCheck with
    ⟨snapshotNode, snapshotConclusion, hNodeLookup, hSnapshotConclusion, hClauseEq⟩
  have hActualLookup :
      cert.dag.node? parent.id =
        some (cert.dag.nodeAt parent.id hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  have hNodeEq :
      snapshotNode = cert.dag.nodeAt parent.id hParentSize :=
    Option.some.inj (hNodeLookup.symm.trans hActualLookup)
  subst snapshotNode
  rcases hInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hInvariantSat⟩
  have hConclusionEq : invariantConclusion = snapshotConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hSnapshotConclusion)
  subst invariantConclusion
  simpa [hClauseEq] using hInvariantSat

/-- 给定父 guard 成立时，guarded 拓扑不变量可回放任意父快照。 -/
theorem parentClauseSatisfiesOfGuards
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (parent : ParentClause σ)
    (hParentMem : parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshotCheck : cert.dag.parentSnapshotChecked parent = true)
    (hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt parent.id hParentSize).guards)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted []) :
    parent.clause.Satisfies env := by
  have hInvariant := hParents parent.id hParentMem
  rcases DAG.parentSnapshotChecked_sound hSnapshotCheck with
    ⟨snapshotNode, snapshotConclusion, hNodeLookup, hSnapshotConclusion, hClauseEq⟩
  have hActualLookup :
      cert.dag.node? parent.id =
        some (cert.dag.nodeAt parent.id hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  have hNodeEq :
      snapshotNode = cert.dag.nodeAt parent.id hParentSize :=
    Option.some.inj (hNodeLookup.symm.trans hActualLookup)
  subst snapshotNode
  rcases hInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = snapshotConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hSnapshotConclusion)
  subst invariantConclusion
  simpa [hClauseEq] using hSatisfies env hEnv hParentGuards

/-- checked DAG 的根结论存在且为空。 -/
theorem rootConclusion {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    ∃ conclusion,
      (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion? cert.dag.problem =
          some conclusion ∧
        conclusion.isEmpty = true := by
  have hClosed := cert.rootClosed
  unfold DAG.rootClosed at hClosed
  rw [cert.dag.node?_eq_some_nodeAt cert.rootExists] at hClosed
  change
    (match
        (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion? cert.dag.problem with
      | some conclusion =>
          (cert.dag.nodeAt cert.dag.root cert.rootExists).unguarded &&
            conclusion.isEmpty
      | none => false) = true at hClosed
  cases hConclusion :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion? cert.dag.problem with
  | none =>
      simp [hConclusion] at hClosed
  | some conclusion =>
      have hEmpty : conclusion.isEmpty = true := by
        exact (Bool.and_eq_true_iff.mp (by
          simpa [hConclusion] using hClosed)).2
      exact ⟨conclusion, rfl, hEmpty⟩

/-- checked DAG 的根节点没有 AVATAR guard。 -/
theorem rootUnguarded {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) :
    (cert.dag.nodeAt cert.dag.root cert.rootExists).unguarded = true := by
  have hClosed := cert.rootClosed
  unfold DAG.rootClosed at hClosed
  rw [cert.dag.node?_eq_some_nodeAt cert.rootExists] at hClosed
  cases hConclusion :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion? cert.dag.problem with
  | none =>
      simp [Node.globallyClosed, hConclusion] at hClosed
  | some conclusion =>
      exact (Bool.and_eq_true_iff.mp (by
        simpa [Node.globallyClosed, hConclusion] using hClosed)).1

/-- checked DAG 上的拓扑归纳入口。 -/
theorem topologicalInduction {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)
              (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      P index hIndex (cert.dag.nodeAt index hIndex) :=
  cert.dag.topologicalInduction cert.parentsBefore hStep

/-- checked DAG 根节点上的拓扑归纳入口。 -/
theorem rootByTopologicalInduction {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)
              (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    P cert.dag.root cert.rootExists
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.dag.rootByTopologicalInduction cert.rootExists cert.parentsBefore hStep

/-- 当前支持节点的一步拓扑 soundness。 -/
theorem supportedTopologicalStep {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.soundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.Invariant (M := M) cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) :
    Node.Invariant (M := M) cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  simpa [Node.Invariant, Node.conclusion?, Node.check] using
    Payload.sound contract witnessContract hProblem
      (cert.dag.nodeAt index hIndex).payload
      (cert.dag.nodeAt index hIndex).parents
      (Bool.and_eq_true_iff.mp
        (cert.nodeSoundnessSupported hSupported index hIndex)).2
      (cert.nodeChecked index hIndex)
      (fun parent hParent =>
        cert.parentClauseValid index hIndex hParents parent hParent)

/-- 整图 soundness：每个 checked 节点都满足其机械结论。 -/
theorem invariant {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.soundnessSupported = true) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      Node.Invariant (M := M) cert.dag.problem (cert.dag.nodeAt index hIndex) :=
  cert.topologicalInduction fun index hIndex hParents =>
    cert.supportedTopologicalStep contract witnessContract hProblem hSupported
      index hIndex hParents

/-- 根节点 soundness。 -/
theorem rootInvariant {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.soundnessSupported = true) :
    Node.Invariant (M := M) cert.dag.problem
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.rootByTopologicalInduction fun index hIndex hParents =>
    cert.supportedTopologicalStep contract witnessContract hProblem hSupported
      index hIndex hParents

/-- 无显式差异见证合同的一步拓扑 soundness。 -/
theorem witnessFreeTopologicalStep {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.witnessFreeSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.Invariant (M := M) cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) :
    Node.Invariant (M := M) cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  simpa [Node.Invariant, Node.conclusion?, Node.check] using
    Payload.soundWitnessFree contract hProblem
      (cert.dag.nodeAt index hIndex).payload
      (cert.dag.nodeAt index hIndex).parents
      (Bool.and_eq_true_iff.mp
        (cert.nodeWitnessFreeSoundnessSupported hSupported index hIndex)).2
      (cert.nodeChecked index hIndex)
      (fun parent hParent =>
        cert.parentClauseValid index hIndex hParents parent hParent)

/-- witness-free 支持片段的整图 soundness。 -/
theorem witnessFreeInvariant {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.witnessFreeSoundnessSupported = true) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      Node.Invariant (M := M) cert.dag.problem (cert.dag.nodeAt index hIndex) :=
  cert.topologicalInduction fun index hIndex hParents =>
    cert.witnessFreeTopologicalStep contract hProblem hSupported index hIndex hParents

/-- witness-free 支持片段的根节点 soundness。 -/
theorem rootWitnessFreeInvariant {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.witnessFreeSoundnessSupported = true) :
    Node.Invariant (M := M) cert.dag.problem
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.rootByTopologicalInduction fun index hIndex hParents =>
    cert.witnessFreeTopologicalStep contract hProblem hSupported index hIndex hParents

/-- 根节点不变量与 checker 给出的空结论共同推出矛盾。 -/
theorem rootEmptyContradiction_of_rootInvariant {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ}
    (cert : CheckedDAG (σ := σ)) (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted [])
    (hInvariant :
      Node.Invariant (M := M) cert.dag.problem
        (cert.dag.nodeAt cert.dag.root cert.rootExists)) : False := by
  rcases cert.rootConclusion with ⟨rootConclusion, hRootConclusion, hRootEmpty⟩
  rcases hInvariant with ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = rootConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hRootConclusion)
  subst rootConclusion
  exact Clause.not_satisfies_of_isEmpty hRootEmpty (hSatisfies env hEnv)

/-- 原生高阶整图证书的空根反证总定理。 -/
theorem refutes {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted [])
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.soundnessSupported = true) : False :=
  cert.rootEmptyContradiction_of_rootInvariant env hEnv
    (cert.rootInvariant contract witnessContract hProblem hSupported)

/-- 无显式差异见证合同的原生 HO 空根反证总定理。 -/
theorem refutesWitnessFree {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted [])
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.witnessFreeSoundnessSupported = true) : False :=
  cert.rootEmptyContradiction_of_rootInvariant env hEnv
    (cert.rootWitnessFreeInvariant contract hProblem hSupported)

/-- residual CDCL 的 initial justification 槽位检查解包。 -/
private theorem propClosureJustificationCheckAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {payload : PropositionalClosurePayload σ}
    (hCheck : payload.justificationsCheck parents = true)
    {slot : Nat} (hSlot : slot < payload.initialClauses.size) :
    ∃ hJust : slot < payload.initialJustifications.size,
      payload.initialJustifications[slot].check parents payload.atomMap
        payload.initialClauses[slot] = true := by
  unfold PropositionalClosurePayload.justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSizeBool, hAllBool⟩
  have hSizeEq :
      payload.initialClauses.size = payload.initialJustifications.size :=
    beq_iff_eq.mp hSizeBool
  have hJust : slot < payload.initialJustifications.size := by
    simpa [hSizeEq] using hSlot
  refine ⟨hJust, ?_⟩
  have hAt :=
    (Array.all_eq_true.mp hAllBool) slot (by
      simpa [Array.size_mapIdx] using hSlot)
  have hJustGet :
      payload.initialJustifications[slot]? =
        some payload.initialJustifications[slot] :=
    Array.getElem?_eq_some_iff.mpr ⟨hJust, rfl⟩
  simpa [Array.getElem_mapIdx, hJustGet] using hAt

/-- 普通 HO payload 的 guarded 拓扑 step。 -/
theorem ordinaryGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (hPayloadSupported :
      (cert.dag.nodeAt index hIndex).payload.soundnessSupported = true) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  rcases Payload.conclusion_exists_of_check (cert.nodeChecked index hIndex) with
    ⟨conclusion, hConclusion⟩
  refine ⟨conclusion, hConclusion, ?_⟩
  intro env hEnv hCurrentGuards
  have hMergeOfParent :
      ∀ parent,
        parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList →
          DAG.payloadMergesParentGuards
            (cert.dag.nodeAt index hIndex).payload = true := by
    intro parent hParent
    cases hPayload : (cert.dag.nodeAt index hIndex).payload <;>
      simp [hPayload, Payload.parentClauses, Payload.soundnessSupported,
        DAG.payloadMergesParentGuards] at hParent hPayloadSupported ⊢
  rcases Payload.sound contract witnessContract hProblem
      (cert.dag.nodeAt index hIndex).payload
      (cert.dag.nodeAt index hIndex).parents
      hPayloadSupported
      (cert.nodeChecked index hIndex)
      (fun parent hParent =>
        cert.parentClauseValidOfGuards valuation index hIndex
          (hMergeOfParent parent hParent) hParents hCurrentGuards parent hParent) with
    ⟨soundConclusion, hSoundConclusion, hSound⟩
  have hEq : soundConclusion = conclusion :=
    Option.some.inj (hSoundConclusion.symm.trans hConclusion)
  subst soundConclusion
  exact hSound env hEnv

/-- theory conflict 节点的 guarded 拓扑 step。 -/
theorem theoryConflictGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : TheoryConflictPayload σ)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hConflictCheck :
      payload.conflict.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
        payload.conflict.clause.isEmpty = true := by
    simpa [Payload.check, TheoryConflictPayload.check] using
      Bool.and_eq_true_iff.mp hCheck
  have hParentMem :
      payload.conflict.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hConflictCheck.1
  have hParentSize : payload.conflict.id < cert.dag.nodes.size :=
    Nat.lt_trans (cert.parentsBefore index hIndex payload.conflict.id hParentMem) hIndex
  have hSnapshot :
      cert.dag.parentSnapshotChecked payload.conflict = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.parentSnapshotsChecked index hIndex
      payload.conflict (by simp [hPayload, Payload.parentClauses,
        TheoryConflictPayload.parentClauses])
  refine ⟨{ literals := #[] }, by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hCurrentGuards
  have hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex
      (by simp [hPayload, DAG.payloadMergesParentGuards])
      payload.conflict.id hParentMem hParentSize hCurrentGuards
  have hParentSat :=
    cert.parentClauseSatisfiesOfGuards valuation index hIndex hParents
      payload.conflict hParentMem hParentSize hSnapshot hParentGuards env hEnv
  exact False.elim
    (Clause.not_satisfies_of_isEmpty hConflictCheck.2 hParentSat)

/-- propositional learned-clause 节点的 guarded 拓扑 step。 -/
theorem propositionalLearnedClauseGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : PropositionalLearnedClausePayload)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload =
        .propositionalLearnedClause payload) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hParentIn :
      (cert.dag.nodeAt index hIndex).parents.contains payload.conflict = true := by
    simpa [Payload.check, PropositionalLearnedClausePayload.check] using hCheck
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    exact Array.mem_def.mp (by simpa using hParentIn)
  have hParentSize : payload.conflict < cert.dag.nodes.size :=
    Nat.lt_trans (cert.parentsBefore index hIndex payload.conflict hParentMem) hIndex
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
  have hParentLookup :
      cert.dag.node? payload.conflict =
        some (cert.dag.nodeAt payload.conflict hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [if_neg (by simp [hPayload, DAG.payloadMergesParentGuards])] at hGuardCheck
  simp only [hPayload] at hGuardCheck
  rw [hParentLookup] at hGuardCheck
  rcases Bool.and_eq_true_iff.mp hGuardCheck with
    ⟨hPrefix, _hLearned⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with
    ⟨hConflictPrefix, hGuardEq⟩
  rcases Bool.and_eq_true_iff.mp hConflictPrefix with
    ⟨_hArtifact, _hTheory⟩
  refine ⟨{ literals := #[] }, by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hCurrentGuards
  have hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.conflict hParentSize).guards :=
    Node.GuardsHold.of_guardSetEq hGuardEq hCurrentGuards
  rcases hParents payload.conflict hParentMem with
    ⟨parentConclusion, hParentConclusion, hParentSat⟩
  have hParentEmpty :
      parentConclusion.isEmpty = true := by
    have hTheory :
        (cert.dag.nodeAt payload.conflict hParentSize).theoryConflict
          cert.dag.problem = true :=
      _hTheory
    unfold Node.theoryConflict at hTheory
    rw [hParentConclusion] at hTheory
    exact (Bool.and_eq_true_iff.mp hTheory).2
  exact False.elim
    (Clause.not_satisfies_of_isEmpty hParentEmpty
      (hParentSat env hEnv hParentGuards))

/-- residual CDCL 节点的 guarded 拓扑 step。 -/
theorem residualCdclGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : PropositionalClosurePayload σ)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .residualCdcl payload)
    (hPayloadSupported : payload.guardedSoundnessSupported = true) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hResidualCheck :
      (!((cert.dag.nodeAt index hIndex).parents.isEmpty) &&
        payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check] using hCheck
  have hClosureCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hResidualCheck).2
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    (Bool.and_eq_true_iff.mp hClosureCheck).1
  have hJustifications :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hClosureCheck).2
  have hInitialLinks := cert.nodePropInitialLinksChecked index hIndex
  have hDagInitials :
      payload.initialJustifications.all
        (fun justification =>
          cert.dag.propInitialJustificationDagOk
            (cert.dag.nodeAt index hIndex).parents justification) = true := by
    simpa [DAG.propInitialLinksOk, hPayload] using hInitialLinks
  refine ⟨{ literals := #[] }, by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv _hCurrentGuards
  let checkedCert : PropResolution.CheckedUnsatCertificate := {
    initialClauses := payload.initialClauses
    proof := payload.proof
    checked := hCheckedUnsat
  }
  apply False.elim
  apply checkedCert.sound
    (valuation := PropLiteralLink.valuation valuation payload.atomMap env)
  intro initial hInitialMem
  have hInitialArray : initial ∈ payload.initialClauses :=
    Array.mem_def.mpr hInitialMem
  rcases Array.mem_iff_getElem.mp hInitialArray with
    ⟨slot, hSlot, hInitialGet⟩
  rcases propClosureJustificationCheckAt hJustifications hSlot with
    ⟨hJustSlot, hJustificationCheck⟩
  have hDagOk :=
    (Array.all_eq_true.mp hDagInitials) slot hJustSlot
  have hJustificationSupported :
      payload.initialJustifications[slot].guardedSoundnessSupported = true := by
    have hAll := Array.all_eq_true.mp hPayloadSupported
    simpa using hAll slot hJustSlot
  cases hJustification : payload.initialJustifications[slot] with
  | parentClause link =>
      have hLinkCheck :
          link.check (cert.dag.nodeAt index hIndex).parents payload.atomMap initial =
            true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropParentClauseLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hLiteralChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hObjectEqBool⟩
      have hInitialEq : initial.clause = link.encodedClause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hObjectEq : link.parent.clause = link.objectClause :=
        Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
      have hDagParent :
          cert.dag.propParentInitialLinkOk
            (cert.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
      unfold DAG.propParentInitialLinkOk at hDagParent
      rcases Bool.and_eq_true_iff.mp hDagParent with
        ⟨hDagPrefix, hParentUnguardedCheck⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize : link.parent.id < cert.dag.nodes.size :=
        Nat.lt_trans
          (cert.parentsBefore index hIndex link.parent.id hParentMem) hIndex
      have hParentLookup :
          cert.dag.node? link.parent.id =
            some (cert.dag.nodeAt link.parent.id hParentSize) :=
        cert.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentUnguardedCheck
      have hParentGuards :
          Node.GuardsHold valuation
            (cert.dag.nodeAt link.parent.id hParentSize).guards :=
        Node.GuardsHold.of_isEmpty hParentUnguardedCheck
      have hObjectSat : link.objectClause.Satisfies env := by
        have hParentSat :=
          cert.parentClauseSatisfiesOfGuards valuation index hIndex hParents
            link.parent hParentMem hParentSize hSnapshot hParentGuards env hEnv
        simpa [hObjectEq] using hParentSat
      simpa [hInitialEq] using
        PropParentClauseLink.encodedClause_satisfies_of_object
          (base := valuation) (env := env) hLiteralChecks hObjectSat
  | guardActivationClause link =>
      have hLinkCheck :
          link.check (cert.dag.nodeAt index hIndex).parents payload.atomMap initial =
            true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropGuardActivationLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hLiteralChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hGuardChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hObjectEqBool⟩
      have hInitialEq : initial.clause = link.encodedClause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hObjectEq : link.parent.clause = link.objectClause :=
        Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
      have hDagActivation :
          cert.dag.propGuardActivationInitialLinkOk
            (cert.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
      unfold DAG.propGuardActivationInitialLinkOk at hDagActivation
      rcases Bool.and_eq_true_iff.mp hDagActivation with
        ⟨hDagPrefix, hParentFields⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize : link.parent.id < cert.dag.nodes.size :=
        Nat.lt_trans
          (cert.parentsBefore index hIndex link.parent.id hParentMem) hIndex
      have hParentLookup :
          cert.dag.node? link.parent.id =
            some (cert.dag.nodeAt link.parent.id hParentSize) :=
        cert.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentFields
      rcases Bool.and_eq_true_iff.mp hParentFields with
        ⟨_hGuarded, hGuardEq⟩
      have hActivationSat :=
        PropGuardActivationLink.encodedClause_satisfies
          (base := valuation) (env := env) hGuardChecks hLiteralChecks
          (fun hLinkGuards => by
            have hParentGuards :
                Node.GuardsHold valuation
                  (cert.dag.nodeAt link.parent.id hParentSize).guards :=
              Node.GuardsHold.of_guardSetEq hGuardEq hLinkGuards
            have hParentSat :=
              cert.parentClauseSatisfiesOfGuards valuation index hIndex hParents
                link.parent hParentMem hParentSize hSnapshot hParentGuards env hEnv
            simpa [hObjectEq] using hParentSat)
      simpa [hInitialEq] using hActivationSat
  | propLearnedClause link =>
      have hLinkCheck :
          link.check (cert.dag.nodeAt index hIndex).parents payload.atomMap initial =
            true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropLearnedClauseLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hLearnedEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hOutside⟩
      have hInitialEq : initial.clause = link.clause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hLearnedEq : link.clause = learnedClauseOfGuards link.guards :=
        PropResolution.clauseEq_eq.mp hLearnedEqBool
      have hDagLearned :
          cert.dag.propLearnedInitialLinkOk
            (cert.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
      unfold DAG.propLearnedInitialLinkOk at hDagLearned
      have hParentMem :
          link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
        exact Array.mem_def.mp (by
          simpa using (Bool.and_eq_true_iff.mp hDagLearned).1)
      have hParentSize : link.parent < cert.dag.nodes.size :=
        Nat.lt_trans
          (cert.parentsBefore index hIndex link.parent hParentMem) hIndex
      have hParentLookup :
          cert.dag.node? link.parent =
            some (cert.dag.nodeAt link.parent hParentSize) :=
        cert.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hDagLearned
      rcases Bool.and_eq_true_iff.mp hDagLearned with
        ⟨_hParentIn, hParentPayloadCheck⟩
      cases hParentPayload :
          (cert.dag.nodeAt link.parent hParentSize).payload with
      | propositionalLearnedClause learnedPayload =>
          simp [hParentPayload] at hParentPayloadCheck
          rcases hParentPayloadCheck with ⟨hGuardEq, _hClauseEq⟩
          by_cases hGuards : Node.GuardsHold valuation link.guards
          · have hParentGuards :
                Node.GuardsHold valuation
                  (cert.dag.nodeAt link.parent hParentSize).guards :=
              Node.GuardsHold.of_guardSetEq hGuardEq hGuards
            rcases hParents link.parent hParentMem with
              ⟨parentConclusion, hParentConclusion, hParentSat⟩
            have hParentEmpty : parentConclusion.isEmpty = true := by
              rw [Node.conclusion?, hParentPayload, Payload.conclusion?] at hParentConclusion
              have hEq : parentConclusion = { literals := #[] } :=
                Option.some.inj hParentConclusion.symm
              subst parentConclusion
              simp [Clause.isEmpty]
            exact False.elim
              (Clause.not_satisfies_of_isEmpty hParentEmpty
                (hParentSat env hEnv hParentGuards))
          · simpa [hInitialEq] using
              PropLearnedClauseLink.satisfies_of_not_guards
                (base := valuation) (env := env) hLearnedEq hOutside hGuards
      | source initialIndex => simp [hParentPayload] at hParentPayloadCheck
      | avatarSplit splitPayload => simp [hParentPayload] at hParentPayloadCheck
      | avatarComponent componentPayload => simp [hParentPayload] at hParentPayloadCheck
      | beta betaPayload => simp [hParentPayload] at hParentPayloadCheck
      | eta etaPayload => simp [hParentPayload] at hParentPayloadCheck
      | substitution evidence => simp [hParentPayload] at hParentPayloadCheck
      | standardizeApart evidence => simp [hParentPayload] at hParentPayloadCheck
      | resolution evidence => simp [hParentPayload] at hParentPayloadCheck
      | factoring evidence => simp [hParentPayload] at hParentPayloadCheck
      | equalityResolution evidence => simp [hParentPayload] at hParentPayloadCheck
      | booleanExtensionality evidence => simp [hParentPayload] at hParentPayloadCheck
      | demodulation evidence => simp [hParentPayload] at hParentPayloadCheck
      | positiveSuperposition evidence => simp [hParentPayload] at hParentPayloadCheck
      | negativeSuperposition evidence => simp [hParentPayload] at hParentPayloadCheck
      | extensionalParamodulation evidence => simp [hParentPayload] at hParentPayloadCheck
      | argumentCongruence evidence => simp [hParentPayload] at hParentPayloadCheck
      | functionExtensionality evidence => simp [hParentPayload] at hParentPayloadCheck
      | theoryConflict conflictPayload => simp [hParentPayload] at hParentPayloadCheck
      | residualCdcl closurePayload => simp [hParentPayload] at hParentPayloadCheck
  | avatarSkeleton link =>
      rw [hJustification] at hJustificationSupported
      simp [PropInitialJustification.guardedSoundnessSupported] at hJustificationSupported

/-- 当前 guarded soundness 支持片段的一步拓扑回放。 -/
theorem guardedSoundnessSupportedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedInvariant (M := M) valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have _hNodeSupported :=
    cert.nodeGuardedSoundnessSupported hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | avatarSplit payload =>
      change (cert.dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true
        at _hNodeSupported
      rw [hPayload] at _hNodeSupported
      simp [Payload.guardedSoundnessSupported] at _hNodeSupported
  | avatarComponent payload =>
      change (cert.dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true
        at _hNodeSupported
      rw [hPayload] at _hNodeSupported
      simp [Payload.guardedSoundnessSupported] at _hNodeSupported
  | beta payload =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | eta payload =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | substitution evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | standardizeApart evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | resolution evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | factoring evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | equalityResolution evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | booleanExtensionality evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | demodulation evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | positiveSuperposition evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | negativeSuperposition evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | extensionalParamodulation evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | argumentCongruence evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | functionExtensionality evidence =>
      exact cert.ordinaryGuardedTopologicalStep contract witnessContract valuation
        hProblem index hIndex hParents (by simp [hPayload, Payload.soundnessSupported])
  | theoryConflict payload =>
      exact cert.theoryConflictGuardedTopologicalStep valuation index hIndex
        hParents payload hPayload
  | propositionalLearnedClause payload =>
      exact cert.propositionalLearnedClauseGuardedTopologicalStep valuation
        index hIndex hParents payload hPayload
  | residualCdcl payload =>
      have hPayloadSupported :
          payload.guardedSoundnessSupported = true := by
        change (cert.dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true
          at _hNodeSupported
        rw [hPayload] at _hNodeSupported
        simpa [Payload.guardedSoundnessSupported] using _hNodeSupported
      exact cert.residualCdclGuardedTopologicalStep valuation index hIndex
        hParents payload hPayload hPayloadSupported

/-- 整图 guarded soundness。 -/
theorem guardedInvariant
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      Node.GuardedInvariant (M := M) valuation cert.dag.problem
        (cert.dag.nodeAt index hIndex) :=
  cert.topologicalInduction fun index hIndex hParents =>
    cert.guardedSoundnessSupportedTopologicalStep contract witnessContract
      valuation hProblem hSupported index hIndex hParents

/-- 根节点的 guarded soundness。 -/
theorem rootGuardedInvariant
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    Node.GuardedInvariant (M := M) valuation cert.dag.problem
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.rootByTopologicalInduction fun index hIndex hParents =>
    cert.guardedSoundnessSupportedTopologicalStep contract witnessContract
      valuation hProblem hSupported index hIndex hParents

/-- 无 guard 空根与 guarded 不变量给出矛盾。 -/
theorem rootEmptyContradiction_of_rootGuardedInvariant
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted [])
    (hInvariant :
      Node.GuardedInvariant (M := M) valuation cert.dag.problem
        (cert.dag.nodeAt cert.dag.root cert.rootExists)) : False := by
  rcases cert.rootConclusion with ⟨rootConclusion, hRootConclusion, hRootEmpty⟩
  rcases hInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = rootConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hRootConclusion)
  subst rootConclusion
  have hRootGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt cert.dag.root cert.rootExists).guards :=
    Node.GuardsHold.of_isEmpty cert.rootUnguarded
  exact Clause.not_satisfies_of_isEmpty hRootEmpty
    (hSatisfies env hEnv hRootGuards)

/-- AVATAR guards 与 residual CDCL 已接入后的 HO-DAG 空根反证总定理。 -/
theorem refutesGuarded
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure.{u, v, w, x} σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (valuation : PropResolution.Valuation)
    (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted [])
    (hProblem : cert.dag.problem.Valid M)
    (hSupported : cert.dag.guardedSoundnessSupported = true) : False :=
  cert.rootEmptyContradiction_of_rootGuardedInvariant valuation env hEnv
    (cert.rootGuardedInvariant contract witnessContract valuation
      hProblem hSupported)

end CheckedDAG

end HODAGCertificate
end Automation
end YesMetaZFC
