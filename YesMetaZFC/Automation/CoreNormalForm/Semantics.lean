import YesMetaZFC.Automation.CoreNormalForm
/-!
# Core normal form 的 Tarski 语义
本模块给 preprocessing 使用的 `CoreSyntax` 建立独立语义层。它不桥接旧 MF1/LCF：
* 所有 sort 共用一个 carrier，并由 `sortInterp` 指定各 sort 的论域；
* bound/free 变量环境与 locally nameless 语法直接对应；
* 函数、谓词、FOOL 布尔项和高阶构造均由模型显式解释；
* NNF、literal、clause 与 clause set 的满足关系建立在同一模型上。
后续 anti-prenex、局部 Skolem 化和定义性 CNF 的 soundness 都只消费这里的语义。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
universe x
structure Truth (_carrier : Type x) : Type x where
  holds : Prop
structure Model where
  Carrier : Type x
  default : Carrier
  sortInterp : CoreSort → Carrier → Prop
  sortNonempty : ∀ sort, ∃ value, sortInterp sort value
  functionInterp : FunctionSymbol → List Carrier → Carrier
  predicateInterp : PredicateSymbol → List Carrier → Prop
  applyInterp : Carrier → Carrier → Carrier
  boolValue : Bool → Carrier
  notValue : Carrier → Carrier
  andValue : Carrier → Carrier → Carrier
  orValue : Carrier → Carrier → Carrier
  impValue : Carrier → Carrier → Carrier
  iffValue : Carrier → Carrier → Carrier
  quoteValue : Prop → Carrier
  lambdaValue : CoreSort → CoreSort → (Carrier → Carrier) → Carrier
  iteValue : Prop → Carrier → Carrier → Carrier
  boolHolds : Carrier → Prop
instance (M : Model) : Inhabited M.Carrier :=
  ⟨M.default⟩
structure Env (M : Model) where
  boundVal : Nat → M.Carrier
  freeVal : CoreSort → VarId → M.Carrier
namespace Env
/-- 环境逐点相等即为记录相等，所有解释函数共用这一外延性。 -/
theorem ext {M : Model} (env₁ env₂ : Env M)
    (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
    (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id) : env₁ = env₂ := by
  cases env₁
  cases env₂
  congr
  · exact funext hBound
  · exact funext (fun sort => funext (hFree sort))

def push {M : Model} (env : Env M) (value : M.Carrier) : Env M where
  boundVal := fun index =>
    match index with
    | 0 => value
    | previous + 1 => env.boundVal previous
  freeVal := env.freeVal
def drop {M : Model} (amount : Nat) (env : Env M) : Env M where
  boundVal := fun index => env.boundVal (index + amount)
  freeVal := env.freeVal
def skip {M : Model} (amount cutoff : Nat) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < cutoff then env.boundVal index else env.boundVal (index + amount)
  freeVal := env.freeVal
def insertAt {M : Model} (depth : Nat) (value : M.Carrier) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < depth then
      env.boundVal index
    else if index = depth then
      value
    else
      env.boundVal (index - 1)
  freeVal := env.freeVal
def setFree {M : Model} (env : Env M) (sort : CoreSort) (id : VarId) (value : M.Carrier) : Env M where
  boundVal := env.boundVal
  freeVal := fun targetSort targetId =>
    if targetSort = sort ∧ targetId = id then value else env.freeVal targetSort targetId
@[simp]
theorem push_bound_zero {M : Model} (env : Env M) (value : M.Carrier) : (env.push value).boundVal 0 = value :=
  rfl
@[simp]
theorem push_bound_succ {M : Model} (env : Env M) (value : M.Carrier) (index : Nat) : (env.push value).boundVal (index + 1) = env.boundVal index :=
  rfl
@[simp]
theorem push_free {M : Model} (env : Env M) (value : M.Carrier) (sort : CoreSort) (id : VarId) : (env.push value).freeVal sort id = env.freeVal sort id :=
  rfl
@[simp]
theorem drop_bound {M : Model} (amount : Nat) (env : Env M) (index : Nat) : (env.drop amount).boundVal index = env.boundVal (index + amount) :=
  rfl
@[simp]
theorem drop_free {M : Model} (amount : Nat) (env : Env M) (sort : CoreSort) (id : VarId) : (env.drop amount).freeVal sort id = env.freeVal sort id :=
  rfl
@[simp]
theorem skip_free {M : Model} (amount cutoff : Nat) (env : Env M) (sort : CoreSort) (id : VarId) : (env.skip amount cutoff).freeVal sort id = env.freeVal sort id :=
  rfl
theorem skip_zero_bound {M : Model} (amount : Nat) (env : Env M) (index : Nat) : (env.skip amount 0).boundVal index = (env.drop amount).boundVal index := by simp [skip, drop]
theorem skip_push_bound {M : Model} (amount cutoff : Nat) (env : Env M) (value : M.Carrier) (index : Nat) : ((env.push value).skip amount (cutoff + 1)).boundVal index = ((env.skip amount cutoff).push value).boundVal index := by
  cases index with
  | zero => rfl
  | succ previous =>
      simp only [push_bound_succ]
      simp [skip, Nat.succ_lt_succ_iff, Nat.succ_add]
theorem drop_push_bound {M : Model} (amount : Nat) (env : Env M) (value : M.Carrier) (index : Nat) : ((env.push value).drop (amount + 1)).boundVal index = (env.drop amount).boundVal index := by
  have hIndex : index + (amount + 1) = (index + amount) + 1 := by omega
  simp only [drop_bound, hIndex, push_bound_succ]
theorem insertAt_push_bound {M : Model} (depth : Nat) (env : Env M) (inserted value : M.Carrier) (index : Nat) : ((env.push value).insertAt (depth + 1) inserted).boundVal index = ((env.insertAt depth inserted).push value).boundVal index := by
  cases index with
  | zero => rfl
  | succ previous =>
      simp only [push_bound_succ]
      by_cases hLt : previous < depth
      · simp [insertAt, Nat.succ_lt_succ_iff, hLt]
      · by_cases hEq : previous = depth
        · simp [insertAt, hEq]
        · have hPositive : 0 < previous := by omega
          cases previous with
          | zero => omega
          | succ index => simp [insertAt, Nat.succ_lt_succ_iff, hLt, hEq]
/-- 移位、删除与插入和 binder 扩张交换；上层不再逐点重建环境。 -/
@[simp] theorem skip_push {M : Model} (amount cutoff : Nat) (env : Env M) (value : M.Carrier) :
    (env.push value).skip amount (cutoff + 1) = (env.skip amount cutoff).push value :=
  ext _ _ (skip_push_bound amount cutoff env value) (fun _ _ => rfl)

@[simp] theorem drop_push {M : Model} (amount : Nat) (env : Env M) (value : M.Carrier) :
    (env.push value).drop (amount + 1) = env.drop amount :=
  ext _ _ (drop_push_bound amount env value) (fun _ _ => rfl)

@[simp] theorem insertAt_push {M : Model} (depth : Nat) (env : Env M) (inserted value : M.Carrier) :
    (env.push value).insertAt (depth + 1) inserted = (env.insertAt depth inserted).push value :=
  ext _ _ (insertAt_push_bound depth env inserted value) (fun _ _ => rfl)

end Env
mutual
  def Term.eval {M : Model} (env : Env M) : Term → M.Carrier
    | Term.bvar _ index => env.boundVal index
    | Term.fvar sort id => env.freeVal sort id
    | Term.app symbol args => M.functionInterp symbol (args.map (Term.eval env))
    | Term.apply fn arg => M.applyInterp (Term.eval env fn) (Term.eval env arg)
    | Term.bool value => M.boolValue value
    | Term.notE body => M.notValue (Term.eval env body)
    | Term.andE left right => M.andValue (Term.eval env left) (Term.eval env right)
    | Term.orE left right => M.orValue (Term.eval env left) (Term.eval env right)
    | Term.impE left right => M.impValue (Term.eval env left) (Term.eval env right)
    | Term.iffE left right => M.iffValue (Term.eval env left) (Term.eval env right)
    | Term.quote formula => M.quoteValue (Formula.eval env formula).holds
    | Term.lam domain codomain body => M.lambdaValue domain codomain (fun value => Term.eval (env.push value) body)
    | Term.ite _ condition thenTerm elseTerm =>
        M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm)
  def Formula.eval {M : Model} (env : Env M) : Formula → Truth M.Carrier
    | Formula.trueE => ⟨True⟩
    | Formula.falseE => ⟨False⟩
    | Formula.atom predicate args => ⟨M.predicateInterp predicate (args.map (Term.eval env))⟩
    | Formula.equal _ left right => ⟨Term.eval env left = Term.eval env right⟩
    | Formula.boolTerm term => ⟨M.boolHolds (Term.eval env term)⟩
    | Formula.neg body => ⟨¬ (Formula.eval env body).holds⟩
    | Formula.imp left right => ⟨(Formula.eval env left).holds → (Formula.eval env right).holds⟩
    | Formula.conj left right => ⟨(Formula.eval env left).holds ∧ (Formula.eval env right).holds⟩
    | Formula.disj left right => ⟨(Formula.eval env left).holds ∨ (Formula.eval env right).holds⟩
    | Formula.iffE left right => ⟨(Formula.eval env left).holds ↔ (Formula.eval env right).holds⟩
    | Formula.forallE sort body => ⟨∀ value, M.sortInterp sort value → (Formula.eval (env.push value) body).holds⟩
    | Formula.existsE sort body => ⟨∃ value, M.sortInterp sort value ∧ (Formula.eval (env.push value) body).holds⟩
end
namespace Formula
def Satisfies {M : Model} (env : Env M) (formula : Formula) : Prop := (Formula.eval env formula).holds
def Satisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env formula
def Unsatisfiable (formula : Formula) : Prop :=
  ¬ Satisfiable.{x} formula
end Formula
theorem Term.eval_eq_of_env_eq {M : Model} (env₁ env₂ : Env M) (hBound : ∀ index, env₁.boundVal index = env₂.boundVal
    index) (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id) (term : Term) : Term.eval env₁ term =
    Term.eval env₂ term := by

  cases Env.ext env₁ env₂ hBound hFree
  rfl
theorem Formula.satisfies_iff_of_env_eq {M : Model} (env₁ env₂ : Env M) (hBound : ∀ index, env₁.boundVal index =
    env₂.boundVal index) (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id) (formula : Formula) :
    Formula.Satisfies env₁ formula ↔ Formula.Satisfies env₂ formula := by

  cases Env.ext env₁ env₂ hBound hFree
  rfl
theorem Term.evalList_eq_of_env_eq {M : Model} (env₁ env₂ : Env M) (hBound : ∀ index, env₁.boundVal index =
    env₂.boundVal index) (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id) (terms : List Term) :
    terms.map (Term.eval env₁) = terms.map (Term.eval env₂) := by

  cases Env.ext env₁ env₂ hBound hFree
  rfl

mutual
  theorem Term.eval_shiftAbove {M : Model} (env : Env M) (amount cutoff : Nat) (term : Term) : Term.eval env (Term.shiftAbove amount cutoff term) = Term.eval (env.skip amount cutoff) term := by

    cases term <;> simp only [Term.shiftAbove, Term.eval]
    case bvar sort index =>
      by_cases hIndex : index < cutoff <;> simp [Term.eval, Env.skip, hIndex]
    all_goals first | rfl | simp only [Term.eval_shiftAbove, Term.evalList_shiftAbove,
      ← Formula.Satisfies.eq_def, Formula.satisfies_shiftAbove, Env.skip_push]
  theorem Formula.satisfies_shiftAbove {M : Model} (env : Env M) (amount cutoff : Nat) (formula : Formula) : Formula.Satisfies env (Formula.shiftAbove amount cutoff formula) ↔ Formula.Satisfies (env.skip amount cutoff) formula := by

    cases formula <;> simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
    all_goals simp only [← Formula.Satisfies.eq_def, Term.eval_shiftAbove, Term.evalList_shiftAbove,
      Formula.satisfies_shiftAbove, Env.skip_push]
  theorem Term.evalList_shiftAbove {M : Model} (env : Env M) (amount cutoff : Nat) (terms : List Term) : (Term.shiftListAbove amount cutoff terms).map (Term.eval env) = terms.map (Term.eval (env.skip amount cutoff)) := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp only [Term.shiftListAbove, List.map_cons]
        rw [Term.eval_shiftAbove env amount cutoff head, Term.evalList_shiftAbove env amount cutoff tail]
end
mutual
  theorem Term.eval_instantiateAt {M : Model} (env : Env M) (depth : Nat) (replacement term : Term) : Term.eval env (Term.instantiateAt depth replacement term) = Term.eval (env.insertAt depth (Term.eval (env.drop depth) replacement)) term := by

    cases term <;> simp only [Term.instantiateAt, Term.eval]
    case bvar sort index =>
      by_cases hLt : index < depth
      · simp [Term.eval, Env.insertAt, hLt]
      · by_cases hEq : index = depth
        · subst index
          simp [Term.shift, Env.insertAt, Term.eval_shiftAbove, Env.skip, Env.drop]
        · simp [Term.eval, Env.insertAt, hLt, hEq]
    all_goals first | rfl | simp only [Term.eval_instantiateAt, Term.evalList_instantiateAt,
      ← Formula.Satisfies.eq_def, Formula.satisfies_instantiateAt, Env.drop_push, Env.insertAt_push]
  theorem Formula.satisfies_instantiateAt {M : Model} (env : Env M) (depth : Nat) (replacement : Term) (formula : Formula) : Formula.Satisfies env (Formula.instantiateAt depth replacement formula) ↔ Formula.Satisfies (env.insertAt depth (Term.eval (env.drop depth) replacement)) formula := by

    cases formula <;> simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
    all_goals simp only [← Formula.Satisfies.eq_def, Term.eval_instantiateAt, Term.evalList_instantiateAt,
      Formula.satisfies_instantiateAt, Env.drop_push, Env.insertAt_push]
  theorem Term.evalList_instantiateAt {M : Model} (env : Env M) (depth : Nat) (replacement : Term) (terms : List Term) : (Term.instantiateListAt depth replacement terms).map (Term.eval env) = terms.map (Term.eval (env.insertAt depth (Term.eval (env.drop depth) replacement))) := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp only [Term.instantiateListAt, List.map_cons]
        rw [Term.eval_instantiateAt env depth replacement head, Term.evalList_instantiateAt env depth replacement tail]
end
namespace Atom
def Satisfies {M : Model} (env : Env M) : Atom → Prop
  | Atom.predicate predicate args => M.predicateInterp predicate (args.map (Term.eval env))
  | Atom.equal _ left right => Term.eval env left = Term.eval env right
  | Atom.boolTerm term => M.boolHolds (Term.eval env term)
end Atom
namespace Literal
def Satisfies {M : Model} (env : Env M) (literal : Literal) : Prop :=
  if literal.positive then
    Atom.Satisfies env literal.atom
  else
    ¬ Atom.Satisfies env literal.atom
end Literal
namespace Nnf
def Satisfies {M : Model} (env : Env M) : Nnf → Prop
  | Nnf.trueE => True
  | Nnf.falseE => False
  | Nnf.lit literal => Literal.Satisfies env literal
  | Nnf.conj left right => Satisfies env left ∧ Satisfies env right
  | Nnf.disj left right => Satisfies env left ∨ Satisfies env right
  | Nnf.forallE sort body => ∀ value, M.sortInterp sort value → Satisfies (env.push value) body
  | Nnf.existsE sort body => ∃ value, M.sortInterp sort value ∧ Satisfies (env.push value) body
def Satisfiable (nnf : Nnf) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env nnf
def Unsatisfiable (nnf : Nnf) : Prop :=
  ¬ Satisfiable.{x} nnf
theorem satisfies_toFormula {M : Model} (env : Env M) (nnf : Nnf) : Formula.Satisfies env nnf.toFormula ↔ Satisfies env nnf := by

  induction nnf generalizing env <;>
    simp_all only [Nnf.toFormula, Formula.Satisfies.eq_def, Formula.eval, Nnf.Satisfies]
  case lit literal =>
    cases literal with
    | mk positive atom =>
        cases positive <;> cases atom <;>
          simp [Literal.toFormula, Atom.toFormula, Literal.Satisfies,
            Atom.Satisfies, Formula.eval]

def Equivalent (left right : Nnf) : Prop :=
  ∀ {M : Model.{x}} (env : Env M), Satisfies env left ↔ Satisfies env right
end Nnf
namespace Clause
def Satisfies {M : Model} (env : Env M) (clause : Clause) : Prop :=
  ∃ literal ∈ clause.toList, Literal.Satisfies env literal
end Clause
namespace ClauseSet
def Satisfies {M : Model} (env : Env M) (clauses : ClauseSet) : Prop :=
  ∀ clause ∈ clauses.toList, Clause.Satisfies env clause
def Satisfiable (clauses : ClauseSet) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env clauses
end ClauseSet
end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
