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

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

universe x

/-- 让 Prop-valued 公式解释与任意 universe 的项 carrier 处在同一互递归层级。 -/
structure Truth (_carrier : Type x) : Type x where
  holds : Prop

/-- `CoreSyntax` 的单域多 sort 模型。 -/
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

/-- locally nameless 变量环境。 -/
structure Env (M : Model) where
  boundVal : Nat → M.Carrier
  freeVal : CoreSort → VarId → M.Carrier

namespace Env

/-- 在 bound stack 顶部压入一个值。 -/
def push {M : Model} (env : Env M) (value : M.Carrier) : Env M where
  boundVal := fun index =>
    match index with
    | 0 => value
    | previous + 1 => env.boundVal previous
  freeVal := env.freeVal

/-- 删除 bound stack 的前 `amount` 个值。 -/
def drop {M : Model} (amount : Nat) (env : Env M) : Env M where
  boundVal := fun index => env.boundVal (index + amount)
  freeVal := env.freeVal

/-- 解释经过 `shiftAbove amount cutoff` 的语法时跳过环境中的同一段。 -/
def skip {M : Model} (amount cutoff : Nat) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < cutoff then env.boundVal index else env.boundVal (index + amount)
  freeVal := env.freeVal

/-- 在 bound stack 的指定深度插入一个值。 -/
def insertAt {M : Model} (depth : Nat) (value : M.Carrier) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < depth then
      env.boundVal index
    else if index = depth then
      value
    else
      env.boundVal (index - 1)
  freeVal := env.freeVal

/-- 修改一个 typed free variable 的值。 -/
def setFree {M : Model} (env : Env M) (sort : CoreSort) (id : VarId)
    (value : M.Carrier) : Env M where
  boundVal := env.boundVal
  freeVal := fun targetSort targetId =>
    if targetSort = sort ∧ targetId = id then value else env.freeVal targetSort targetId

@[simp]
theorem push_bound_zero {M : Model} (env : Env M) (value : M.Carrier) :
    (env.push value).boundVal 0 = value :=
  rfl

@[simp]
theorem push_bound_succ {M : Model} (env : Env M) (value : M.Carrier) (index : Nat) :
    (env.push value).boundVal (index + 1) = env.boundVal index :=
  rfl

@[simp]
theorem push_free {M : Model} (env : Env M) (value : M.Carrier)
    (sort : CoreSort) (id : VarId) :
    (env.push value).freeVal sort id = env.freeVal sort id :=
  rfl

@[simp]
theorem drop_bound {M : Model} (amount : Nat) (env : Env M) (index : Nat) :
    (env.drop amount).boundVal index = env.boundVal (index + amount) :=
  rfl

@[simp]
theorem drop_free {M : Model} (amount : Nat) (env : Env M)
    (sort : CoreSort) (id : VarId) :
    (env.drop amount).freeVal sort id = env.freeVal sort id :=
  rfl

@[simp]
theorem skip_free {M : Model} (amount cutoff : Nat) (env : Env M)
    (sort : CoreSort) (id : VarId) :
    (env.skip amount cutoff).freeVal sort id = env.freeVal sort id :=
  rfl

theorem skip_zero_bound {M : Model} (amount : Nat) (env : Env M) (index : Nat) :
    (env.skip amount 0).boundVal index = (env.drop amount).boundVal index := by
  simp [skip, drop]

theorem skip_push_bound {M : Model} (amount cutoff : Nat) (env : Env M)
    (value : M.Carrier) (index : Nat) :
    ((env.push value).skip amount (cutoff + 1)).boundVal index =
      ((env.skip amount cutoff).push value).boundVal index := by
  cases index with
  | zero =>
      rfl
  | succ previous =>
      simp only [push_bound_succ]
      simp [skip, Nat.succ_lt_succ_iff, Nat.succ_add]

theorem drop_push_bound {M : Model} (amount : Nat) (env : Env M)
    (value : M.Carrier) (index : Nat) :
    ((env.push value).drop (amount + 1)).boundVal index =
      (env.drop amount).boundVal index := by
  have hIndex : index + (amount + 1) = (index + amount) + 1 := by omega
  simp only [drop_bound, hIndex, push_bound_succ]

theorem insertAt_push_bound {M : Model} (depth : Nat) (env : Env M)
    (inserted value : M.Carrier) (index : Nat) :
    ((env.push value).insertAt (depth + 1) inserted).boundVal index =
      ((env.insertAt depth inserted).push value).boundVal index := by
  cases index with
  | zero =>
      rfl
  | succ previous =>
      simp only [push_bound_succ]
      by_cases hLt : previous < depth
      · simp [insertAt, Nat.succ_lt_succ_iff, hLt]
      · by_cases hEq : previous = depth
        · simp [insertAt, hEq]
        · have hPositive : 0 < previous := by omega
          cases previous with
          | zero =>
              omega
          | succ index =>
              simp [insertAt, Nat.succ_lt_succ_iff, hLt, hEq]

end Env

mutual
  /-- 核心项解释。 -/
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
    | Term.lam domain codomain body =>
        M.lambdaValue domain codomain (fun value => Term.eval (env.push value) body)
    | Term.ite _ condition thenTerm elseTerm =>
        M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm)
          (Term.eval env elseTerm)

  /-- 核心公式的互递归内部解释。公开接口见 `Formula.Satisfies`。 -/
  def Formula.eval {M : Model} (env : Env M) : Formula → Truth M.Carrier
    | Formula.trueE => ⟨True⟩
    | Formula.falseE => ⟨False⟩
    | Formula.atom predicate args =>
        ⟨M.predicateInterp predicate (args.map (Term.eval env))⟩
    | Formula.equal _ left right => ⟨Term.eval env left = Term.eval env right⟩
    | Formula.boolTerm term => ⟨M.boolHolds (Term.eval env term)⟩
    | Formula.neg body => ⟨¬ (Formula.eval env body).holds⟩
    | Formula.imp left right =>
        ⟨(Formula.eval env left).holds → (Formula.eval env right).holds⟩
    | Formula.conj left right =>
        ⟨(Formula.eval env left).holds ∧ (Formula.eval env right).holds⟩
    | Formula.disj left right =>
        ⟨(Formula.eval env left).holds ∨ (Formula.eval env right).holds⟩
    | Formula.iffE left right =>
        ⟨(Formula.eval env left).holds ↔ (Formula.eval env right).holds⟩
    | Formula.forallE sort body =>
        ⟨∀ value, M.sortInterp sort value → (Formula.eval (env.push value) body).holds⟩
    | Formula.existsE sort body =>
        ⟨∃ value, M.sortInterp sort value ∧ (Formula.eval (env.push value) body).holds⟩
end

namespace Formula

/-- 核心公式满足关系。 -/
def Satisfies {M : Model} (env : Env M) (formula : Formula) : Prop :=
  (Formula.eval env formula).holds

/-- 核心公式的可满足性。 -/
def Satisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env formula

/-- 核心公式的不可满足性。 -/
def Unsatisfiable (formula : Formula) : Prop :=
  ¬ Satisfiable.{x} formula

end Formula

mutual
  /-- 项解释只依赖环境的逐点取值。 -/
  theorem Term.eval_eq_of_env_eq {M : Model} (env₁ env₂ : Env M)
      (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
      (term : Term) : Term.eval env₁ term = Term.eval env₂ term := by
    cases term with
    | bvar _ index =>
        simpa only [Term.eval] using hBound index
    | fvar sort id =>
        simpa only [Term.eval] using hFree sort id
    | app symbol args =>
        simp only [Term.eval]
        congr 1
        exact Term.evalList_eq_of_env_eq env₁ env₂ hBound hFree args
    | apply fn arg =>
        simp only [Term.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree fn,
          Term.eval_eq_of_env_eq env₁ env₂ hBound hFree arg]
    | bool _ =>
        simp only [Term.eval]
    | notE body =>
        simp only [Term.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree body]
    | andE left right
    | orE left right
    | impE left right
    | iffE left right =>
        simp only [Term.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree left,
          Term.eval_eq_of_env_eq env₁ env₂ hBound hFree right]
    | quote formula =>
        simp only [Term.eval]
        congr 1
        apply propext
        exact Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree formula
    | lam domain codomain body =>
        simp only [Term.eval]
        congr 1
        funext value
        apply Term.eval_eq_of_env_eq
        · intro index
          cases index <;> simp [Env.push, hBound]
        · intro sort id
          simp [Env.push, hFree]
    | ite _ condition thenTerm elseTerm =>
        simp only [Term.eval]
        congr 1
        · apply propext
          exact Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree condition
        · exact Term.eval_eq_of_env_eq env₁ env₂ hBound hFree thenTerm
        · exact Term.eval_eq_of_env_eq env₁ env₂ hBound hFree elseTerm

  /-- 公式满足关系只依赖环境的逐点取值。 -/
  theorem Formula.satisfies_iff_of_env_eq {M : Model} (env₁ env₂ : Env M)
      (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
      (formula : Formula) :
      Formula.Satisfies env₁ formula ↔ Formula.Satisfies env₂ formula := by
    cases formula with
    | trueE
    | falseE =>
        simp only [Formula.Satisfies, Formula.eval]
    | atom _ args =>
        simp only [Formula.Satisfies, Formula.eval]
        rw [Term.evalList_eq_of_env_eq env₁ env₂ hBound hFree args]
    | equal _ left right =>
        simp only [Formula.Satisfies, Formula.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree left,
          Term.eval_eq_of_env_eq env₁ env₂ hBound hFree right]
    | boolTerm term =>
        simp only [Formula.Satisfies, Formula.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree term]
    | neg body =>
        simp only [Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          not_congr (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree body)
    | imp left right =>
        simp only [Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          imp_congr
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree left)
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree right)
    | conj left right =>
        simp only [Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          and_congr
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree left)
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree right)
    | disj left right =>
        simp only [Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          or_congr
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree left)
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree right)
    | iffE left right =>
        simp only [Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          iff_congr
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree left)
            (Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree right)
    | forallE sort body =>
        simp only [Formula.Satisfies, Formula.eval]
        constructor <;> intro h value hSort
        · apply (Formula.satisfies_iff_of_env_eq (env₁.push value) (env₂.push value)
              (by
                intro index
                cases index <;> simp [Env.push, hBound])
              (by
                intro target id
                simp [Env.push, hFree]) body).mp
          exact h value hSort
        · apply (Formula.satisfies_iff_of_env_eq (env₁.push value) (env₂.push value)
              (by
                intro index
                cases index <;> simp [Env.push, hBound])
              (by
                intro target id
                simp [Env.push, hFree]) body).mpr
          exact h value hSort
    | existsE sort body =>
        simp only [Formula.Satisfies, Formula.eval]
        constructor
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          exact (Formula.satisfies_iff_of_env_eq (env₁.push value) (env₂.push value)
            (by
              intro index
              cases index <;> simp [Env.push, hBound])
            (by
              intro target id
              simp [Env.push, hFree]) body).mp hBody
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          exact (Formula.satisfies_iff_of_env_eq (env₁.push value) (env₂.push value)
            (by
              intro index
              cases index <;> simp [Env.push, hBound])
            (by
              intro target id
              simp [Env.push, hFree]) body).mpr hBody

  /-- 项列表解释只依赖环境的逐点取值。 -/
  theorem Term.evalList_eq_of_env_eq {M : Model} (env₁ env₂ : Env M)
      (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
      (terms : List Term) :
      terms.map (Term.eval env₁) = terms.map (Term.eval env₂) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [List.map_cons]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree head,
          Term.evalList_eq_of_env_eq env₁ env₂ hBound hFree tail]
end

mutual
  /-- `shiftAbove` 的项语义是跳过环境中的对应区段。 -/
  theorem Term.eval_shiftAbove {M : Model} (env : Env M) (amount cutoff : Nat)
      (term : Term) :
      Term.eval env (Term.shiftAbove amount cutoff term) =
        Term.eval (env.skip amount cutoff) term := by
    cases term with
    | bvar sort index =>
        by_cases hIndex : index < cutoff
        · simp [Term.shiftAbove, Term.eval, Env.skip, hIndex]
        · simp [Term.shiftAbove, Term.eval, Env.skip, hIndex]
    | fvar sort id =>
        simp [Term.shiftAbove, Term.eval, Env.skip]
    | app symbol args =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        exact Term.evalList_shiftAbove env amount cutoff args
    | apply fn arg =>
        simp [Term.shiftAbove, Term.eval, Term.eval_shiftAbove]
    | bool value =>
        simp [Term.shiftAbove, Term.eval]
    | notE body =>
        simp [Term.shiftAbove, Term.eval, Term.eval_shiftAbove]
    | andE left right
    | orE left right
    | impE left right
    | iffE left right =>
        simp [Term.shiftAbove, Term.eval, Term.eval_shiftAbove]
    | quote formula =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        apply propext
        exact Formula.satisfies_shiftAbove env amount cutoff formula
    | lam domain codomain body =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        funext value
        rw [Term.eval_shiftAbove]
        apply Term.eval_eq_of_env_eq
        · exact Env.skip_push_bound amount cutoff env value
        · intro sort id
          rfl
    | ite sort condition thenTerm elseTerm =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        · apply propext
          exact Formula.satisfies_shiftAbove env amount cutoff condition
        · exact Term.eval_shiftAbove env amount cutoff thenTerm
        · exact Term.eval_shiftAbove env amount cutoff elseTerm

  /-- `shiftAbove` 的公式语义是跳过环境中的对应区段。 -/
  theorem Formula.satisfies_shiftAbove {M : Model} (env : Env M)
      (amount cutoff : Nat) (formula : Formula) :
      Formula.Satisfies env (Formula.shiftAbove amount cutoff formula) ↔
        Formula.Satisfies (env.skip amount cutoff) formula := by
    cases formula with
    | trueE
    | falseE =>
        simp [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
    | atom predicate args =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        rw [Term.evalList_shiftAbove env amount cutoff args]
    | equal sort left right =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        rw [Term.eval_shiftAbove env amount cutoff left,
          Term.eval_shiftAbove env amount cutoff right]
    | boolTerm term =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        rw [Term.eval_shiftAbove env amount cutoff term]
    | neg body =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          not_congr (Formula.satisfies_shiftAbove env amount cutoff body)
    | imp left right =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          imp_congr
            (Formula.satisfies_shiftAbove env amount cutoff left)
            (Formula.satisfies_shiftAbove env amount cutoff right)
    | conj left right =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          and_congr
            (Formula.satisfies_shiftAbove env amount cutoff left)
            (Formula.satisfies_shiftAbove env amount cutoff right)
    | disj left right =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          or_congr
            (Formula.satisfies_shiftAbove env amount cutoff left)
            (Formula.satisfies_shiftAbove env amount cutoff right)
    | iffE left right =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          iff_congr
            (Formula.satisfies_shiftAbove env amount cutoff left)
            (Formula.satisfies_shiftAbove env amount cutoff right)
    | forallE sort body =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        constructor <;> intro h value hSort
        · apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).skip amount (cutoff + 1))
              ((env.skip amount cutoff).push value)
              (Env.skip_push_bound amount cutoff env value)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_shiftAbove (env.push value) amount (cutoff + 1) body).mp
            (h value hSort)
        · apply (Formula.satisfies_shiftAbove (env.push value) amount (cutoff + 1) body).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).skip amount (cutoff + 1))
              ((env.skip amount cutoff).push value)
              (Env.skip_push_bound amount cutoff env value)
              (by intro target id; rfl) body).mpr
          exact h value hSort
    | existsE sort body =>
        simp only [Formula.shiftAbove, Formula.Satisfies, Formula.eval]
        constructor
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).skip amount (cutoff + 1))
              ((env.skip amount cutoff).push value)
              (Env.skip_push_bound amount cutoff env value)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_shiftAbove (env.push value) amount (cutoff + 1) body).mp
            hBody
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_shiftAbove (env.push value) amount (cutoff + 1) body).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).skip amount (cutoff + 1))
              ((env.skip amount cutoff).push value)
              (Env.skip_push_bound amount cutoff env value)
              (by intro target id; rfl) body).mpr
          exact hBody

  /-- `shiftAbove` 对项列表的语义。 -/
  theorem Term.evalList_shiftAbove {M : Model} (env : Env M) (amount cutoff : Nat)
      (terms : List Term) :
      (Term.shiftListAbove amount cutoff terms).map (Term.eval env) =
        terms.map (Term.eval (env.skip amount cutoff)) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Term.shiftListAbove, List.map_cons]
        rw [Term.eval_shiftAbove env amount cutoff head,
          Term.evalList_shiftAbove env amount cutoff tail]
end

mutual
  /-- locally nameless 实例化的项语义。 -/
  theorem Term.eval_instantiateAt {M : Model} (env : Env M) (depth : Nat)
      (replacement term : Term) :
      Term.eval env (Term.instantiateAt depth replacement term) =
        Term.eval
          (env.insertAt depth (Term.eval (env.drop depth) replacement)) term := by
    cases term with
    | bvar sort index =>
        by_cases hLt : index < depth
        · simp [Term.instantiateAt, Term.eval, Env.insertAt, hLt]
        · by_cases hEq : index = depth
          · subst index
            calc
              Term.eval env
                  (Term.instantiateAt depth replacement (Term.bvar sort depth)) =
                  Term.eval env (Term.shiftAbove depth 0 replacement) := by
                    simp [Term.instantiateAt, Term.shift]
              _ = Term.eval (env.skip depth 0) replacement :=
                Term.eval_shiftAbove env depth 0 replacement
              _ = Term.eval (env.drop depth) replacement := by
                apply Term.eval_eq_of_env_eq
                · exact Env.skip_zero_bound depth env
                · intro target id
                  rfl
              _ = Term.eval
                  (env.insertAt depth (Term.eval (env.drop depth) replacement))
                  (Term.bvar sort depth) := by
                    simp [Term.eval, Env.insertAt]
          · have hGt : depth < index := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hLt) (Ne.symm hEq)
            simp [Term.instantiateAt, Term.eval, Env.insertAt, hLt, hEq]
    | fvar sort id =>
        simp [Term.instantiateAt, Term.eval, Env.insertAt]
    | app symbol args =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        exact Term.evalList_instantiateAt env depth replacement args
    | apply fn arg =>
        simp [Term.instantiateAt, Term.eval, Term.eval_instantiateAt]
    | bool value =>
        simp [Term.instantiateAt, Term.eval]
    | notE body =>
        simp [Term.instantiateAt, Term.eval, Term.eval_instantiateAt]
    | andE left right
    | orE left right
    | impE left right
    | iffE left right =>
        simp [Term.instantiateAt, Term.eval, Term.eval_instantiateAt]
    | quote formula =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        apply propext
        exact Formula.satisfies_instantiateAt env depth replacement formula
    | lam domain codomain body =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        funext value
        rw [Term.eval_instantiateAt]
        apply Term.eval_eq_of_env_eq
        · intro index
          rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
            (env.drop depth) (Env.drop_push_bound depth env value)
            (by intro target id; rfl) replacement]
          exact Env.insertAt_push_bound depth env _ value index
        · intro target id
          rfl
    | ite sort condition thenTerm elseTerm =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        · apply propext
          exact Formula.satisfies_instantiateAt env depth replacement condition
        · exact Term.eval_instantiateAt env depth replacement thenTerm
        · exact Term.eval_instantiateAt env depth replacement elseTerm

  /-- locally nameless 实例化的公式语义。 -/
  theorem Formula.satisfies_instantiateAt {M : Model} (env : Env M) (depth : Nat)
      (replacement : Term) (formula : Formula) :
      Formula.Satisfies env (Formula.instantiateAt depth replacement formula) ↔
        Formula.Satisfies
          (env.insertAt depth (Term.eval (env.drop depth) replacement)) formula := by
    cases formula with
    | trueE
    | falseE =>
        simp [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
    | atom predicate args =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        rw [Term.evalList_instantiateAt env depth replacement args]
    | equal sort left right =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        rw [Term.eval_instantiateAt env depth replacement left,
          Term.eval_instantiateAt env depth replacement right]
    | boolTerm term =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        rw [Term.eval_instantiateAt env depth replacement term]
    | neg body =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          not_congr (Formula.satisfies_instantiateAt env depth replacement body)
    | imp left right =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          imp_congr
            (Formula.satisfies_instantiateAt env depth replacement left)
            (Formula.satisfies_instantiateAt env depth replacement right)
    | conj left right =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          and_congr
            (Formula.satisfies_instantiateAt env depth replacement left)
            (Formula.satisfies_instantiateAt env depth replacement right)
    | disj left right =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          or_congr
            (Formula.satisfies_instantiateAt env depth replacement left)
            (Formula.satisfies_instantiateAt env depth replacement right)
    | iffE left right =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          iff_congr
            (Formula.satisfies_instantiateAt env depth replacement left)
            (Formula.satisfies_instantiateAt env depth replacement right)
    | forallE sort body =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        constructor <;> intro h value hSort
        · apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1)
                (Term.eval ((env.push value).drop (depth + 1)) replacement))
              ((env.insertAt depth (Term.eval (env.drop depth) replacement)).push value)
              (by
                intro index
                rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
                  (env.drop depth) (Env.drop_push_bound depth env value)
                  (by intro target id; rfl) replacement]
                exact Env.insertAt_push_bound depth env _ value index)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_instantiateAt (env.push value) (depth + 1)
            replacement body).mp (h value hSort)
        · apply (Formula.satisfies_instantiateAt (env.push value) (depth + 1)
            replacement body).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1)
                (Term.eval ((env.push value).drop (depth + 1)) replacement))
              ((env.insertAt depth (Term.eval (env.drop depth) replacement)).push value)
              (by
                intro index
                rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
                  (env.drop depth) (Env.drop_push_bound depth env value)
                  (by intro target id; rfl) replacement]
                exact Env.insertAt_push_bound depth env _ value index)
              (by intro target id; rfl) body).mpr
          exact h value hSort
    | existsE sort body =>
        simp only [Formula.instantiateAt, Formula.Satisfies, Formula.eval]
        constructor
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1)
                (Term.eval ((env.push value).drop (depth + 1)) replacement))
              ((env.insertAt depth (Term.eval (env.drop depth) replacement)).push value)
              (by
                intro index
                rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
                  (env.drop depth) (Env.drop_push_bound depth env value)
                  (by intro target id; rfl) replacement]
                exact Env.insertAt_push_bound depth env _ value index)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_instantiateAt (env.push value) (depth + 1)
            replacement body).mp hBody
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_instantiateAt (env.push value) (depth + 1)
            replacement body).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1)
                (Term.eval ((env.push value).drop (depth + 1)) replacement))
              ((env.insertAt depth (Term.eval (env.drop depth) replacement)).push value)
              (by
                intro index
                rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
                  (env.drop depth) (Env.drop_push_bound depth env value)
                  (by intro target id; rfl) replacement]
                exact Env.insertAt_push_bound depth env _ value index)
              (by intro target id; rfl) body).mpr
          exact hBody

  /-- locally nameless 实例化对项列表的语义。 -/
  theorem Term.evalList_instantiateAt {M : Model} (env : Env M) (depth : Nat)
      (replacement : Term) (terms : List Term) :
      (Term.instantiateListAt depth replacement terms).map (Term.eval env) =
        terms.map
          (Term.eval (env.insertAt depth (Term.eval (env.drop depth) replacement))) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Term.instantiateListAt, List.map_cons]
        rw [Term.eval_instantiateAt env depth replacement head,
          Term.evalList_instantiateAt env depth replacement tail]
end

namespace Atom

/-- NNF 原子的满足关系。 -/
def Satisfies {M : Model} (env : Env M) : Atom → Prop
  | Atom.predicate predicate args =>
      M.predicateInterp predicate (args.map (Term.eval env))
  | Atom.equal _ left right => Term.eval env left = Term.eval env right
  | Atom.boolTerm term => M.boolHolds (Term.eval env term)

end Atom

namespace Literal

/-- NNF 字面量的满足关系。 -/
def Satisfies {M : Model} (env : Env M) (literal : Literal) : Prop :=
  if literal.positive then
    Atom.Satisfies env literal.atom
  else
    ¬ Atom.Satisfies env literal.atom

end Literal

namespace Nnf

/-- NNF 的满足关系。 -/
def Satisfies {M : Model} (env : Env M) : Nnf → Prop
  | Nnf.trueE => True
  | Nnf.falseE => False
  | Nnf.lit literal => Literal.Satisfies env literal
  | Nnf.conj left right => Satisfies env left ∧ Satisfies env right
  | Nnf.disj left right => Satisfies env left ∨ Satisfies env right
  | Nnf.forallE sort body =>
      ∀ value, M.sortInterp sort value → Satisfies (env.push value) body
  | Nnf.existsE sort body =>
      ∃ value, M.sortInterp sort value ∧ Satisfies (env.push value) body

/-- 公开的 NNF 可满足性谓词，供各预处理阶段共同消费。 -/
def Satisfiable (nnf : Nnf) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env nnf

/-- NNF 不可满足性。 -/
def Unsatisfiable (nnf : Nnf) : Prop :=
  ¬ Satisfiable.{x} nnf

theorem satisfies_toFormula {M : Model} (env : Env M) (nnf : Nnf) :
    Formula.Satisfies env nnf.toFormula ↔ Satisfies env nnf := by
  induction nnf generalizing env with
  | trueE =>
      simp [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
  | falseE =>
      simp [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
  | lit literal =>
      cases literal with
      | mk positive atom =>
          cases positive <;> cases atom <;>
            simp [Nnf.toFormula, Literal.toFormula, Atom.toFormula, Literal.Satisfies,
              Atom.Satisfies, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
  | conj left right ihLeft ihRight =>
      simp only [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
      simpa only [Formula.Satisfies] using and_congr (ihLeft env) (ihRight env)
  | disj left right ihLeft ihRight =>
      simp only [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
      simpa only [Formula.Satisfies] using or_congr (ihLeft env) (ihRight env)
  | forallE sort body ih =>
      simp only [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
      constructor <;> intro h value hSort
      · exact (ih (env.push value)).mp (h value hSort)
      · exact (ih (env.push value)).mpr (h value hSort)
  | existsE sort body ih =>
      simp only [Nnf.toFormula, Formula.Satisfies, Formula.eval, Nnf.Satisfies]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        exact ⟨value, hSort, (ih (env.push value)).mp hBody⟩
      · rintro ⟨value, hSort, hBody⟩
        exact ⟨value, hSort, (ih (env.push value)).mpr hBody⟩

/-- 两个 NNF 在所有模型与环境下语义等价。 -/
def Equivalent (left right : Nnf) : Prop :=
  ∀ {M : Model.{x}} (env : Env M), Satisfies env left ↔ Satisfies env right

end Nnf

namespace Clause

/-- 字句满足关系：至少一个字面量成立。 -/
def Satisfies {M : Model} (env : Env M) (clause : Clause) : Prop :=
  ∃ literal ∈ clause.toList, Literal.Satisfies env literal

end Clause

namespace ClauseSet

/-- 字句集满足关系：所有字句都成立。 -/
def Satisfies {M : Model} (env : Env M) (clauses : ClauseSet) : Prop :=
  ∀ clause ∈ clauses.toList, Clause.Satisfies env clause

/-- 字句集可满足性。 -/
def Satisfiable (clauses : ClauseSet) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Satisfies env clauses

end ClauseSet

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
