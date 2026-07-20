import YesMetaZFC.SetTheory.Definitional.Language
import YesMetaZFC.SetTheory.Model

/-!
# 带定义原子的集合论语义

日常满足关系只调用原子的原生 `Interpretation`，不会递归进入定义体。`Kernel.atom_iff`
保存原生解释与分层定义体之间的一次性数学合同；完全展开到旧核只存在于 `Audit` 模块。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional

universe u v

namespace Env

/-- 沿新核项 substitution 拉回环境。 -/
def substitute {ℳ : SetTheory.Structure.{v}} {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth) :
    SetTheory.Env ℳ sourceDepth where
  bound := fun entry =>
    match substitution entry with
    | .bound target => env.bound target
    | .free id => env.free id
  free := env.free

end Env

namespace Term

/-- 新核集合论项的解释。 -/
def eval {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) : Term depth → ℳ.Domain
  | .bound entry => env.bound entry
  | .free id => env.free id

/-- bound-variable 重命名等价于环境反向重索引。 -/
@[simp] theorem eval_rename {ℳ : SetTheory.Structure.{v}}
    {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (term : Term sourceDepth) :
    eval env (term.rename indexMap) =
      eval (SetTheory.Env.reindex env indexMap) term := by
  cases term <;> rfl

/-- 当前环境栈顶最新 bound 变量的解释。 -/
@[simp] theorem eval_newest {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) :
    eval (env.push value) (newest : Term (depth + 1)) = value :=
  rfl

/-- weakening 不改变项的解释。 -/
@[simp] theorem eval_weaken {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) (term : Term depth) :
    eval (env.push value) term.weaken = eval env term := by
  cases term <;> rfl

/-- substitution 后解释项等价于沿 substitution 拉回环境。 -/
@[simp] theorem eval_bind {ℳ : SetTheory.Structure.{v}}
    {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth)
    (term : Term sourceDepth) :
    eval env (term.bind substitution) =
      eval (Env.substitute env substitution) term := by
  cases term <;> rfl

end Term

namespace TermVector

/-- 参数向量在当前环境中的取值。 -/
def eval {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) {count : Nat}
    (arguments : TermVector count depth) :
    Fin count → ℳ.Domain :=
  fun entry => Term.eval env (arguments entry)

/-- 项参数向量在当前环境中形成的 schema 参数环境。 -/
def evalEnv {ℳ : SetTheory.Structure.{v}} {count depth : Nat}
    (parameters : TermVector count depth)
    (env : SetTheory.Env ℳ depth) :
    SetTheory.Env ℳ count where
  bound := parameters.eval env
  free := env.free

/-- 参数向量穿过一个新 binder 后仍解释为原参数环境。 -/
@[simp, prove_auto_norm index]
theorem evalEnv_weaken {ℳ : SetTheory.Structure.{v}}
    {count depth : Nat} (parameters : TermVector count depth)
    (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) :
    parameters.weaken.evalEnv (env.push value) =
      parameters.evalEnv env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval]
  · rfl

/-- 单参数向量解释后的唯一 bound 参数就是原项的解释。 -/
@[simp, prove_auto_norm index]
theorem evalEnv_singleton_bound {ℳ : SetTheory.Structure.{v}}
    {depth : Nat} (term : Term depth) (env : SetTheory.Env ℳ depth) :
    ((singleton term).evalEnv env).bound 0 = term.eval env := by
  rfl

/-- 没有局部 binder 时，bound 参数向量直接解释为当前参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_zero {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount) :
    (boundParameters parameterCount 0).evalEnv env = env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

/-- 一个局部 binder 下，bound 参数向量仍解释为外层参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_one {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount)
    (first : ℳ.Domain) :
    (boundParameters parameterCount 1).evalEnv
        (env.push first) = env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

/-- 两个局部 binder 下，bound 参数向量仍解释为外层参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_two {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount)
    (first second : ℳ.Domain) :
    (boundParameters parameterCount 2).evalEnv
        ((env.push first).push second) = env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

/-- 三个局部 binder 下，bound 参数向量仍解释为外层参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_three {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount)
    (first second third : ℳ.Domain) :
    (boundParameters parameterCount 3).evalEnv
        (((env.push first).push second).push third) = env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

/-- 四个局部 binder 下，bound 参数向量仍解释为外层参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_four {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount)
    (first second third fourth : ℳ.Domain) :
    (boundParameters parameterCount 4).evalEnv
        ((((env.push first).push second).push third).push fourth) =
      env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

/-- 五个局部 binder 下，bound 参数向量仍解释为外层参数环境。 -/
@[prove_auto_norm index]
theorem evalEnv_boundParameters_five {ℳ : SetTheory.Structure.{v}}
    {parameterCount : Nat} (env : SetTheory.Env ℳ parameterCount)
    (first second third fourth fifth : ℳ.Domain) :
    (boundParameters parameterCount 5).evalEnv
        (((((env.push first).push second).push third).push fourth).push
          fifth) =
      env := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [evalEnv, eval, boundParameters, SetTheory.Env.push, Term.eval]
  · rfl

end TermVector

/--
定义原子的原生解释。

`atom` 可以直接使用 Lean 中已有的数学谓词；日常 `rfl` 和 `simp` 不需要进入公式定义体。
-/
structure Interpretation (σ : AtomSignature.{u}) where
  atom :
    {ℳ : SetTheory.Structure.{v}} →
      (symbol : σ.Symbol) →
      (Fin (σ.arity symbol) → ℳ.Domain) →
      (FreeVarId → ℳ.Domain) →
        Prop

namespace Semantics

/-- 原子参数在当前环境中的取值构成其定义体环境。 -/
def atomEnv {σ : AtomSignature.{u}} {ℳ : SetTheory.Structure.{v}}
    {depth : Nat} (env : SetTheory.Env ℳ depth)
    {symbol : σ.Symbol}
    (arguments : TermVector (σ.arity symbol) depth) :
    SetTheory.Env ℳ (σ.arity symbol) where
  bound := arguments.eval env
  free := env.free

/-- substitution 穿过 binder 时，新旧环境构造交换。 -/
private theorem substitute_liftSubstitution {ℳ : SetTheory.Structure.{v}}
    {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth) (value : ℳ.Domain)
    (substitution : Fin sourceDepth → Term targetDepth) :
    Env.substitute (env.push value) (Term.liftSubstitution substitution) =
      (Env.substitute env substitution).push value := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · change
        Term.eval (env.push value) (substitution previous).weaken =
          Term.eval env (substitution previous)
      exact Term.eval_weaken env value (substitution previous)
  · rfl

/-- substitution 与原子定义体环境构造交换。 -/
private theorem atomEnv_bind {σ : AtomSignature.{u}}
    {ℳ : SetTheory.Structure.{v}} {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth)
    {symbol : σ.Symbol}
    (arguments : TermVector (σ.arity symbol) sourceDepth) :
    atomEnv env (arguments.bind substitution) =
      atomEnv (Env.substitute env substitution) arguments := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [atomEnv, TermVector.eval, TermVector.bind, TermVector.get]
  · rfl

/-- 新核的原生满足关系；原子是不可见内部定义体的语义叶节点。 -/
def satisfies {σ : AtomSignature.{u}} (interpretation : Interpretation.{u, v} σ) :
    {ℳ : SetTheory.Structure.{v}} →
      {availableStage depth : Nat} →
        SetTheory.Env ℳ depth → Formula σ availableStage depth → Prop
  | _, _, _, _, .falsum => False
  | _, _, _, _, .truth => True
  | ℳ, _, _, env, .mem left right =>
      ℳ.mem (Term.eval env left) (Term.eval env right)
  | _, _, _, env, .atom symbol _ arguments =>
      interpretation.atom symbol (arguments.eval env) env.free
  | _, _, _, env, .neg formula =>
      ¬ satisfies interpretation env formula
  | _, _, _, env, .conj left right =>
      satisfies interpretation env left ∧ satisfies interpretation env right
  | _, _, _, env, .disj left right =>
      satisfies interpretation env left ∨ satisfies interpretation env right
  | _, _, _, env, .imp left right =>
      satisfies interpretation env left → satisfies interpretation env right
  | _, _, _, env, .iff left right =>
      satisfies interpretation env left ↔ satisfies interpretation env right
  | _, _, _, env, .forallE body =>
      ∀ value, satisfies interpretation (env.push value) body
  | _, _, _, env, .existsE body =>
      ∃ value, satisfies interpretation (env.push value) body

/-- 新核公式 substitution 等价于先拉回环境再解释原公式。 -/
@[simp] theorem satisfies_bind {σ : AtomSignature.{u}}
    (interpretation : Interpretation.{u, v} σ)
    {ℳ : SetTheory.Structure.{v}}
    {availableStage sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth) :
    ∀ formula : Formula σ availableStage sourceDepth,
      satisfies interpretation env (formula.bind substitution) ↔
        satisfies interpretation (Env.substitute env substitution) formula
  | .falsum => by
      simp [Formula.bind, satisfies]
  | .truth => by
      simp [Formula.bind, satisfies]
  | .mem left right => by
      simp only [Formula.bind, satisfies, Term.eval_bind]
  | .atom symbol hStage arguments => by
      simp only [Formula.bind, satisfies]
      change
        interpretation.atom symbol
            (atomEnv env (arguments.bind substitution)).bound
            (atomEnv env (arguments.bind substitution)).free ↔
          interpretation.atom symbol
            (atomEnv (Env.substitute env substitution) arguments).bound
            (atomEnv (Env.substitute env substitution) arguments).free
      rw [atomEnv_bind]
  | .neg formula => by
      simpa [Formula.bind, satisfies] using
        not_congr (satisfies_bind interpretation env substitution formula)
  | .conj left right => by
      simpa [Formula.bind, satisfies] using
        and_congr
          (satisfies_bind interpretation env substitution left)
          (satisfies_bind interpretation env substitution right)
  | .disj left right => by
      simpa [Formula.bind, satisfies] using
        or_congr
          (satisfies_bind interpretation env substitution left)
          (satisfies_bind interpretation env substitution right)
  | .imp left right => by
      simpa [Formula.bind, satisfies] using
        imp_congr
          (satisfies_bind interpretation env substitution left)
          (satisfies_bind interpretation env substitution right)
  | .iff left right => by
      simpa [Formula.bind, satisfies] using
        iff_congr
          (satisfies_bind interpretation env substitution left)
          (satisfies_bind interpretation env substitution right)
  | .forallE body => by
      simp only [Formula.bind, satisfies]
      constructor
      · intro h value
        have hBody :=
          (satisfies_bind interpretation (env.push value)
            (Term.liftSubstitution substitution) body).mp (h value)
        simpa only [substitute_liftSubstitution] using hBody
      · intro h value
        apply
          (satisfies_bind interpretation (env.push value)
            (Term.liftSubstitution substitution) body).mpr
        simpa only [substitute_liftSubstitution] using h value
  | .existsE body => by
      simp only [Formula.bind, satisfies]
      constructor
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        have hBody' :=
          (satisfies_bind interpretation (env.push value)
            (Term.liftSubstitution substitution) body).mp hBody
        simpa only [substitute_liftSubstitution] using hBody'
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        apply
          (satisfies_bind interpretation (env.push value)
            (Term.liftSubstitution substitution) body).mpr
        simpa only [substitute_liftSubstitution] using hBody

/-!
`rename` 只是把 bound 变量替换为目标环境中的对应位置，因此直接复用
`satisfies_bind`，不再按公式构造子复制一遍机械递归。
-/
@[simp] theorem satisfies_rename {σ : AtomSignature.{u}}
    (interpretation : Interpretation.{u, v} σ)
    {ℳ : SetTheory.Structure.{v}}
    {availableStage sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (formula : Formula σ availableStage sourceDepth) :
    satisfies interpretation env (formula.rename indexMap) ↔
      satisfies interpretation
        (SetTheory.Env.reindex env indexMap) formula := by
  rw [Formula.rename, satisfies_bind]
  rfl

/-- 全称闭合等价于任意 bound 参数赋值下满足原公式。 -/
theorem satisfies_forallClosure_iff {σ : AtomSignature.{u}}
    (interpretation : Interpretation.{u, v} σ)
    {ℳ : SetTheory.Structure.{v}} {availableStage depth : Nat}
    (free : FreeVarId → ℳ.Domain)
    (formula : Formula σ availableStage depth) :
    satisfies interpretation
        { bound := Fin.elim0, free := free }
        (Formula.forallClosure depth formula) ↔
      ∀ bound : Fin depth → ℳ.Domain,
        satisfies interpretation
          { bound := bound, free := free } formula := by
  induction depth with
  | zero =>
      constructor
      · intro h bound
        have hBound : bound = Fin.elim0 := by
          funext entry
          exact Fin.elim0 entry
        simpa [hBound] using h
      · intro h
        exact h Fin.elim0
  | succ depth ih =>
      rw [Formula.forallClosure]
      rw [ih (.forallE formula)]
      simp only [satisfies]
      constructor
      · intro h bound
        let tail : Fin depth → ℳ.Domain :=
          fun entry => bound entry.succ
        have hBody := h tail (bound 0)
        have hEnv :
            ({ bound := tail, free := free } :
                SetTheory.Env ℳ depth).push (bound 0) =
              ({ bound := bound, free := free } :
                SetTheory.Env ℳ (depth + 1)) := by
          rw [SetTheory.Env.mk.injEq]
          constructor
          · funext entry
            refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl
          · rfl
        simpa only [hEnv] using hBody
      · intro h bound value
        let extended : Fin (depth + 1) → ℳ.Domain :=
          Fin.cases value bound
        have hBody := h extended
        have hEnv :
            ({ bound := bound, free := free } :
                SetTheory.Env ℳ depth).push value =
              ({ bound := extended, free := free } :
                SetTheory.Env ℳ (depth + 1)) := by
          rfl
        simpa only [hEnv] using hBody

end Semantics

/--
定义原子核。

`atom_iff` 是原生原子解释与分层语法定义体之间的审计合同。日常语义只读取
`interpretation`，不会通过定义约化进入 `definitions.body`。
-/
structure Kernel (σ : AtomSignature.{u}) where
  definitions : Definitions σ
  interpretation : Interpretation.{u, v} σ
  atom_iff :
    ∀ {ℳ : SetTheory.Structure.{v}} (symbol : σ.Symbol)
      (_hExtensional : Extensional ℳ)
      (arguments : Fin (σ.arity symbol) → ℳ.Domain)
      (free : FreeVarId → ℳ.Domain),
      interpretation.atom symbol arguments free ↔
        Semantics.satisfies interpretation {
          bound := arguments
          free := free
        } (definitions.body symbol)

end Definitional
end SetTheory
end YesMetaZFC
