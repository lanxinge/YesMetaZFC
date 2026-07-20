import YesMetaZFC.SetTheory.Model

/-!
# 定义原子核的纯隶属审计语言

本模块保存旧纯 `∈` 核的最小独立副本，只供 `Definitional.Audit` 的展开与保守性证明
使用。生产定理与自动化不应导入本模块，也不在 `SetTheory` 根命名空间恢复旧接口。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Audit
namespace Pure

universe u

/-- 深度为 `depth` 的纯集合论项。 -/
inductive Term (depth : Nat) where
  | bound : Fin depth → Term depth
  | free : FreeVarId → Term depth
  deriving Repr

namespace Term

/-- 按 substitution 替换 bound 变量。 -/
def bind {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth) :
    Term sourceDepth → Term targetDepth
  | .bound entry => substitution entry
  | .free id => .free id

/-- 在上下文顶部加入一个新 binder。 -/
def weaken {depth : Nat} (term : Term depth) : Term (depth + 1) :=
  term.bind (.bound ∘ Fin.succ)

/-- 当前上下文顶部最新引入的 bound 变量。 -/
def newest {depth : Nat} : Term (depth + 1) :=
  .bound 0

/-- substitution 穿过一个 binder 时的 lifting。 -/
def liftSubstitution {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth) :
    Fin (sourceDepth + 1) → Term (targetDepth + 1) :=
  Fin.cases newest fun entry => (substitution entry).weaken

/-- 项中出现的自由变量编号。 -/
def freeSupport {depth : Nat} : Term depth → List FreeVarId
  | .bound _ => []
  | .free id => [id]

@[simp] theorem freeSupport_bound {depth : Nat} (entry : Fin depth) :
    (Term.bound entry).freeSupport = [] :=
  rfl

@[simp] theorem freeSupport_free {depth : Nat} (id : FreeVarId) :
    (Term.free id : Term depth).freeSupport = [id] :=
  rfl

@[simp] theorem freeSupport_weaken {depth : Nat} (term : Term depth) :
    term.weaken.freeSupport = term.freeSupport := by
  cases term <;> rfl

/-- 不引入自由变量的 substitution 保持项的自由变量支持。 -/
theorem freeSupport_bind_of_closed {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = [])
    (term : Term sourceDepth) :
    (term.bind substitution).freeSupport = term.freeSupport := by
  cases term with
  | bound entry =>
      exact hClosed entry
  | free =>
      rfl

/-- lifting 保持“不引入自由变量”合同。 -/
theorem liftSubstitution_closed {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = []) :
    ∀ entry, (liftSubstitution substitution entry).freeSupport = [] := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · rfl
  · simpa [liftSubstitution] using hClosed previous

/-- 纯集合论项的解释。 -/
def eval {ℳ : SetTheory.Structure.{u}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) : Term depth → ℳ.Domain
  | .bound entry => env.bound entry
  | .free id => env.free id

@[simp] theorem eval_weaken {ℳ : SetTheory.Structure.{u}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (value : ℳ.Domain) (term : Term depth) :
    eval (env.push value) term.weaken = eval env term := by
  cases term <;> rfl

end Term

/-- 深度为 `depth`、只含隶属原子的纯集合论公式。 -/
inductive Formula : Nat → Type where
  | falsum {depth : Nat} : Formula depth
  | truth {depth : Nat} : Formula depth
  | mem {depth : Nat} : Term depth → Term depth → Formula depth
  | neg {depth : Nat} : Formula depth → Formula depth
  | conj {depth : Nat} : Formula depth → Formula depth → Formula depth
  | disj {depth : Nat} : Formula depth → Formula depth → Formula depth
  | imp {depth : Nat} : Formula depth → Formula depth → Formula depth
  | iff {depth : Nat} : Formula depth → Formula depth → Formula depth
  | forallE {depth : Nat} : Formula (depth + 1) → Formula depth
  | existsE {depth : Nat} : Formula (depth + 1) → Formula depth
  deriving Repr

namespace Formula

/-- 按 substitution 替换公式中的 bound 变量。 -/
def bind {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth) :
    Formula sourceDepth → Formula targetDepth
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right => .mem (left.bind substitution) (right.bind substitution)
  | .neg formula => .neg (bind substitution formula)
  | .conj left right => .conj (bind substitution left) (bind substitution right)
  | .disj left right => .disj (bind substitution left) (bind substitution right)
  | .imp left right => .imp (bind substitution left) (bind substitution right)
  | .iff left right => .iff (bind substitution left) (bind substitution right)
  | .forallE body => .forallE (bind (Term.liftSubstitution substitution) body)
  | .existsE body => .existsE (bind (Term.liftSubstitution substitution) body)

/-- 公式中出现的自由变量编号。 -/
def freeSupport {depth : Nat} : Formula depth → List FreeVarId
  | .falsum => []
  | .truth => []
  | .mem left right => left.freeSupport ++ right.freeSupport
  | .neg formula => formula.freeSupport
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      left.freeSupport ++ right.freeSupport
  | .forallE body
  | .existsE body =>
      body.freeSupport

/-- 公式没有自由变量。 -/
abbrev FreeClosed {depth : Nat} (formula : Formula depth) : Prop :=
  formula.freeSupport = []

/-- 不引入自由变量的 substitution 保持公式的自由变量支持。 -/
theorem freeSupport_bind_of_closed {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = [])
    (formula : Formula sourceDepth) :
    (formula.bind substitution).freeSupport = formula.freeSupport := by
  induction formula generalizing targetDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | mem left right =>
      simp [bind, freeSupport,
        Term.freeSupport_bind_of_closed substitution hClosed]
  | neg formula ih =>
      simp [bind, freeSupport, ih substitution hClosed]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [bind, freeSupport, ihLeft substitution hClosed,
        ihRight substitution hClosed]
  | forallE body ih
  | existsE body ih =>
      simpa [bind, freeSupport] using
        ih (Term.liftSubstitution substitution)
          (Term.liftSubstitution_closed substitution hClosed)

end Formula

namespace Env

/-- 沿纯项 substitution 拉回共享环境。 -/
def substitute {ℳ : SetTheory.Structure.{u}}
    {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth) :
    SetTheory.Env ℳ sourceDepth where
  bound := fun entry => Term.eval env (substitution entry)
  free := env.free

end Env

namespace Formula

private theorem substitute_liftSubstitution {ℳ : SetTheory.Structure.{u}}
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

/-- 纯集合论公式的 Tarski 满足关系。 -/
def satisfies {ℳ : SetTheory.Structure.{u}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) : Formula depth → Prop
  | .falsum => False
  | .truth => True
  | .mem left right => ℳ.mem (left.eval env) (right.eval env)
  | .neg formula => ¬ satisfies env formula
  | .conj left right => satisfies env left ∧ satisfies env right
  | .disj left right => satisfies env left ∨ satisfies env right
  | .imp left right => satisfies env left → satisfies env right
  | .iff left right => satisfies env left ↔ satisfies env right
  | .forallE body => ∀ value, satisfies (env.push value) body
  | .existsE body => ∃ value, satisfies (env.push value) body

/-- substitution 后满足公式等价于沿 substitution 拉回环境。 -/
@[simp] theorem satisfies_bind {ℳ : SetTheory.Structure.{u}}
    {sourceDepth targetDepth : Nat}
    (env : SetTheory.Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth) :
    ∀ formula : Formula sourceDepth,
      satisfies env (formula.bind substitution) ↔
        satisfies (Env.substitute env substitution) formula
  | .falsum => Iff.rfl
  | .truth => Iff.rfl
  | .mem left right => by
      cases left <;> cases right <;> rfl
  | .neg formula => by
      simpa [bind, satisfies] using
        not_congr (satisfies_bind env substitution formula)
  | .conj left right => by
      simpa [bind, satisfies] using
        and_congr
          (satisfies_bind env substitution left)
          (satisfies_bind env substitution right)
  | .disj left right => by
      simpa [bind, satisfies] using
        or_congr
          (satisfies_bind env substitution left)
          (satisfies_bind env substitution right)
  | .imp left right => by
      simpa [bind, satisfies] using
        imp_congr
          (satisfies_bind env substitution left)
          (satisfies_bind env substitution right)
  | .iff left right => by
      simpa [bind, satisfies] using
        iff_congr
          (satisfies_bind env substitution left)
          (satisfies_bind env substitution right)
  | .forallE body => by
      simp only [bind, satisfies]
      constructor
      · intro h value
        have hBody :=
          (satisfies_bind (env.push value)
            (Term.liftSubstitution substitution) body).mp (h value)
        simpa only [substitute_liftSubstitution] using hBody
      · intro h value
        apply
          (satisfies_bind (env.push value)
            (Term.liftSubstitution substitution) body).mpr
        simpa only [substitute_liftSubstitution] using h value
  | .existsE body => by
      simp only [bind, satisfies]
      constructor
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        have hBody' :=
          (satisfies_bind (env.push value)
            (Term.liftSubstitution substitution) body).mp hBody
        simpa only [substitute_liftSubstitution] using hBody'
      · rintro ⟨value, hBody⟩
        refine ⟨value, ?_⟩
        apply
          (satisfies_bind (env.push value)
            (Term.liftSubstitution substitution) body).mpr
        simpa only [substitute_liftSubstitution] using hBody

end Formula

/-- Jech 意义下的纯集合论句子。 -/
structure Sentence where
  formula : Formula 0
  freeClosed : formula.FreeClosed

/-- 纯集合论理论是纯句子的谓词。 -/
abbrev Theory := Sentence → Prop

namespace Structure

/-- 一个结构满足纯句子。 -/
def SatisfiesSentence (ℳ : SetTheory.Structure.{u})
    (sentence : Sentence) : Prop :=
  ∀ free : FreeVarId → ℳ.Domain,
    Formula.satisfies {
      bound := Fin.elim0
      free := free
    } sentence.formula

/-- 一个外延结构满足纯理论中的全部句子。 -/
def Models (ℳ : SetTheory.Structure.{u}) (theory : Theory) : Prop :=
  SetTheory.Extensional ℳ ∧
    ∀ sentence, theory sentence → SatisfiesSentence ℳ sentence

end Structure

/-- 固定模型 universe 的纯集合论语义蕴涵。 -/
def SemanticallyEntails (theory : Theory) (target : Sentence) : Prop :=
  ∀ ℳ : SetTheory.Structure.{u},
    Structure.Models ℳ theory →
      Structure.SatisfiesSentence ℳ target

end Pure
end Audit
end Definitional
end SetTheory
end YesMetaZFC
