import YesMetaZFC.Model.Semantics.Algebra
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 标准 AST 与 Lean 语义的实际实例

语法代数的解释对象是原 AST，原生语义代数的解释对象是环境上的项值与谓词。
两者都不新建模型或选择对象；原生实例适用于任意原有多排序结构。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder
universe u v w x

namespace Ast
variable {σ : Signature.{u, v, w}}

/-- 同一异质骨架在语法参数列中的装配。 -/
def arguments {b f ss} : Values (Term σ b f) ss → Arguments σ b f ss
  | .nil => .nil
  | .cons t ts => .cons t (arguments ts)

/-- 当前 AST 的完整构造代数。它也可充当背景内部的符号表达式实例。 -/
abbrev algebra (σ : Signature.{u, v, w}) :
    Sem_algebra.{u, v, w, max u v w, max u v w} σ where
  Tm := Term σ
  Pr := Formula σ
  bvar := Term.bvar
  fvar := Term.fvar
  app a ts := .app a (arguments ts)
  rel r ts := .rel r (arguments ts)
  eq := Formula.equal
  bot := .falsum
  top := .truth
  neg := Formula.neg
  conj := Formula.conj
  disj := Formula.disj
  imp := Formula.imp
  iff := Formula.iff
  all := Formula.forallE
  ex := Formula.existsE

mutual
/-- 标准项嵌入语法背景后就是原项。 -/
@[simp] theorem tm_eq {b f s} (t : Term σ b f s) : (algebra σ).tm t = t := by
  cases t with
  | bvar i | fvar i => rfl
  | app a ts => exact congrArg (Term.app a) (args_eq ts)

/-- 参数列装配精确恢复原来的类型化 AST。 -/
@[simp] theorem args_eq {b f ss} (ts : Arguments σ b f ss) :
    arguments ((algebra σ).args ts) = ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      change Arguments.cons ((algebra σ).tm t) (arguments ((algebra σ).args ts)) = _
      rw [tm_eq, args_eq]
end

/-- 标准公式嵌入保持全部正文。 -/
@[simp] theorem fm_eq {b f} (φ : Formula σ b f) : (algebra σ).fm φ = φ := by
  induction φ <;> simp_all [Sem_algebra.fm]

end Ast

namespace Native
variable {σ : Signature.{u, v, w}}

/-- 默认背景：上下文中的映射是环境函数，量词遍历该结构的排序载体。 -/
abbrev algebra (ℳ : Structure.{u, v, w, x} σ) :
    Sem_algebra.{u, v, w, max u x, max u x} σ where
  Tm b f s := Env ℳ b f → ℳ.Carrier s
  Pr b f := Env ℳ b f → Prop
  bvar i ρ := ρ.boundVal i
  fvar i ρ := ρ.freeVal i
  app a ts ρ := ℳ.funcInterp a (ts.map (fun _ t => t ρ))
  rel r ts ρ := ℳ.relInterp r (ts.map (fun _ t => t ρ))
  eq t t' ρ := t ρ = t' ρ
  bot _ := False
  top _ := True
  neg p ρ := ¬ p ρ
  conj p q ρ := p ρ ∧ q ρ
  disj p q ρ := p ρ ∨ q ρ
  imp p q ρ := p ρ → q ρ
  iff p q ρ := p ρ ↔ q ρ
  all _ p ρ := ∀ a, p (ρ.pushBound a)
  ex _ p ρ := ∃ a, p (ρ.pushBound a)

variable (ℳ : Structure.{u, v, w, x} σ)

/-- 异质项值列逐点求值与 AST 装配交换。 -/
theorem arguments_eval {b f ss} (ts : Values (Term σ b f) ss) (ρ : Env ℳ b f) :
    (Ast.arguments ts).eval ρ = ts.map (fun _ t => t.eval ρ) := by
  induction ts with
  | nil => rfl
  | cons t ts h => exact congrArg (Values.cons (t.eval ρ)) h

/-- 标准语法到任意原生结构的实际解释映射。 -/
def interpretation : Sem_map (Ast.algebra σ) (algebra ℳ) where
  tm t ρ := t.eval ρ
  fm φ ρ := Formula.satisfies ρ φ
  bvar_eq _ := rfl
  fvar_eq _ := rfl
  app_eq a ts := by
    funext ρ
    change ℳ.funcInterp a ((Ast.arguments ts).eval ρ) = _
    rw [arguments_eval]
    change _ = ℳ.funcInterp a _
    rw [Values.map_comp]
  rel_eq r ts := by
    funext ρ
    change ℳ.relInterp r ((Ast.arguments ts).eval ρ) = _
    rw [arguments_eval]
    change _ = ℳ.relInterp r _
    rw [Values.map_comp]
  eq_eq _ _ := rfl
  bot_eq := rfl
  top_eq := rfl
  neg_eq _ := rfl
  conj_eq _ _ := rfl
  disj_eq _ _ := rfl
  imp_eq _ _ := rfl
  iff_eq _ _ := rfl
  all_eq _ _ := rfl
  ex_eq _ _ := rfl

/-- 默认项解释精确恢复既有求值。 -/
theorem tm_eq {b f s} (t : Term σ b f s) (ρ : Env ℳ b f) :
    (algebra ℳ).tm t ρ = t.eval ρ := by
  have h := (interpretation ℳ).toTm_map.tm_eval t
  rw [Ast.tm_eq] at h
  exact congrArg (fun t => t ρ) h.symm

/-- 默认公式解释逐公式恢复既有满足关系，包括全部量词。 -/
theorem fm_eq {b f} (φ : Formula σ b f) (ρ : Env ℳ b f) :
    (algebra ℳ).fm φ ρ ↔ Formula.satisfies ρ φ := by
  have h := (interpretation ℳ).fm_eval φ
  rw [Ast.fm_eq] at h
  exact Iff.of_eq (congrArg (fun p => p ρ) h.symm)

end Native
end YesMetaZFC.Model
