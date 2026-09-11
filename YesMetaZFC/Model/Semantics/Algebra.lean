import YesMetaZFC.Logic.Syntax
import YesMetaZFC.Model.Values

/-!
# 上下文索引的语义代数

`Tm b f s` 是背景中从变量上下文到排序 `s` 的映射，`Pr b f` 是该上下文的谓词。
它们不必是 Lean 对象及其函数空间：内部项、函数图和布尔值谓词均可作为解释对象。
等同与量词是显式操作；这里不要求宿主非空性、外部良基性或二阶封闭。
本模块只给解释运算，逻辑可靠性不作为任意代数的隐藏结论。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder

universe u v w x y x' y'

-- 两个独立字段分别保留项与谓词的 universe。
set_option linter.checkUnivs false in
/-- 排序上下文的背景操作，不包含任何函数或关系符号的解释。 -/
structure Sem_context (σ : Signature.{u, v, w}) where
  Tm : SortContext σ → SortContext σ → σ.SortSymbol → Type (max u x)
  Pr : SortContext σ → SortContext σ → Type y
  bvar : ∀ {b f s}, Variable b s → Tm b f s
  fvar : ∀ {b f s}, Variable f s → Tm b f s
  eq : ∀ {b f s}, Tm b f s → Tm b f s → Pr b f
  bot : ∀ {b f}, Pr b f
  top : ∀ {b f}, Pr b f
  neg : ∀ {b f}, Pr b f → Pr b f
  conj : ∀ {b f}, Pr b f → Pr b f → Pr b f
  disj : ∀ {b f}, Pr b f → Pr b f → Pr b f
  imp : ∀ {b f}, Pr b f → Pr b f → Pr b f
  iff : ∀ {b f}, Pr b f → Pr b f → Pr b f
  all : ∀ {b f} (s : σ.SortSymbol), Pr (s :: b) f → Pr b f
  ex : ∀ {b f} (s : σ.SortSymbol), Pr (s :: b) f → Pr b f

-- 继承的项域与谓词域继续保持独立的 universe。
set_option linter.checkUnivs false in
/-- 背景操作与符号解释共同构成公式求值所需的代数。 -/
structure Sem_algebra (σ : Signature.{u, v, w})
    extends Sem_context.{u, v, w, x, y} σ where
  app : ∀ {b f} (a : σ.FuncSymbol),
    Values (Tm b f) (σ.funcDomain a) → Tm b f (σ.funcCodomain a)
  rel : ∀ {b f} (r : σ.RelSymbol), Values (Tm b f) (σ.relDomain r) → Pr b f

namespace Sem_algebra
variable {σ : Signature.{u, v, w}} (A : Sem_algebra.{u, v, w, x, y} σ)

mutual
/-- 只对当前标准 AST 递归，不对背景的内部码做外部递归。 -/
def tm {b f s} : Term σ b f s → A.Tm b f s
  | .bvar i => A.bvar i
  | .fvar i => A.fvar i
  | .app a ts => A.app a (args ts)

/-- 异质项列在同一上下文中的解释。 -/
def args {b f ss} : Arguments σ b f ss → Values (A.Tm b f) ss
  | .nil => .nil
  | .cons t ts => .cons (tm t) (args ts)
end

/-- 全部一阶构造的解释；量词由背景操作解释。 -/
def fm {b f} : Formula σ b f → A.Pr b f
  | .falsum => A.bot
  | .truth => A.top
  | .rel r ts => A.rel r (A.args ts)
  | .equal t t' => A.eq (A.tm t) (A.tm t')
  | .neg φ => A.neg (fm φ)
  | .conj φ ψ => A.conj (fm φ) (fm ψ)
  | .disj φ ψ => A.disj (fm φ) (fm ψ)
  | .imp φ ψ => A.imp (fm φ) (fm ψ)
  | .iff φ ψ => A.iff (fm φ) (fm ψ)
  | .forallE s φ => A.all s (fm φ)
  | .existsE s φ => A.ex s (fm φ)

end Sem_algebra

/-- 只保持变量及函数应用的项解释映射。 -/
structure Tm_map {σ : Signature.{u, v, w}}
    (A : Sem_algebra.{u, v, w, x, y} σ)
    (B : Sem_algebra.{u, v, w, x', y'} σ) where
  tm : ∀ {b f s}, A.Tm b f s → B.Tm b f s
  bvar_eq : ∀ {b f s} (i : Variable b s), tm (A.bvar (f := f) i) = B.bvar i
  fvar_eq : ∀ {b f s} (i : Variable f s), tm (A.fvar (b := b) i) = B.fvar i
  app_eq : ∀ {b f} a (ts : Values (A.Tm b f) (σ.funcDomain a)),
    tm (A.app a ts) = B.app a (ts.map (fun _ => tm))

/-- 逐操作保持的完整解释映射；不含真值反射或可证性反射。 -/
structure Sem_map {σ : Signature.{u, v, w}}
    (A : Sem_algebra.{u, v, w, x, y} σ)
    (B : Sem_algebra.{u, v, w, x', y'} σ) extends Tm_map A B where
  fm : ∀ {b f}, A.Pr b f → B.Pr b f
  rel_eq : ∀ {b f} r (ts : Values (A.Tm b f) (σ.relDomain r)),
    fm (A.rel r ts) = B.rel r (ts.map (fun _ => tm))
  eq_eq : ∀ {b f s} (t t' : A.Tm b f s), fm (A.eq t t') = B.eq (tm t) (tm t')
  bot_eq : ∀ {b f}, fm (A.bot (b := b) (f := f)) = B.bot
  top_eq : ∀ {b f}, fm (A.top (b := b) (f := f)) = B.top
  neg_eq : ∀ {b f} (p : A.Pr b f), fm (A.neg p) = B.neg (fm p)
  conj_eq : ∀ {b f} (p q : A.Pr b f), fm (A.conj p q) = B.conj (fm p) (fm q)
  disj_eq : ∀ {b f} (p q : A.Pr b f), fm (A.disj p q) = B.disj (fm p) (fm q)
  imp_eq : ∀ {b f} (p q : A.Pr b f), fm (A.imp p q) = B.imp (fm p) (fm q)
  iff_eq : ∀ {b f} (p q : A.Pr b f), fm (A.iff p q) = B.iff (fm p) (fm q)
  all_eq : ∀ {b f} s (p : A.Pr (s :: b) f), fm (A.all s p) = B.all s (fm p)
  ex_eq : ∀ {b f} s (p : A.Pr (s :: b) f), fm (A.ex s p) = B.ex s (fm p)

namespace Tm_map
variable {σ : Signature.{u, v, w}}
  {A : Sem_algebra.{u, v, w, x, y} σ} {B : Sem_algebra.{u, v, w, x', y'} σ}

mutual
/-- 项解释沿背景映射交换。 -/
theorem tm_eval (I : Tm_map A B) {b f s} (t : Term σ b f s) :
    I.tm (A.tm t) = B.tm t := by
  cases t with
  | bvar i => exact I.bvar_eq i
  | fvar i => exact I.fvar_eq i
  | app a ts =>
      exact (I.app_eq a (A.args ts)).trans (congrArg (B.app a) (I.args_eval ts))

/-- 参数列解释沿背景映射交换。 -/
theorem args_eval (I : Tm_map A B) {b f ss} (ts : Arguments σ b f ss) :
    (A.args ts).map (fun _ => I.tm) = B.args ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      change Values.cons (I.tm (A.tm t)) ((A.args ts).map (fun _ => I.tm)) = _
      rw [I.tm_eval, I.args_eval]
      rfl
end

end Tm_map

namespace Sem_map
variable {σ : Signature.{u, v, w}}
  {A : Sem_algebra.{u, v, w, x, y} σ} {B : Sem_algebra.{u, v, w, x', y'} σ}

/-- 完整公式的解释保持由原子与各逻辑操作的保持推出。 -/
theorem fm_eval (I : Sem_map A B) {b f} (φ : Formula σ b f) :
    I.fm (A.fm φ) = B.fm φ := by
  induction φ with
  | falsum => exact I.bot_eq
  | truth => exact I.top_eq
  | rel r ts => exact (I.rel_eq r _).trans (congrArg (B.rel r) (I.toTm_map.args_eval ts))
  | equal t t' => simp only [Sem_algebra.fm, I.eq_eq, I.toTm_map.tm_eval]
  | neg φ h => exact (I.neg_eq _).trans (congrArg B.neg h)
  | conj φ ψ h k => simp only [Sem_algebra.fm, I.conj_eq, h, k]
  | disj φ ψ h k => simp only [Sem_algebra.fm, I.disj_eq, h, k]
  | imp φ ψ h k => simp only [Sem_algebra.fm, I.imp_eq, h, k]
  | iff φ ψ h k => simp only [Sem_algebra.fm, I.iff_eq, h, k]
  | forallE s φ h => exact (I.all_eq s _).trans (congrArg (B.all s) h)
  | existsE s φ h => exact (I.ex_eq s _).trans (congrArg (B.ex s) h)

end Sem_map
end YesMetaZFC.Model
