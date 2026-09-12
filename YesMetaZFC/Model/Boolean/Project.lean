import YesMetaZFC.Model.Boolean.Closure
import YesMetaZFC.Model.SetTheory.ProjectSemantics

/-! # 原 Project 语法的布尔值解释

原项、环境和代入算法保持不变；外延等同与子集原子分别解释为已证明的名称等号、包含值。
逐构造核验与原 `fo_formula` 的对应，因此最终公理验证针对原仓库理论。
-/

namespace YesMetaZFC.Model.Boolean.BV_project
open SetTheory SetTheory.Definitional
open Logic.FirstOrder (Values)
open BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

abbrev carrier_structure := Project.FirstOrderSemantics.reduct
  (BV_str.top_structure 𝔹.toBA_alg (name_structure 𝔹))
abbrev Env (n : Nat) := SetTheory.Env (carrier_structure 𝔹) n

attribute [local implicit_reducible] name_structure Project.FirstOrderSemantics.reduct SetTheory.signature

def value {s : Nat} : {n : Nat} → Project.Formula s n → Env 𝔹 n → B
  | _, .falsum, _ => 𝔹.bot
  | _, .truth, _ => 𝔹.top
  | _, .mem t t', ρ => bv_mem 𝔹 (t.eval ρ) (t'.eval ρ)
  | _, .atom .extensionalEq _ ts, ρ => bv_eq 𝔹 ((ts 0).eval ρ) ((ts 1).eval ρ)
  | _, .atom .subset _ ts, ρ => subset 𝔹 ((ts 0).eval ρ) ((ts 1).eval ρ)
  | _, .neg φ, ρ => 𝔹.neg (value φ ρ)
  | _, .conj φ ψ, ρ => 𝔹.meet (value φ ρ) (value ψ ρ)
  | _, .disj φ ψ, ρ => 𝔹.join (value φ ρ) (value ψ ρ)
  | _, .imp φ ψ, ρ => 𝔹.imp (value φ ρ) (value ψ ρ)
  | _, .iff φ ψ, ρ => 𝔹.iff (value φ ρ) (value ψ ρ)
  | _, .forallE φ, ρ => 𝔹.iInf (fun G => value φ (ρ.push G))
  | _, .existsE φ, ρ => 𝔹.iSup (fun G => value φ (ρ.push G))
termination_by structural _ φ _ => φ

theorem value_bind {s n m} (φ : Project.Formula s n) (θ : Fin n → Project.Term m) (ρ : Env 𝔹 m) :
    value 𝔹 (φ.bind θ) ρ = value 𝔹 φ (Definitional.Env.substitute ρ θ) := by
  induction φ generalizing m with
  | falsum => rfl
  | truth => rfl
  | mem t t' => simp only [Formula.bind, value, Term.eval_bind]
  | atom r _ ts => cases r <;> simp only [Formula.bind, value, TermVector.get_bind, Term.eval_bind]
  | neg φ ih => simp only [Formula.bind, value, ih]
  | conj φ ψ ih ik => simp only [Formula.bind, value, ih, ik]
  | disj φ ψ ih ik => simp only [Formula.bind, value, ih, ik]
  | imp φ ψ ih ik => simp only [Formula.bind, value, ih, ik]
  | iff φ ψ ih ik => simp only [Formula.bind, value, ih, ik]
  | forallE φ ih => simp only [Formula.bind, value, ih, Semantics.substitute_lift]
  | existsE φ ih => simp only [Formula.bind, value, ih, Semantics.substitute_lift]

theorem value_rename {s n m} (φ : Project.Formula s n) (ξ : Fin n → Fin m) (ρ : Env 𝔹 m) :
    value 𝔹 (φ.rename ξ) ρ = value 𝔹 φ (ρ.reindex ξ) := by rw [Formula.rename, value_bind]; rfl

def Env_rel {n} (c : B) (ρ τ : Env 𝔹 n) : Prop :=
  ∀ t : Project.Term n, 𝔹.le c (bv_eq 𝔹 (t.eval ρ) (t.eval τ))

theorem env_refl {n} (c : B) (ρ : Env 𝔹 n) : Env_rel 𝔹 c ρ ρ := by
  intro t; rw [eq_refl]; exact 𝔹.le_top _

theorem env_push {n c} {ρ τ : Env 𝔹 n} (h : Env_rel 𝔹 c ρ τ) (G H : BV_graph.{u, u} B)
    (k : 𝔹.le c (bv_eq 𝔹 G H)) : Env_rel 𝔹 c (ρ.push G) (τ.push H) := by
  intro t
  cases t with
  | free i => exact h (.free i)
  | bound i =>
    exact Fin.cases k (fun i => h (.bound i)) i

theorem value_congr {s n c} (φ : Project.Formula s n) (ρ τ : Env 𝔹 n) (h : Env_rel 𝔹 c ρ τ) :
    𝔹.Agree c (value 𝔹 φ ρ) (value 𝔹 φ τ) := by
  induction φ with
  | falsum => exact 𝔹.agree_refl _ _
  | truth => exact 𝔹.agree_refl _ _
  | mem t t' =>
      exact (name_laws 𝔹).rel .membership c
        (.cons (t.eval ρ) (.cons (t'.eval ρ) .nil)) (.cons (t.eval τ) (.cons (t'.eval τ) .nil))
        ⟨h t, h t', trivial⟩
  | atom r _ ts =>
    cases r with
    | extensionalEq => exact (name_laws 𝔹).toEQ_laws.eq_agree (s := SetSort.set) (h (ts 0)) (h (ts 1))
    | subset => exact 𝔹.agree_iInf (fun G => 𝔹.agree_imp
        (𝔹.agree_mono (h (ts 0)) (stable_agree 𝔹 (stable_set 𝔹 G) _ _))
        (𝔹.agree_mono (h (ts 1)) (stable_agree 𝔹 (stable_set 𝔹 G) _ _)))
  | neg φ ih => exact 𝔹.agree_neg (ih _ _ h)
  | conj φ ψ ih ik => exact 𝔹.agree_meet (ih _ _ h) (ik _ _ h)
  | disj φ ψ ih ik => exact 𝔹.agree_join (ih _ _ h) (ik _ _ h)
  | imp φ ψ ih ik => exact 𝔹.agree_imp (ih _ _ h) (ik _ _ h)
  | iff φ ψ ih ik => exact 𝔹.agree_iff (ih _ _ h) (ik _ _ h)
  | forallE φ ih => exact 𝔹.agree_iInf (fun G => ih _ _ (env_push 𝔹 h G G (by
      rw [eq_refl]; exact 𝔹.le_top _)))
  | existsE φ ih => exact 𝔹.agree_iSup (fun G => ih _ _ (env_push 𝔹 h G G (by
      rw [eq_refl]; exact 𝔹.le_top _)))

/-- 任意开放正文及固定参数实际给出尊重名称等号的谓词。 -/
theorem value_stable {s n} (φ : Project.Formula s (n+1)) (ρ : Env 𝔹 n) :
    Stable 𝔹 (fun G => value 𝔹 φ (ρ.push G)) := by
  intro G H
  exact (value_congr 𝔹 φ _ _ (env_push 𝔹 (env_refl 𝔹 _ ρ) G H (𝔹.le_refl _))).1

theorem value_stable_left {s n} (φ : Project.Formula s (n+2)) (ρ : Env 𝔹 n)
    (K : BV_graph.{u, u} B) : Stable 𝔹 (fun G => value 𝔹 φ ((ρ.push G).push K)) := by
  intro G H
  exact (value_congr 𝔹 φ _ _ (env_push 𝔹
    (env_push 𝔹 (env_refl 𝔹 _ ρ) G H (𝔹.le_refl _)) K K (by rw [eq_refl]; exact 𝔹.le_top _))).1

/-- 全称闭合保留任意有限参数赋值。 -/
theorem closure_valid {s n} (φ : Project.Formula s n) (ρ : Env 𝔹 0)
    (h : ∀ b, 𝔹.le 𝔹.top (value 𝔹 φ ⟨b, ρ.free⟩)) :
    𝔹.le 𝔹.top (value 𝔹 (Formula.forallClosure n φ) ρ) := by
  induction n with
  | zero => exact h ρ.bound
  | succ n ih =>
    apply ih (.forallE φ)
    intro b
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : BV_graph.{u, u} B => value 𝔹 φ ((⟨b, ρ.free⟩ : Env 𝔹 n).push G)))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    simpa only [SetTheory.Env.push] using h (Fin.cases G b)

theorem mem_value {b} (t t' : Logic.FirstOrder.Term ℒ b [] SetSort.set)
    (ρ : (name_structure 𝔹).Env 𝔹.toBA_alg b []) :
    BV_str.value 𝔹 (name_structure 𝔹) (Project.fo_mem t t') ρ = bv_mem 𝔹 (t.eval ρ) (t'.eval ρ) := by
  rw [Project.fo_mem, BV_str.value_rel]; rfl

/-- 原翻译的每个自由闭合公式恰有相同的布尔值。 -/
theorem formula_correct {s n} (φ : Project.Formula s n) (hc : φ.FreeClosed)
    (ρ : (name_structure 𝔹).Env 𝔹.toBA_alg (Project.fo_bound_context n) [])
    (f : FreeVarId → BV_graph.{u, u} B) :
    BV_str.value 𝔹 (name_structure 𝔹) (Project.fo_formula φ hc) ρ =
      value 𝔹 φ (Project.FirstOrderSemantics.projectEnv ρ f) := by
  induction φ with
  | falsum => simp only [Project.fo_formula, BV_str.value_bot, value]
  | truth => simp only [Project.fo_formula, BV_str.value_top, value]
  | mem t t' => simp only [Project.fo_formula, mem_value, Project.FirstOrderSemantics.term_correct ρ f, value]
  | atom r _ ts =>
    cases r with
    | extensionalEq =>
      simp only [Project.fo_formula, BV_str.value_equal, Project.FirstOrderSemantics.term_correct ρ f, value]
      rfl
    | subset =>
      simp only [Project.fo_formula, BV_str.value_all, BV_str.value_imp, mem_value,
        Logic.FirstOrder.Term.eval_weakenBound, Project.FirstOrderSemantics.term_correct ρ f,
        Logic.FirstOrder.Term.eval, value, subset]
      rfl
  | neg φ ih => simp only [Project.fo_formula, BV_str.value_neg, value, ih]
  | conj φ ψ ih ik => simp only [Project.fo_formula, BV_str.value_conj, value, ih, ik]
  | disj φ ψ ih ik => simp only [Project.fo_formula, BV_str.value_disj, value, ih, ik]
  | imp φ ψ ih ik => simp only [Project.fo_formula, BV_str.value_imp, value, ih, ik]
  | iff φ ψ ih ik => simp only [Project.fo_formula, BV_str.value_iff, value, ih, ik]
  | forallE φ ih =>
    simp only [Project.fo_formula, BV_str.value_all, value, ih, Project.FirstOrderSemantics.projectEnv_push]
    rfl
  | existsE φ ih =>
    simp only [Project.fo_formula, BV_str.value_ex, value, ih, Project.FirstOrderSemantics.projectEnv_push]
    rfl

end YesMetaZFC.Model.Boolean.BV_project
