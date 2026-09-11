import YesMetaZFC.Model.Semantics.Instances

/-! # 标准语法代入的背景作用

这里只要求背景接受当前 AST 所表示的代入；不要求所有内部码都能外部解码。
量词下的作用显式使用 `liftBound`，恒等及复合也分别核验。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder
universe u v w x y

variable {σ : Signature.{u, v, w}}

/-- 项代入只要求变量与函数应用的局部作用律。 -/
structure Tm_substitution (A : Sem_algebra.{u, v, w, x, y} σ) where
  tm : ∀ {b f b' f' s}, Substitution σ b f b' f' → A.Tm b f s → A.Tm b' f' s
  bvar_eq : ∀ {b f b' f' s} (θ : Substitution σ b f b' f') (i : Variable b s),
    tm θ (A.bvar i) = A.tm ((Term.bvar i).substitute θ)
  fvar_eq : ∀ {b f b' f' s} (θ : Substitution σ b f b' f') (i : Variable f s),
    tm θ (A.fvar i) = A.tm ((Term.fvar i).substitute θ)
  app_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') a ts,
    tm θ (A.app a ts) = A.app a (ts.map (fun _ => tm θ))

/-- 完整谓词代入另要求原子、联结词及量词的局部作用律。 -/
structure Sem_substitution (A : Sem_algebra.{u, v, w, x, y} σ)
    extends Tm_substitution A where
  fm : ∀ {b f b' f'}, Substitution σ b f b' f' → A.Pr b f → A.Pr b' f'
  rel_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') r ts,
    fm θ (A.rel r ts) = A.rel r (ts.map (fun _ => tm θ))
  eq_eq : ∀ {b f b' f' s} (θ : Substitution σ b f b' f') (t t' : A.Tm b f s),
    fm θ (A.eq t t') = A.eq (tm θ t) (tm θ t')
  bot_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f'), fm θ A.bot = A.bot
  top_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f'), fm θ A.top = A.top
  neg_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') p,
    fm θ (A.neg p) = A.neg (fm θ p)
  conj_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') p q,
    fm θ (A.conj p q) = A.conj (fm θ p) (fm θ q)
  disj_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') p q,
    fm θ (A.disj p q) = A.disj (fm θ p) (fm θ q)
  imp_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') p q,
    fm θ (A.imp p q) = A.imp (fm θ p) (fm θ q)
  iff_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') p q,
    fm θ (A.iff p q) = A.iff (fm θ p) (fm θ q)
  all_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') s p,
    fm θ (A.all s p) = A.all s (fm (θ.liftBound s) p)
  ex_eq : ∀ {b f b' f'} (θ : Substitution σ b f b' f') s p,
    fm θ (A.ex s p) = A.ex s (fm (θ.liftBound s) p)

/-- 全部背景对象上的恒等与复合；不把这些额外条件加入标准 AST 的代入正确性。 -/
structure Sem_action {A : Sem_algebra.{u, v, w, x, y} σ}
    (R : Sem_substitution A) : Prop where
  tm_id : ∀ {b f s} (t : A.Tm b f s), R.tm .id t = t
  fm_id : ∀ {b f} (p : A.Pr b f), R.fm .id p = p
  tm_comp : ∀ {b f b' f' b'' f'' s}
    (θ : Substitution σ b f b' f') (η : Substitution σ b' f' b'' f'') (t : A.Tm b f s),
    R.tm η (R.tm θ t) = R.tm (η.comp θ) t
  fm_comp : ∀ {b f b' f' b'' f''}
    (θ : Substitution σ b f b' f') (η : Substitution σ b' f' b'' f'') (p : A.Pr b f),
    R.fm η (R.fm θ p) = R.fm (η.comp θ) p

namespace Tm_substitution
variable {A : Sem_algebra.{u, v, w, x, y} σ}

mutual
/-- 项代入的正确性只消费变量与应用的作用律。 -/
theorem tm_eval (R : Tm_substitution A) {b f b' f' s}
    (θ : Substitution σ b f b' f') (t : Term σ b f s) :
    A.tm (t.substitute θ) = R.tm θ (A.tm t) := by
  cases t with
  | bvar i => exact (R.bvar_eq _ i).symm
  | fvar i => exact (R.fvar_eq _ i).symm
  | app a ts =>
      have h : (.app a ts : Term σ b f _).substitute θ = .app a (ts.substitute θ) :=
        by cases θ <;> rfl
      rw [h]
      change A.app a (A.args (ts.substitute θ)) = R.tm θ (A.app a (A.args ts))
      rw [R.args_eval, R.app_eq]

/-- 异质参数列逐项代入。 -/
theorem args_eval (R : Tm_substitution A) {b f b' f' ss}
    (θ : Substitution σ b f b' f') (ts : Arguments σ b f ss) :
    A.args (ts.substitute θ) = (A.args ts).map (fun _ => R.tm θ) := by
  cases ts with
  | nil => cases θ <;> rfl
  | cons t ts =>
      have h := congr (congrArg Values.cons (R.tm_eval θ t)) (R.args_eval θ ts)
      have k : (Arguments.cons t ts).substitute θ = .cons (t.substitute θ) (ts.substitute θ) :=
        by cases θ <;> rfl
      rw [k]
      exact h
end

end Tm_substitution

namespace Sem_substitution
variable {A : Sem_algebra.{u, v, w, x, y} σ}

/-- 完整公式的代入正确性，包含量词下的变量提升。 -/
theorem fm_eval (R : Sem_substitution A) {b f b' f'}
    (θ : Substitution σ b f b' f') (φ : Formula σ b f) :
    A.fm (φ.substitute θ) = R.fm θ (A.fm φ) := by
  induction φ generalizing b' f' with
  | falsum =>
      have h : (Formula.falsum : Formula σ _ _).substitute θ = .falsum := by cases θ <;> rfl
      rw [h]
      exact (R.bot_eq _).symm
  | truth =>
      have h : (Formula.truth : Formula σ _ _).substitute θ = .truth := by cases θ <;> rfl
      rw [h]
      exact (R.top_eq _).symm
  | rel r ts =>
      calc
        _ = A.rel r (A.args (ts.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [R.toTm_substitution.args_eval]; exact (R.rel_eq _ _ _).symm
  | equal t t' =>
      calc
        _ = A.eq (A.tm (t.substitute θ)) (A.tm (t'.substitute θ)) := by cases θ <;> rfl
        _ = _ := by
          rw [R.toTm_substitution.tm_eval, R.toTm_substitution.tm_eval]
          exact (R.eq_eq _ _ _).symm
  | neg φ h =>
      calc
        _ = A.neg (A.fm (φ.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [h]; exact (R.neg_eq _ _).symm
  | conj φ ψ h k =>
      calc
        _ = A.conj (A.fm (φ.substitute θ)) (A.fm (ψ.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [h, k]; exact (R.conj_eq _ _ _).symm
  | disj φ ψ h k =>
      calc
        _ = A.disj (A.fm (φ.substitute θ)) (A.fm (ψ.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [h, k]; exact (R.disj_eq _ _ _).symm
  | imp φ ψ h k =>
      calc
        _ = A.imp (A.fm (φ.substitute θ)) (A.fm (ψ.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [h, k]; exact (R.imp_eq _ _ _).symm
  | iff φ ψ h k =>
      calc
        _ = A.iff (A.fm (φ.substitute θ)) (A.fm (ψ.substitute θ)) := by cases θ <;> rfl
        _ = _ := by rw [h, k]; exact (R.iff_eq _ _ _).symm
  | forallE s φ h =>
      calc
        _ = A.all s (A.fm (φ.substitute (θ.liftBound s))) := by cases θ <;> rfl
        _ = _ := by rw [h]; exact (R.all_eq _ _ _).symm
  | existsE s φ h =>
      calc
        _ = A.ex s (A.fm (φ.substitute (θ.liftBound s))) := by cases θ <;> rfl
        _ = _ := by rw [h]; exact (R.ex_eq _ _ _).symm

end Sem_substitution

namespace Native
variable (ℳ : Structure.{u, v, w, x} σ)

/-- 原生环境的拉回保持连续代入；包括非闭项与全部排序。 -/
theorem pullback_comp {b f b' f' b'' f''}
    (θ : Substitution σ b f b' f') (η : Substitution σ b' f' b'' f'')
    (ρ : Env ℳ b'' f'') : ρ.pullback (η.comp θ) = (ρ.pullback η).pullback θ := by
  cases η with
  | id => rfl
  | map α β =>
      cases θ with
      | id => rfl
      | map γ δ =>
          apply Env.ext
          · intro s i
            exact Term.eval_substitute ρ (.map α β) (γ i)
          · intro s i
            exact Term.eval_substitute ρ (.map α β) (δ i)

/-- 任意原生结构上的实际代入作用；量词交换复用已证明的环境提升定理。 -/
def substitution : Sem_substitution (algebra ℳ) where
  tm θ t ρ := t (ρ.pullback θ)
  fm θ p ρ := p (ρ.pullback θ)
  bvar_eq θ i := by
    funext ρ
    rw [tm_eq]
    cases θ <;> rfl
  fvar_eq θ i := by
    funext ρ
    rw [tm_eq]
    cases θ <;> rfl
  app_eq θ a ts := by
    funext ρ
    change ℳ.funcInterp a _ = ℳ.funcInterp a _
    rw [Values.map_comp]
  rel_eq θ r ts := by
    funext ρ
    change ℳ.relInterp r _ = ℳ.relInterp r _
    rw [Values.map_comp]
  eq_eq _ _ _ := rfl
  bot_eq _ := rfl
  top_eq _ := rfl
  neg_eq _ _ := rfl
  conj_eq _ _ _ := rfl
  disj_eq _ _ _ := rfl
  imp_eq _ _ _ := rfl
  iff_eq _ _ _ := rfl
  all_eq θ s p := by
    funext ρ
    change (∀ a, p ((ρ.pullback θ).pushBound a)) = (∀ a, p ((ρ.pushBound a).pullback _))
    simp only [Env.pullback_liftBound]
  ex_eq θ s p := by
    funext ρ
    change (∃ a, p ((ρ.pullback θ).pushBound a)) = (∃ a, p ((ρ.pushBound a).pullback _))
    simp only [Env.pullback_liftBound]

/-- 原生拉回在全部环境函数和谓词上保持恒等与复合。 -/
theorem action : Sem_action (substitution ℳ) where
  tm_id _ := rfl
  fm_id _ := rfl
  tm_comp θ η t := by funext ρ; exact congrArg t (pullback_comp ℳ θ η ρ).symm
  fm_comp θ η p := by funext ρ; exact congrArg p (pullback_comp ℳ θ η ρ).symm

end Native

namespace Ast

/-- 标准码的参数装配与代入交换。 -/
theorem arguments_substitute {b f b' f' ss} (θ : Substitution σ b f b' f')
    (ts : Values (Term σ b f) ss) :
    (arguments ts).substitute θ = arguments (ts.map (fun _ t => t.substitute θ)) := by
  cases θ <;> induction ts with
  | nil => rfl
  | cons t ts h => exact congrArg (Arguments.cons _) h

/-- 原 AST 也是代入作用的实际实例，不需要商化或选择函数。 -/
def substitution (σ : Signature.{u, v, w}) : Sem_substitution (algebra σ) where
  tm θ t := t.substitute θ
  fm θ φ := φ.substitute θ
  bvar_eq _ _ := (tm_eq _).symm
  fvar_eq _ _ := (tm_eq _).symm
  app_eq θ a ts := by
    have h := arguments_substitute θ ts
    cases θ <;> exact congrArg (Term.app a) h
  rel_eq θ r ts := by
    have h := arguments_substitute θ ts
    cases θ <;> exact congrArg (Formula.rel r) h
  eq_eq θ _ _ := by cases θ <;> rfl
  bot_eq θ := by cases θ <;> rfl
  top_eq θ := by cases θ <;> rfl
  neg_eq θ _ := by cases θ <;> rfl
  conj_eq θ _ _ := by cases θ <;> rfl
  disj_eq θ _ _ := by cases θ <;> rfl
  imp_eq θ _ _ := by cases θ <;> rfl
  iff_eq θ _ _ := by cases θ <;> rfl
  all_eq θ _ _ := by cases θ <;> rfl
  ex_eq θ _ _ := by cases θ <;> rfl

/-- 语法背景的恒等与复合由原核的代入定理核验。 -/
theorem action (σ : Signature.{u, v, w}) : Sem_action (substitution σ) where
  tm_id _ := rfl
  fm_id _ := rfl
  tm_comp θ η t := Term.substitute_comp η θ t
  fm_comp θ η φ := Formula.substitute_comp η θ φ

end Ast
end YesMetaZFC.Model
