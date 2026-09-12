import YesMetaZFC.Model.Boolean.Algebra
import YesMetaZFC.Model.Semantics.Substitution

/-! # 任意签名上的布尔值语义

等号与关系都由结构给出布尔值。顶值原子结构复用原项和环境算法；
布尔联结词与量词由公共 `Sem_algebra.fm` 解释，可靠性另由规则证书证明。
-/

namespace YesMetaZFC.Model.Boolean
open Logic Logic.FirstOrder
universe u v w x y

structure BV_str (σ : Signature.{u, v, w}) (B : Type y) where
  Carrier : σ.SortSymbol → Type (max u x)
  nonempty : ∀ s, Nonempty (Carrier s)
  funcInterp : (a : σ.FuncSymbol) → Values Carrier (σ.funcDomain a) → Carrier (σ.funcCodomain a)
  eqv : ∀ {s}, Carrier s → Carrier s → B
  relv : (r : σ.RelSymbol) → Values Carrier (σ.relDomain r) → B

namespace BV_str
variable {σ : Signature.{u, v, w}} {B : Type y}

/-- 顶值原子解释；这里不宣称它保持布尔复合公式或模型性。 -/
abbrev top_structure (𝔹 : BA_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B) :
    Structure.{u, v, w, x} σ where
  Carrier := ℳ.Carrier
  nonempty := ℳ.nonempty
  funcInterp := ℳ.funcInterp
  relInterp r xs := 𝔹.le 𝔹.top (ℳ.relv r xs)

abbrev Env (𝔹 : BA_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B) :=
  FirstOrder.Env (top_structure 𝔹 ℳ)

variable (𝔹 : CB_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B)

abbrev algebra : Sem_algebra.{u, v, w, max u x, max u x y} σ where
  Tm b f s := Env 𝔹.toBA_alg ℳ b f → ℳ.Carrier s
  Pr b f := Env 𝔹.toBA_alg ℳ b f → B
  bvar i ρ := ρ.boundVal i
  fvar i ρ := ρ.freeVal i
  app a ts ρ := ℳ.funcInterp a (ts.map (fun _ t => t ρ))
  rel r ts ρ := ℳ.relv r (ts.map (fun _ t => t ρ))
  eq t t' ρ := ℳ.eqv (t ρ) (t' ρ)
  bot _ := 𝔹.bot
  top _ := 𝔹.top
  neg p ρ := 𝔹.neg (p ρ)
  conj p q ρ := 𝔹.meet (p ρ) (q ρ)
  disj p q ρ := 𝔹.join (p ρ) (q ρ)
  imp p q ρ := 𝔹.imp (p ρ) (q ρ)
  iff p q ρ := 𝔹.iff (p ρ) (q ρ)
  all _ p ρ := 𝔹.iInf (fun a => p (ρ.pushBound a))
  ex _ p ρ := 𝔹.iSup (fun a => p (ρ.pushBound a))

def term_map : Tm_map (Ast.algebra σ) (algebra 𝔹 ℳ) where
  tm t ρ := t.eval ρ
  bvar_eq := (Native.interpretation (top_structure 𝔹.toBA_alg ℳ)).bvar_eq
  fvar_eq := (Native.interpretation (top_structure 𝔹.toBA_alg ℳ)).fvar_eq
  app_eq := (Native.interpretation (top_structure 𝔹.toBA_alg ℳ)).app_eq

theorem tm_eq {b f s} (t : Term σ b f s) (ρ : Env 𝔹.toBA_alg ℳ b f) :
    (algebra 𝔹 ℳ).tm t ρ = t.eval ρ := by
  have h := (term_map 𝔹 ℳ).tm_eval t
  rw [Ast.tm_eq] at h
  exact congrArg (fun t => t ρ) h.symm

theorem args_eq {b f ss} (ts : Arguments σ b f ss) (ρ : Env 𝔹.toBA_alg ℳ b f) :
    ((algebra 𝔹 ℳ).args ts).map (fun _ t => t ρ) = ts.eval ρ := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      change Values.cons ((algebra 𝔹 ℳ).tm t ρ) (((algebra 𝔹 ℳ).args ts).map (fun _ t => t ρ)) =
        Values.cons (t.eval ρ) (ts.eval ρ)
      rw [tm_eq, args_eq ts ρ]

abbrev value {b f} (φ : Formula σ b f) (ρ : Env 𝔹.toBA_alg ℳ b f) : B := (algebra 𝔹 ℳ).fm φ ρ

section
variable {b f} (φ ψ : Formula σ b f) (ρ : Env 𝔹.toBA_alg ℳ b f)
theorem value_bot : value 𝔹 ℳ (.falsum : Formula σ b f) ρ = 𝔹.bot := rfl
theorem value_top : value 𝔹 ℳ (.truth : Formula σ b f) ρ = 𝔹.top := rfl
theorem value_neg : value 𝔹 ℳ (.neg φ) ρ = 𝔹.neg (value 𝔹 ℳ φ ρ) := rfl
theorem value_conj : value 𝔹 ℳ (.conj φ ψ) ρ = 𝔹.meet (value 𝔹 ℳ φ ρ) (value 𝔹 ℳ ψ ρ) := rfl
theorem value_disj : value 𝔹 ℳ (.disj φ ψ) ρ = 𝔹.join (value 𝔹 ℳ φ ρ) (value 𝔹 ℳ ψ ρ) := rfl
theorem value_imp : value 𝔹 ℳ (.imp φ ψ) ρ = 𝔹.imp (value 𝔹 ℳ φ ρ) (value 𝔹 ℳ ψ ρ) := rfl
theorem value_iff : value 𝔹 ℳ (.iff φ ψ) ρ = 𝔹.iff (value 𝔹 ℳ φ ρ) (value 𝔹 ℳ ψ ρ) := rfl
theorem value_all {s} (φ : Formula σ (s :: b) f) :
    value 𝔹 ℳ (.forallE s φ) ρ = 𝔹.iInf (fun a => value 𝔹 ℳ φ (ρ.pushBound a)) := rfl
theorem value_ex {s} (φ : Formula σ (s :: b) f) :
    value 𝔹 ℳ (.existsE s φ) ρ = 𝔹.iSup (fun a => value 𝔹 ℳ φ (ρ.pushBound a)) := rfl
end

theorem value_equal {b f s} (t t' : Term σ b f s) (ρ : Env 𝔹.toBA_alg ℳ b f) :
    value 𝔹 ℳ (.equal t t') ρ = ℳ.eqv (t.eval ρ) (t'.eval ρ) := by
  change ℳ.eqv ((algebra 𝔹 ℳ).tm t ρ) ((algebra 𝔹 ℳ).tm t' ρ) = _
  rw [tm_eq, tm_eq]

theorem value_rel {b f} (r : σ.RelSymbol) (ts : Arguments σ b f (σ.relDomain r))
    (ρ : Env 𝔹.toBA_alg ℳ b f) : value 𝔹 ℳ (.rel r ts) ρ = ℳ.relv r (ts.eval ρ) := by
  change ℳ.relv r (((algebra 𝔹 ℳ).args ts).map (fun _ t => t ρ)) = _
  rw [args_eq]

/-- 标准代入在布尔背景中的完整作用，复用原环境提升与公共代入定理。 -/
def substitution : Sem_substitution (algebra 𝔹 ℳ) where
  tm θ t ρ := t (ρ.pullback θ)
  fm θ p ρ := p (ρ.pullback θ)
  bvar_eq θ i := by funext ρ; rw [tm_eq]; cases θ <;> rfl
  fvar_eq θ i := by funext ρ; rw [tm_eq]; cases θ <;> rfl
  app_eq θ a ts := by
    funext ρ
    change ℳ.funcInterp a _ = ℳ.funcInterp a _
    rw [Values.map_comp]
  rel_eq θ r ts := by
    funext ρ
    change ℳ.relv r _ = ℳ.relv r _
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
    apply congrArg 𝔹.iInf
    funext a
    exact congrArg p (FirstOrder.Env.pullback_liftBound ρ θ s a).symm
  ex_eq θ s p := by
    funext ρ
    apply congrArg 𝔹.iSup
    funext a
    exact congrArg p (FirstOrder.Env.pullback_liftBound ρ θ s a).symm

theorem value_substitute {b f b' f'} (θ : Substitution σ b f b' f') (φ : Formula σ b f)
    (ρ : Env 𝔹.toBA_alg ℳ b' f') : value 𝔹 ℳ (φ.substitute θ) ρ = value 𝔹 ℳ φ (ρ.pullback θ) :=
  congrArg (fun p => p ρ) ((substitution 𝔹 ℳ).fm_eval θ φ)

end BV_str

/-- 原生结构在命题布尔代数中的实际解释。 -/
def native_str {σ : Signature.{u, v, w}} (ℳ : Structure.{u, v, w, x} σ) : BV_str σ Prop where
  Carrier := ℳ.Carrier
  nonempty := ℳ.nonempty
  funcInterp := ℳ.funcInterp
  eqv a b := a = b
  relv := ℳ.relInterp

end YesMetaZFC.Model.Boolean
