import YesMetaZFC.Model.Boolean.Semantics
import YesMetaZFC.Model.Boolean.TruthCongruence

/-! # 布尔值结构的等词证书与公式同余

项同余只消费函数保持；公式同余另消费等号规律和关系保持。
原生结构给出实际证书，布尔名称模型随后使用已证明的图等号与隶属同余。
-/

namespace YesMetaZFC.Model.Boolean
open Logic Logic.FirstOrder
universe u v w x y
variable {σ : Signature.{u, v, w}} {B : Type y}

namespace BV_str
variable (𝔹 : BA_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B)

def Args_rel (c : B) : {ss : List σ.SortSymbol} → Values ℳ.Carrier ss → Values ℳ.Carrier ss → Prop
  | _, .nil, .nil => True
  | _, .cons a as, .cons b bs => 𝔹.le c (ℳ.eqv a b) ∧ Args_rel c as bs

def Fn_respects : Prop := ∀ a c (xs ys : Values ℳ.Carrier (σ.funcDomain a)),
  Args_rel 𝔹 ℳ c xs ys → 𝔹.le c (ℳ.eqv (ℳ.funcInterp a xs) (ℳ.funcInterp a ys))

def Rel_respects : Prop := ∀ r c (xs ys : Values ℳ.Carrier (σ.relDomain r)),
  Args_rel 𝔹 ℳ c xs ys → 𝔹.Agree c (ℳ.relv r xs) (ℳ.relv r ys)

def Env_rel {b f} (c : B) (ρ τ : Env 𝔹 ℳ b f) : Prop :=
  (∀ {s} (i : Variable b s), 𝔹.le c (ℳ.eqv (ρ.boundVal i) (τ.boundVal i))) ∧
  (∀ {s} (i : Variable f s), 𝔹.le c (ℳ.eqv (ρ.freeVal i) (τ.freeVal i)))

mutual
theorem term_congr (hF : Fn_respects 𝔹 ℳ) {b f s c} {ρ τ : Env 𝔹 ℳ b f}
    (h : Env_rel 𝔹 ℳ c ρ τ) (t : Term σ b f s) : 𝔹.le c (ℳ.eqv (t.eval ρ) (t.eval τ)) := by
  cases t with
  | bvar i => exact h.1 i
  | fvar i => exact h.2 i
  | app a ts => exact hF a c _ _ (arguments_congr hF h ts)

theorem arguments_congr (hF : Fn_respects 𝔹 ℳ) {b f ss c} {ρ τ : Env 𝔹 ℳ b f}
    (h : Env_rel 𝔹 ℳ c ρ τ) (ts : Arguments σ b f ss) : Args_rel 𝔹 ℳ c (ts.eval ρ) (ts.eval τ) := by
  cases ts with
  | nil => trivial
  | cons t ts => exact ⟨term_congr hF h t, arguments_congr hF h ts⟩
end

end BV_str

structure EQ_laws (𝔹 : BA_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B) : Prop where
  eq_refl : ∀ {s} (a : ℳ.Carrier s), ℳ.eqv a a = 𝔹.top
  eq_symm : ∀ {s} (a b : ℳ.Carrier s), ℳ.eqv a b = ℳ.eqv b a
  eq_trans : ∀ {s} (a b c : ℳ.Carrier s), 𝔹.le (𝔹.meet (ℳ.eqv a b) (ℳ.eqv b c)) (ℳ.eqv a c)

structure BV_laws (𝔹 : BA_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B) : Prop extends EQ_laws 𝔹 ℳ where
  fn : ℳ.Fn_respects 𝔹
  rel : ℳ.Rel_respects 𝔹

namespace EQ_laws
variable {𝔹 : BA_alg B} {ℳ : BV_str.{u, v, w, x, y} σ B} (L : EQ_laws 𝔹 ℳ)
include L

theorem eq_under {s c} {a a' b b' : ℳ.Carrier s}
    (h : 𝔹.le c (ℳ.eqv a a')) (k : 𝔹.le c (ℳ.eqv b b')) :
    𝔹.le (𝔹.meet c (ℳ.eqv a b)) (ℳ.eqv a' b') := by
  have h' : 𝔹.le c (ℳ.eqv a' a) := by rw [L.eq_symm]; exact h
  exact 𝔹.le_trans (𝔹.le_meet
    (𝔹.le_trans (𝔹.le_meet (𝔹.le_trans (𝔹.meet_le_left _ _) h') (𝔹.meet_le_right _ _)) (L.eq_trans a' a b))
    (𝔹.le_trans (𝔹.meet_le_left _ _) k)) (L.eq_trans a' b b')

theorem eq_agree {s c} {a a' b b' : ℳ.Carrier s}
    (h : 𝔹.le c (ℳ.eqv a a')) (k : 𝔹.le c (ℳ.eqv b b')) :
    𝔹.Agree c (ℳ.eqv a b) (ℳ.eqv a' b') := by
  refine ⟨L.eq_under h k, L.eq_under ?_ ?_⟩
  · rw [L.eq_symm]; exact h
  · rw [L.eq_symm]; exact k

theorem env_push {b f s c} {ρ τ : ℳ.Env 𝔹 b f}
    (h : ℳ.Env_rel 𝔹 c ρ τ) (a : ℳ.Carrier s) :
    ℳ.Env_rel 𝔹 c (ρ.pushBound a) (τ.pushBound a) := by
  constructor
  · intro s i
    cases i with
    | here => change 𝔹.le c (ℳ.eqv a a); rw [L.eq_refl]; exact 𝔹.le_top _
    | there i => exact h.1 i
  · exact h.2

end EQ_laws

namespace BV_str
variable (𝔹 : CB_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B)

/-- 全部开放公式在布尔等同环境下同余；量词处只使用同一载体上的实际见证。 -/
theorem value_congr (L : BV_laws 𝔹.toBA_alg ℳ) {b f c} (φ : Formula σ b f)
    (ρ τ : ℳ.Env 𝔹.toBA_alg b f) (h : ℳ.Env_rel 𝔹.toBA_alg c ρ τ) :
    𝔹.Agree c (value 𝔹 ℳ φ ρ) (value 𝔹 ℳ φ τ) := by
  induction φ with
  | falsum => exact 𝔹.agree_refl _ _
  | truth => exact 𝔹.agree_refl _ _
  | rel r ts =>
      rw [value_rel, value_rel]
      exact L.rel r c _ _ (arguments_congr 𝔹.toBA_alg ℳ L.fn h ts)
  | equal t t' =>
      rw [value_equal, value_equal]
      exact L.toEQ_laws.eq_agree (term_congr 𝔹.toBA_alg ℳ L.fn h t)
        (term_congr 𝔹.toBA_alg ℳ L.fn h t')
  | neg φ ih => exact 𝔹.agree_neg (ih _ _ h)
  | conj φ ψ ih ik => exact 𝔹.agree_meet (ih _ _ h) (ik _ _ h)
  | disj φ ψ ih ik => exact 𝔹.agree_join (ih _ _ h) (ik _ _ h)
  | imp φ ψ ih ik => exact 𝔹.agree_imp (ih _ _ h) (ik _ _ h)
  | iff φ ψ ih ik => exact 𝔹.agree_iff (ih _ _ h) (ik _ _ h)
  | forallE s φ ih => exact 𝔹.agree_iInf (fun a => ih _ _ (L.toEQ_laws.env_push h a))
  | existsE s φ ih => exact 𝔹.agree_iSup (fun a => ih _ _ (L.toEQ_laws.env_push h a))

end BV_str

private theorem native_args_eq (ℳ : Structure.{u, v, w, x} σ) {ss c}
    (xs ys : Values ℳ.Carrier ss) (h : (native_str ℳ).Args_rel prop_algebra.toBA_alg c xs ys)
    (hc : c) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons a xs ih =>
      cases ys with
      | cons b ys =>
          exact (congrArg (fun a => Values.cons a xs) (h.1 hc)).trans
            (congrArg (Values.cons b) (ih ys h.2))

/-- 任意原生结构实际满足全部布尔等词与符号同余证书。 -/
theorem native_laws (ℳ : Structure.{u, v, w, x} σ) : BV_laws prop_algebra.toBA_alg (native_str ℳ) where
  eq_refl _ := propext ⟨fun _ h => h, fun _ => rfl⟩
  eq_symm _ _ := propext eq_comm
  eq_trans _ _ _ := fun ⟨h, k⟩ => h.trans k
  fn a _ xs ys h := fun hc => congrArg (ℳ.funcInterp a) (native_args_eq ℳ xs ys h hc)
  rel _ _ xs ys h := ⟨
    fun ⟨hc, hr⟩ => (native_args_eq ℳ xs ys h hc) ▸ hr,
    fun ⟨hc, hr⟩ => (native_args_eq ℳ xs ys h hc).symm ▸ hr⟩

end YesMetaZFC.Model.Boolean
