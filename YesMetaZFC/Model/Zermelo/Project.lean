import YesMetaZFC.Model.Zermelo.Semantics
import YesMetaZFC.SetTheory.Axioms.Z
import YesMetaZFC.SetTheory.Definitional.Project.Derivation

/-! # 原 Project 公式的稳定解释

全分离消费任意开放公式；其稳定性与外延同余由语法归纳统一给出。
到原类型化纯语言的对应只要求变量逐点相同，不使用环境函数外延性。
-/

namespace YesMetaZFC.Model.Zermelo
open SetTheory SetTheory.Definitional
universe u

abbrev p_carrier : SetTheory.Structure.{u+1} where
  Domain := V.{u}
  nonempty := ⟨V.empty⟩
  mem := V.mem
abbrev PEnv := SetTheory.Env p_carrier.{u}

def value {s : Nat} : {n : Nat} → Project.Formula s n → PEnv.{u} n → Prop
  | _, .falsum, _ => False
  | _, .truth, _ => True
  | _, .mem t t', ρ => V.mem (t.eval ρ) (t'.eval ρ)
  | _, .atom .extensionalEq _ ts, ρ => V.eq ((ts 0).eval ρ) ((ts 1).eval ρ)
  | _, .atom .subset _ ts, ρ => V.sub ((ts 0).eval ρ) ((ts 1).eval ρ)
  | _, .neg φ, ρ => ¬ value φ ρ
  | _, .conj φ ψ, ρ => value φ ρ ∧ value ψ ρ
  | _, .disj φ ψ, ρ => ¬¬(value φ ρ ∨ value ψ ρ)
  | _, .imp φ ψ, ρ => value φ ρ → value ψ ρ
  | _, .iff φ ψ, ρ => value φ ρ ↔ value ψ ρ
  | _, .forallE φ, ρ => ∀ x, value φ (ρ.push x)
  | _, .existsE φ, ρ => ¬¬∃ x, value φ (ρ.push x)
termination_by structural _ φ _ => φ

instance value_st {s n} (φ : Project.Formula s n) (ρ : PEnv.{u} n) : St (value φ ρ) := by
  induction φ with
  | falsum => exact st_false
  | truth => exact st_true
  | mem _ _ => exact V.mem_st _ _
  | atom r _ _ => cases r; exact V.eq_st _ _; exact V.sub_st _ _
  | neg _ _ | disj _ _ _ _ | existsE _ _ => exact st_not
  | conj _ _ ih ik => letI := ih ρ; letI := ik ρ; exact st_and
  | imp _ _ _ ik => letI := ik ρ; exact st_imp
  | iff _ _ ih ik => letI := ih ρ; letI := ik ρ; exact st_iff
  | forallE _ ih => letI := fun x => ih (ρ.push x); exact st_all

def PEnv_rel {n} (ρ τ : PEnv.{u} n) : Prop :=
  ∀ t : Project.Term n, V.eq (t.eval ρ) (t.eval τ)

theorem penv_refl {n} (ρ : PEnv.{u} n) : PEnv_rel ρ ρ := fun _ => V.eq_refl _

theorem penv_push {n} {ρ τ : PEnv.{u} n} (h : PEnv_rel ρ τ) {x y : V.{u}} (e : V.eq x y) :
    PEnv_rel (ρ.push x) (τ.push y) := by
  intro t
  cases t with
  | free i => exact h (.free i)
  | bound i => exact fin_cases e (fun i => h (.bound i)) i

theorem value_congr {s n} (φ : Project.Formula s n) {ρ τ : PEnv.{u} n} (h : PEnv_rel ρ τ) :
    value φ ρ ↔ value φ τ := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | mem t t' => exact V.mem_congr (h t) (h t')
  | atom r _ ts =>
    cases r with
    | extensionalEq => exact V.eq_congr (h (ts 0)) (h (ts 1))
    | subset =>
      exact ⟨fun k x hx => (V.mem_right (h (ts 1))).mp (k x ((V.mem_right (h (ts 0))).mpr hx)),
        fun k x hx => (V.mem_right (h (ts 1))).mpr (k x ((V.mem_right (h (ts 0))).mp hx))⟩
  | neg _ ih => exact not_congr (ih h)
  | conj _ _ ih ik => exact and_congr (ih h) (ik h)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih h) (ik h))
  | imp _ _ ih ik => exact imp_congr (ih h) (ik h)
  | iff _ _ ih ik => exact st_iff_congr (ih h) (ik h)
  | forallE _ ih =>
    exact ⟨fun k x => (ih (penv_push h (V.eq_refl x))).mp (k x),
      fun k x => (ih (penv_push h (V.eq_refl x))).mpr (k x)⟩
  | existsE _ ih =>
    exact nn_congr ⟨fun ⟨x, k⟩ => ⟨x, (ih (penv_push h (V.eq_refl x))).mp k⟩,
      fun ⟨x, k⟩ => ⟨x, (ih (penv_push h (V.eq_refl x))).mpr k⟩⟩

theorem ptm_bind {n m} (t : Project.Term n) (θ : Fin n → Project.Term m)
    (ρ : PEnv.{u} m) (τ : PEnv.{u} n)
    (h : ∀ i, (θ i).eval ρ = τ.bound i) (k : ∀ i, ρ.free i = τ.free i) :
    (t.bind θ).eval ρ = t.eval τ := by
  cases t with
  | bound i => exact h i
  | free i => exact k i

theorem value_bind {s n m} (φ : Project.Formula s n) (θ : Fin n → Project.Term m)
    (ρ : PEnv.{u} m) (τ : PEnv.{u} n)
    (h : ∀ i, (θ i).eval ρ = τ.bound i) (k : ∀ i, ρ.free i = τ.free i) :
    value (φ.bind θ) ρ ↔ value φ τ := by
  induction φ generalizing m with
  | falsum | truth => exact Iff.rfl
  | mem t t' =>
    change V.mem ((t.bind θ).eval ρ) ((t'.bind θ).eval ρ) ↔ _
    rw [ptm_bind t θ ρ τ h k, ptm_bind t' θ ρ τ h k]; exact Iff.rfl
  | atom r _ ts =>
    have e i : ((ts.bind θ) i).eval ρ = (ts i).eval τ :=
      (congrArg (Term.eval ρ) (TermVector.get_bind θ ts i)).trans (ptm_bind (ts i) θ ρ τ h k)
    cases r with
    | extensionalEq => change V.eq _ _ ↔ _; rw [e 0, e 1]; exact Iff.rfl
    | subset => change V.sub _ _ ↔ _; rw [e 0, e 1]; exact Iff.rfl
  | neg _ ih => exact not_congr (ih _ _ _ h k)
  | conj _ _ ih ik => exact and_congr (ih _ _ _ h k) (ik _ _ _ h k)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih _ _ _ h k) (ik _ _ _ h k))
  | imp _ _ ih ik => exact imp_congr (ih _ _ _ h k) (ik _ _ _ h k)
  | iff _ _ ih ik => exact st_iff_congr (ih _ _ _ h k) (ik _ _ _ h k)
  | forallE φ ih =>
    have e x := ih (Term.liftSubstitution θ) (ρ.push x) (τ.push x)
      (fun i => fin_cases rfl (fun i => (Term.eval_weaken ρ x (θ i)).trans (h i)) i) k
    exact ⟨fun g x => (e x).mp (g x), fun g x => (e x).mpr (g x)⟩
  | existsE φ ih =>
    have e x := ih (Term.liftSubstitution θ) (ρ.push x) (τ.push x)
      (fun i => fin_cases rfl (fun i => (Term.eval_weaken ρ x (θ i)).trans (h i)) i) k
    exact nn_congr ⟨fun ⟨x, g⟩ => ⟨x, (e x).mp g⟩, fun ⟨x, g⟩ => ⟨x, (e x).mpr g⟩⟩

theorem closure_valid {s n} (φ : Project.Formula s n) (ρ : PEnv.{u} 0)
    (h : ∀ b, value φ ⟨b, ρ.free⟩) : value (Formula.forallClosure n φ) ρ := by
  induction n with
  | zero => exact h ρ.bound
  | succ n ih =>
    apply ih (.forallE φ)
    intro b x
    change value φ ⟨fin_cases x b, ρ.free⟩
    exact h _

/-- 分离实例的正文、有限参数及绑定位置均保持原样。 -/
theorem separation_core {n} (φ : Project.UnarySchema n) (ρ : PEnv.{u} n) :
    value (Axioms.Schema.separationCore φ) ρ := by
  intro a
  let p (x : V.{u}) := value φ.body (ρ.push x)
  apply nn_in
  refine ⟨V.sep a p, fun x => ?_⟩
  have e : value (φ.body.rename BoundEmbedding.unaryUnderTwo)
      (((ρ.push a).push (V.sep a p)).push x) ↔ p x :=
    value_bind φ.body _ _ _ (fun i => fin_cases rfl (fun _ => rfl) i) (fun _ => rfl)
  exact (V.sep_mem a x p (fun d =>
    (value_congr φ.body (penv_push (penv_refl ρ) d)).mp)).trans (and_congr Iff.rfl e.symm)

theorem ptm_correct {n} (t : Project.Term n) (hc : t.freeSupport = [])
    (ρ : Env.{u} (Project.fo_bound_context n) []) (τ : PEnv.{u} n)
    (h : ∀ i, ρ.boundVal (Project.fo_bound_variable i) = τ.bound i) :
    (Project.fo_term t hc).eval ρ = t.eval τ := by
  cases t with
  | bound i => exact h i
  | free _ => cases hc

/-- 正确性针对仓库原翻译，不重写对象逻辑或理论公理。 -/
theorem formula_correct {s n} (φ : Project.Formula s n) (hc : φ.FreeClosed)
    (ρ : Env.{u} (Project.fo_bound_context n) []) (τ : PEnv.{u} n)
    (h : ∀ i, ρ.boundVal (Project.fo_bound_variable i) = τ.bound i) :
    sat (Project.fo_formula φ hc) ρ ↔ value φ τ := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | mem t t' =>
    apply (sat_mem _ _ _).trans
    rw [ptm_correct t hc.1 ρ τ h, ptm_correct t' hc.2 ρ τ h]
    exact Iff.rfl
  | atom r _ ts =>
    cases r with
    | extensionalEq =>
      apply (sat_eq _ _ _).trans
      rw [ptm_correct (ts 0) (hc 0) ρ τ h, ptm_correct (ts 1) (hc 1) ρ τ h]
      exact Iff.rfl
    | subset =>
      have e (x : V.{u}) (i : Fin 2) :
          ((Project.fo_term (ts i) (hc i)).weakenBound SetSort.set).eval (ρ.pushBound x) =
            (ts i).eval τ := (tm_weaken _ ρ x).trans (ptm_correct (ts i) (hc i) ρ τ h)
      exact ⟨fun k x hx => (e x 1) ▸ (sat_mem _ _ _).mp (k x ((sat_mem _ _ _).mpr ((e x 0).symm ▸ hx))),
        fun k x hx => (sat_mem _ _ _).mpr ((e x 1).symm ▸ k x ((e x 0) ▸ (sat_mem _ _ _).mp hx))⟩
  | neg _ ih => exact not_congr (ih hc _ _ h)
  | conj _ _ ih ik => exact and_congr (ih hc.1 _ _ h) (ik hc.2 _ _ h)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih hc.1 _ _ h) (ik hc.2 _ _ h))
  | imp _ _ ih ik => exact imp_congr (ih hc.1 _ _ h) (ik hc.2 _ _ h)
  | iff _ _ ih ik => exact st_iff_congr (ih hc.1 _ _ h) (ik hc.2 _ _ h)
  | forallE φ ih =>
    have e x := ih hc (ρ.pushBound x) (τ.push x) (fun i => fin_cases rfl (fun i => h i) i)
    exact ⟨fun k x => (e x).mp (k x), fun k x => (e x).mpr (k x)⟩
  | existsE φ ih =>
    have e x := ih hc (ρ.pushBound x) (τ.push x) (fun i => fin_cases rfl (fun i => h i) i)
    exact nn_congr ⟨fun ⟨x, k⟩ => ⟨x, (e x).mp k⟩, fun ⟨x, k⟩ => ⟨x, (e x).mpr k⟩⟩

end YesMetaZFC.Model.Zermelo
