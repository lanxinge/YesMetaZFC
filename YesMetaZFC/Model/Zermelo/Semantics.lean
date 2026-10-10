import YesMetaZFC.Model.Zermelo.Tree
import YesMetaZFC.Model.Semantics.Background
import YesMetaZFC.SetTheory.Language

/-! # 集合树上的经典一阶稳定语义

直接解释仓库的原始 AST，并提供原 Hilbert 核的六规则证书。
环境只按点比较；代入和同余均证明逻辑等价，不使用函数或命题外延性。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory
universe u

abbrev carrier : FirstOrder.Structure.{0,0,0,u+1} ℒ where
  Carrier _ := V.{u}
  nonempty _ := ⟨V.empty⟩
  funcInterp f := nomatch f
  relInterp | .membership, .cons x (.cons y .nil) => x ∈ y

attribute [local implicit_reducible] SetTheory.signature

abbrev Env := FirstOrder.Env carrier.{u}

abbrev algebra : Sem_algebra.{0,0,0,u+1,u+1} ℒ where
  Tm b f _ := Env.{u} b f → V.{u}
  Pr b f := Env.{u} b f → Prop
  bvar i ρ := ρ.boundVal i
  fvar i ρ := ρ.freeVal i
  app f := nomatch f
  rel | .membership, .cons t (.cons t' .nil) => fun ρ => t ρ ∈ t' ρ
  eq t t' ρ := V.eq (t ρ) (t' ρ)
  bot _ := False
  top _ := True
  neg p ρ := ¬ p ρ
  conj p q ρ := p ρ ∧ q ρ
  disj p q ρ := ¬¬(p ρ ∨ q ρ)
  imp p q ρ := p ρ → q ρ
  iff p q ρ := p ρ ↔ q ρ
  all _ p ρ := ∀ a, p (ρ.pushBound a)
  ex _ p ρ := ¬¬∃ a, p (ρ.pushBound a)

abbrev sat {b f} (φ : FirstOrder.Formula ℒ b f) (ρ : Env.{u} b f) : Prop := algebra.fm φ ρ

theorem tm_val {b f s} (t : FirstOrder.Term ℒ b f s) (ρ : Env.{u} b f) :
    algebra.tm t ρ = t.eval ρ := by
  cases t with
  | bvar _ | fvar _ => rfl
  | app f _ => nomatch f

theorem sat_eq {b f s} (t t' : FirstOrder.Term ℒ b f s) (ρ : Env.{u} b f) :
    sat (.equal t t') ρ ↔ V.eq (t.eval ρ) (t'.eval ρ) := by
  change V.eq (algebra.tm t ρ) (algebra.tm t' ρ) ↔ _
  rw [tm_val, tm_val]

theorem sat_mem {b f} (t t' : FirstOrder.Term ℒ b f SetSort.set) (ρ : Env.{u} b f) :
    sat (.rel .membership (.cons t (.cons t' .nil))) ρ ↔ V.mem (t.eval ρ) (t'.eval ρ) := by
  change (algebra.tm t ρ ∈ algebra.tm t' ρ) ↔ _
  rw [tm_val, tm_val]
  rfl

instance sat_st {b f} (φ : FirstOrder.Formula ℒ b f) (ρ : Env.{u} b f) : St (sat φ ρ) := by
  induction φ with
  | falsum => exact st_false
  | truth => exact st_true
  | equal _ _ => exact V.eq_st _ _
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons _ (.cons _ .nil) => V.mem_st _ _
  | neg _ _ | disj _ _ _ _ | existsE _ _ _ => exact st_not
  | conj _ _ ih ik => letI := ih ρ; letI := ik ρ; exact st_and
  | imp _ _ _ ik => letI := ik ρ; exact st_imp
  | iff _ _ ih ik => letI := ih ρ; letI := ik ρ; exact st_iff
  | forallE s φ ih => letI := fun a => ih (ρ.pushBound a); exact st_all

def Env_rel {b f} (ρ τ : Env.{u} b f) : Prop :=
  (∀ {s} (i : Variable b s), V.eq (ρ.boundVal i) (τ.boundVal i)) ∧
  (∀ {s} (i : Variable f s), V.eq (ρ.freeVal i) (τ.freeVal i))

theorem env_refl {b f} (ρ : Env.{u} b f) : Env_rel ρ ρ :=
  ⟨fun _ => V.eq_refl _, fun _ => V.eq_refl _⟩

theorem env_push {b f s} {ρ τ : Env.{u} b f} (h : Env_rel ρ τ) {x y : V.{u}}
    (k : V.eq x y) : Env_rel (ρ.pushBound (sort := s) x) (τ.pushBound y) :=
  ⟨fun i => match i with | .here => k | .there i => h.1 i, h.2⟩

theorem tm_congr {b f s} (t : FirstOrder.Term ℒ b f s) {ρ τ : Env.{u} b f}
    (h : Env_rel ρ τ) : V.eq (t.eval ρ) (t.eval τ) := by
  cases t with
  | bvar i => exact h.1 i
  | fvar i => exact h.2 i
  | app f _ => nomatch f

/-- 对全部开放公式及所有参数成立，随后直接用于全分离模式。 -/
theorem sat_congr {b f} (φ : FirstOrder.Formula ℒ b f) {ρ τ : Env.{u} b f}
    (h : Env_rel ρ τ) : sat φ ρ ↔ sat φ τ := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | equal t t' =>
    exact (sat_eq t t' ρ).trans
      ((V.eq_congr (tm_congr t h) (tm_congr t' h)).trans (sat_eq t t' τ).symm)
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons t' .nil) =>
      (sat_mem t t' ρ).trans
        ((V.mem_congr (tm_congr t h) (tm_congr t' h)).trans (sat_mem t t' τ).symm)
  | neg _ ih => exact not_congr (ih h)
  | conj _ _ ih ik => exact and_congr (ih h) (ik h)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih h) (ik h))
  | imp _ _ ih ik => exact imp_congr (ih h) (ik h)
  | iff _ _ ih ik => exact st_iff_congr (ih h) (ik h)
  | forallE _ _ ih => exact ⟨fun k x => (ih (env_push h (V.eq_refl x))).mp (k x),
      fun k x => (ih (env_push h (V.eq_refl x))).mpr (k x)⟩
  | existsE _ _ ih =>
    exact nn_congr
      ⟨fun ⟨x, k⟩ => ⟨x, (ih (env_push h (V.eq_refl x))).mp k⟩,
       fun ⟨x, k⟩ => ⟨x, (ih (env_push h (V.eq_refl x))).mpr k⟩⟩

theorem tm_rename {b f b' f' s} (t : FirstOrder.Term ℒ b f s)
    (ξ : VariableRenaming b b') (η : VariableRenaming f f')
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), ρ.boundVal (ξ i) = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), ρ.freeVal (η i) = τ.freeVal i) :
    (t.renameMapped ξ η).eval ρ = t.eval τ := by
  cases t with
  | bvar i => exact h i
  | fvar i => exact k i
  | app f _ => nomatch f

/-- 点态重命名律，不把两个环境提升为函数等号。 -/
theorem sat_rename {b f b' f'} (φ : FirstOrder.Formula ℒ b f)
    (ξ : VariableRenaming b b') (η : VariableRenaming f f')
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), ρ.boundVal (ξ i) = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), ρ.freeVal (η i) = τ.freeVal i) :
    sat (φ.renameMapped ξ η) ρ ↔ sat φ τ := by
  induction φ generalizing b' f' with
  | falsum | truth => exact Iff.rfl
  | equal t t' =>
    exact (sat_eq _ _ _).trans ((tm_rename t ξ η ρ τ h k) ▸
      (tm_rename t' ξ η ρ τ h k) ▸ (sat_eq t t' τ).symm)
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons t' .nil) =>
        (sat_mem _ _ _).trans ((tm_rename t ξ η ρ τ h k) ▸
          (tm_rename t' ξ η ρ τ h k) ▸ (sat_mem t t' τ).symm)
  | neg _ ih => exact not_congr (ih _ _ _ _ h k)
  | conj _ _ ih ik => exact and_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k))
  | imp _ _ ih ik => exact imp_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | iff _ _ ih ik => exact st_iff_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | forallE s φ ih =>
    have e x := ih (VariableRenaming.lift ξ) η (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => h i) k
    exact ⟨fun g x => (e x).mp (g x), fun g x => (e x).mpr (g x)⟩
  | existsE s φ ih =>
    have e x := ih (VariableRenaming.lift ξ) η (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => h i) k
    exact nn_congr ⟨fun ⟨x, g⟩ => ⟨x, (e x).mp g⟩, fun ⟨x, g⟩ => ⟨x, (e x).mpr g⟩⟩

theorem tm_weaken {b f s t} (a : FirstOrder.Term ℒ b f t) (ρ : Env.{u} b f) (x : V.{u}) :
    (a.weakenBound s).eval (ρ.pushBound x) = a.eval ρ :=
  tm_rename a _ _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem tm_subst {b f b' f' s} (t : FirstOrder.Term ℒ b f s)
    (θ : VariableSubstitution ℒ b b' f') (η : VariableSubstitution ℒ f b' f')
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), (θ i).eval ρ = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), (η i).eval ρ = τ.freeVal i) :
    (t.substituteMapped θ η).eval ρ = t.eval τ := by
  cases t with
  | bvar i => exact h i
  | fvar i => exact k i
  | app f _ => nomatch f

theorem sat_subst {b f b' f'} (φ : FirstOrder.Formula ℒ b f)
    (θ : VariableSubstitution ℒ b b' f') (η : VariableSubstitution ℒ f b' f')
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), (θ i).eval ρ = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), (η i).eval ρ = τ.freeVal i) :
    sat (φ.substituteMapped θ η) ρ ↔ sat φ τ := by
  induction φ generalizing b' f' with
  | falsum | truth => exact Iff.rfl
  | equal t t' =>
    exact (sat_eq _ _ _).trans ((tm_subst t θ η ρ τ h k) ▸
      (tm_subst t' θ η ρ τ h k) ▸ (sat_eq t t' τ).symm)
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons t' .nil) =>
        (sat_mem _ _ _).trans ((tm_subst t θ η ρ τ h k) ▸
          (tm_subst t' θ η ρ τ h k) ▸ (sat_mem t t' τ).symm)
  | neg _ ih => exact not_congr (ih _ _ _ _ h k)
  | conj _ _ ih ik => exact and_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k))
  | imp _ _ ih ik => exact imp_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | iff _ _ ih ik => exact st_iff_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | forallE s φ ih =>
    have e x := ih (VariableSubstitution.liftBound s θ) (VariableSubstitution.weakenBound s η)
      (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => (tm_weaken _ ρ x).trans (h i))
      (fun i => (tm_weaken _ ρ x).trans (k i))
    exact ⟨fun g x => (e x).mp (g x), fun g x => (e x).mpr (g x)⟩
  | existsE s φ ih =>
    have e x := ih (VariableSubstitution.liftBound s θ) (VariableSubstitution.weakenBound s η)
      (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => (tm_weaken _ ρ x).trans (h i))
      (fun i => (tm_weaken _ ρ x).trans (k i))
    exact nn_congr ⟨fun ⟨x, g⟩ => ⟨x, (e x).mp g⟩, fun ⟨x, g⟩ => ⟨x, (e x).mpr g⟩⟩

theorem sat_inst {b f s} (φ : FirstOrder.Formula ℒ (s :: b) f)
    (t : FirstOrder.Term ℒ b f s) (ρ : Env.{u} b f) :
    sat (φ.instantiateTop t) ρ ↔ sat φ (ρ.pushBound (t.eval ρ)) :=
  sat_subst φ _ _ _ _ (fun i => match i with | .here => rfl | .there _ => rfl) (fun _ => rfl)

theorem sat_abstract {b f s} (φ : FirstOrder.Formula ℒ b (s :: f))
    (ρ : Env.{u} b f) (x : V.{u}) :
    sat φ.abstractFreeTop (ρ.pushBound x) ↔ sat φ (ρ.pushFree x) :=
  sat_subst φ _ _ _ _ (fun _ => rfl) (fun i => match i with | .here => rfl | .there _ => rfl)

theorem sat_forall {b f s} (φ : FirstOrder.Formula ℒ b (s :: f)) (ρ : Env.{u} b f) :
    sat (φ.forallFreeTop s) ρ ↔ ∀ x, sat φ (ρ.pushFree x) :=
  ⟨fun h x => (sat_abstract φ ρ x).mp (h x), fun h x => (sat_abstract φ ρ x).mpr (h x)⟩

theorem sat_exists {b f s} (φ : FirstOrder.Formula ℒ b (s :: f)) (ρ : Env.{u} b f) :
    sat (φ.existsFreeTop s) ρ ↔ ¬¬∃ x, sat φ (ρ.pushFree x) :=
  nn_congr ⟨fun ⟨x, h⟩ => ⟨x, (sat_abstract φ ρ x).mp h⟩,
    fun ⟨x, h⟩ => ⟨x, (sat_abstract φ ρ x).mpr h⟩⟩

theorem sat_weaken {b f s} (φ : FirstOrder.Formula ℒ b f) (ρ : Env.{u} b f) (x : V.{u}) :
    sat (φ.weakenFree s) (ρ.pushFree x) ↔ sat φ ρ :=
  sat_rename φ _ _ _ _ (fun _ => rfl) (fun _ => rfl)

abbrev background : Sem_background.{0,0,0,u+1,u+1} ℒ where
  context := algebra.toSem_context
  valid p := ∀ ρ, p ρ

/-- 实际模型是原相对语义接口的一个具体实例。 -/
abbrev model : Sem_model background.{u} where
  app := algebra.app
  rel := algebra.rel

theorem axiom_valid {f} {φ : OpenFormula ℒ f} (h : HilbertBaseAxiom ℒ φ)
    (ρ : Env.{u} [] f) : sat φ ρ := by
  cases h with
  | implication_distribution _ _ _ => exact fun h k p => h p (k p)
  | self_implication _ | weakening _ _ => exact fun h _ => h
  | contradiction _ _ => exact fun h n => (n h).elim
  | classical φ => exact fun h => St.elim (fun n => n (h n))
  | explosion _ _ => exact fun n h => (n h).elim
  | case_analysis φ ψ => exact fun h k => st_cases (sat φ ρ) h k
  | truth_intro => trivial
  | falsum_elimination _ => exact False.elim
  | negation_intro _ => exact id
  | negation_elimination _ => exact fun h n => n h
  | conjunction_intro _ _ => exact fun h k => ⟨h, k⟩
  | conjunction_elim_left _ _ => exact And.left
  | conjunction_elim_right _ _ => exact And.right
  | disjunction_intro_left _ _ => exact fun h => nn_in (Or.inl h)
  | disjunction_intro_right _ _ => exact fun h => nn_in (Or.inr h)
  | disjunction_elimination _ _ _ => exact fun h k e => st_use e (fun p => p.elim h k)
  | biconditional_intro _ _ => exact fun h k => ⟨h, k⟩
  | biconditional_elim_left _ _ => exact Iff.mp
  | biconditional_elim_right _ _ => exact Iff.mpr
  | forall_specialization _ φ t => exact fun h => (sat_inst φ t ρ).mpr (h (t.eval ρ))
  | forall_distribution s φ ψ =>
    intro h k
    exact (sat_forall ψ ρ).mpr (fun x => (sat_forall (.imp φ ψ) ρ).mp h x
      ((sat_forall φ ρ).mp k x))
  | vacuous_forall s φ =>
    intro h
    exact (sat_forall (φ.weakenFree s) ρ).mpr (fun x => (sat_weaken φ ρ x).mpr h)
  | exists_introduction _ φ t =>
    exact fun h => nn_in ⟨t.eval ρ, (sat_inst φ t ρ).mp h⟩
  | exists_elimination s φ ψ =>
    intro h k
    exact st_use ((sat_exists φ ρ).mp k) (fun ⟨x, hx⟩ =>
      (sat_weaken ψ ρ x).mp ((sat_forall (.imp φ (ψ.weakenFree s)) ρ).mp h x hx))
  | equality_reflexivity t => exact (sat_eq t t ρ).mpr (V.eq_refl _)
  | equality_substitution s t t' φ =>
    intro h k
    apply (sat_inst φ t' ρ).mpr
    exact (sat_congr φ (ρ := ρ.pushBound (t.eval ρ)) (τ := ρ.pushBound (t'.eval ρ))
      ⟨(fun i => match i with
      | .here => (sat_eq t t' ρ).mp h
      | .there i => nomatch i), fun _ => V.eq_refl _⟩).mp ((sat_inst φ t ρ).mp k)

/-- 原经典逻辑公理及全部六规则，无排中律参数。 -/
theorem rules : Sem_rules model.{u} where
  axiom_valid h := axiom_valid h
  sentence_lift {f} {φ} h ρ := by
    cases f with
    | nil =>
      exact (sat_congr φ ⟨(fun i => nomatch i), (fun i => nomatch i)⟩).mpr
        (h FirstOrder.Env.empty)
    | cons s f =>
      exact (sat_rename φ _ _ ρ FirstOrder.Env.empty
        (fun i => nomatch i) (fun i => nomatch i)).mpr (h FirstOrder.Env.empty)
  mp h k ρ := k ρ (h ρ)
  generalize {f} {s} {φ} h ρ := (sat_forall φ ρ).mpr (fun x => h (ρ.pushFree x))
  strengthen {f} {s} {φ} h ρ := (sat_weaken φ ρ V.empty).mp (h (ρ.pushFree V.empty))
  substitute {f} {f'} θ {φ} h ρ := (sat_subst φ _ _ ρ (ρ.pullback (.free_map θ))
    (fun _ => rfl) (fun _ => rfl)).mpr (h _)

theorem not_false : ¬ model.{u}.holds (.falsum : FirstOrder.Sentence ℒ) :=
  fun h => h FirstOrder.Env.empty

end YesMetaZFC.Model.Zermelo
