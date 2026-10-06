import YesMetaZFC.Model.Zermelo.Hull

/-! # 在闭包范围内重放原 Hilbert 推导
自由变量的实际成员证书随原推导传递；一般化、代入和加强均使用原核的构造子。
本模块消费原 Z 推导。收集公理仍由独立的局部范围解释提供，尚未加入此重放定理。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional
universe u
attribute [local implicit_reducible] SetTheory.signature

theorem sc_rename {b f b' f'} (φ : FirstOrder.Formula ℒ b f)
    (ξ : VariableRenaming b b') (η : VariableRenaming f f') (d : V.{u})
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), ρ.boundVal (ξ i) = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), ρ.freeVal (η i) = τ.freeVal i) :
    sc_sat (φ.renameMapped ξ η) d ρ ↔ sc_sat φ d τ := by
  induction φ generalizing b' f' with
  | falsum | truth => exact Iff.rfl
  | equal t t' =>
    exact (sat_weaken (s := SetSort.set) (.equal (t.renameMapped ξ η) (t'.renameMapped ξ η)) ρ d).trans
      ((sat_eq _ _ _).trans ((tm_rename t ξ η ρ τ h k) ▸ (tm_rename t' ξ η ρ τ h k) ▸
        (sat_eq t t' τ).symm.trans (sat_weaken (s := SetSort.set) (.equal t t') τ d).symm))
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons t' .nil) =>
      (sat_weaken (s := SetSort.set) (.rel .membership (.cons (t.renameMapped ξ η)
        (.cons (t'.renameMapped ξ η) .nil))) ρ d).trans
        ((sat_mem _ _ _).trans ((tm_rename t ξ η ρ τ h k) ▸ (tm_rename t' ξ η ρ τ h k) ▸
          (sat_mem t t' τ).symm.trans
            (sat_weaken (s := SetSort.set) (.rel .membership (.cons t (.cons t' .nil))) τ d).symm))
  | neg _ ih => exact not_congr (ih _ _ _ _ h k)
  | conj _ _ ih ik => exact and_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k))
  | imp _ _ ih ik => exact imp_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | iff _ _ ih ik => exact st_iff_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | forallE s φ ih | existsE s φ ih =>
    cases s
    have e x := ih (VariableRenaming.lift ξ) η (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => h i) k
    first
    | exact ⟨fun p x hx => (e x).mp (p x hx), fun p x hx => (e x).mpr (p x hx)⟩
    | exact nn_congr ⟨fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mp p⟩,
        fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mpr p⟩⟩

theorem sc_weaken {b f s} (φ : FirstOrder.Formula ℒ b f) (d : V.{u}) (ρ : Env.{u} b f) (x : V.{u}) :
    sc_sat (φ.weakenFree s) d (ρ.pushFree x) ↔ sc_sat φ d ρ :=
  sc_rename φ _ _ d _ _ (fun _ => rfl) (fun _ => rfl)

theorem sc_inst_value {b f s} (φ : FirstOrder.Formula ℒ (s :: b) f)
    (t : FirstOrder.Term ℒ b f s) (d : V.{u}) (ρ : Env.{u} b f) :
    sc_sat (φ.instantiateTop t) d ρ ↔ sc_sat φ d (ρ.pushBound (t.eval ρ)) :=
  sc_subst φ _ _ d _ _ (fun i => match i with | .here => rfl | .there _ => rfl) (fun _ => rfl)

theorem sc_abstract {b f s} (φ : FirstOrder.Formula ℒ b (s :: f))
    (d : V.{u}) (ρ : Env.{u} b f) (x : V.{u}) :
    sc_sat φ.abstractFreeTop d (ρ.pushBound x) ↔ sc_sat φ d (ρ.pushFree x) :=
  sc_subst φ _ _ d _ _ (fun _ => rfl) (fun i => match i with | .here => rfl | .there _ => rfl)

theorem sc_forall {b f s} (φ : FirstOrder.Formula ℒ b (s :: f)) (d : V.{u}) (ρ : Env.{u} b f) :
    sc_sat (φ.forallFreeTop s) d ρ ↔ ∀ x, x ∈ d → sc_sat φ d (ρ.pushFree x) := by
  cases s
  exact ⟨fun h x hx => (sc_abstract φ d ρ x).mp (h x hx),
    fun h x hx => (sc_abstract φ d ρ x).mpr (h x hx)⟩

theorem sc_exists_free {b f s} (φ : FirstOrder.Formula ℒ b (s :: f)) (d : V.{u}) (ρ : Env.{u} b f) :
    sc_sat (φ.existsFreeTop s) d ρ ↔ ¬¬∃ x, x ∈ d ∧ sc_sat φ d (ρ.pushFree x) := by
  cases s
  exact nn_congr ⟨fun ⟨x, hx, p⟩ => ⟨x, hx, (sc_abstract φ d ρ x).mp p⟩,
    fun ⟨x, hx, p⟩ => ⟨x, hx, (sc_abstract φ d ρ x).mpr p⟩⟩

abbrev Sc_free {b f} (d : V.{u}) (ρ : Env.{u} b f) : Prop :=
  ∀ {s} (i : Variable f s), ρ.freeVal i ∈ d

private theorem sc_tm_mem {f s} (t : OpenTerm ℒ f s) {d : V.{u}} {ρ : Env.{u} [] f}
    (h : Sc_free d ρ) : t.eval ρ ∈ d := by
  cases t with
  | bvar i => nomatch i
  | fvar i => exact h i
  | app g _ => nomatch g

private theorem sc_eq_value {b f s} (t t' : FirstOrder.Term ℒ b f s) (d : V.{u}) (ρ : Env.{u} b f) :
    sc_sat (.equal t t') d ρ ↔ V.eq (t.eval ρ) (t'.eval ρ) :=
  (sat_weaken (s := SetSort.set) (.equal t t') ρ d).trans (sat_eq t t' ρ)

/-- 原全部逻辑公理在带成员证书的环境中有效。 -/
theorem sc_axiom {f} {φ : OpenFormula ℒ f} (p : HilbertBaseAxiom ℒ φ)
    (d : V.{u}) (ρ : Env.{u} [] f) (hρ : Sc_free d ρ) : sc_sat φ d ρ := by
  cases p with
  | implication_distribution _ _ _ => exact fun h k p => h p (k p)
  | self_implication _ | weakening _ _ => exact fun h _ => h
  | contradiction _ _ => exact fun h n => (n h).elim
  | classical φ => exact fun h => St.elim (fun n => n (h n))
  | explosion _ _ => exact fun n h => (n h).elim
  | case_analysis φ ψ => exact fun h k => st_cases (sc_sat φ d ρ) h k
  | truth_intro => trivial
  | falsum_elimination _ => exact False.elim
  | negation_intro _ => exact id
  | negation_elimination _ => exact fun h n => n h
  | conjunction_intro _ _ => exact fun h k => ⟨h, k⟩
  | conjunction_elim_left _ _ => exact And.left
  | conjunction_elim_right _ _ => exact And.right
  | disjunction_intro_left _ _ => exact fun h => nn_in (.inl h)
  | disjunction_intro_right _ _ => exact fun h => nn_in (.inr h)
  | disjunction_elimination _ _ _ => exact fun h k e => st_use e (fun p => p.elim h k)
  | biconditional_intro _ _ => exact fun h k => ⟨h, k⟩
  | biconditional_elim_left _ _ => exact Iff.mp
  | biconditional_elim_right _ _ => exact Iff.mpr
  | forall_specialization s φ t => cases s; exact fun h => sc_inst φ t d ρ h (sc_tm_mem t hρ)
  | forall_distribution s φ ψ =>
    intro h k
    exact (sc_forall ψ d ρ).mpr (fun x hx => (sc_forall (.imp φ ψ) d ρ).mp h x hx
      ((sc_forall φ d ρ).mp k x hx))
  | vacuous_forall s φ =>
    exact fun h => (sc_forall (φ.weakenFree s) d ρ).mpr (fun x _ => (sc_weaken φ d ρ x).mpr h)
  | exists_introduction s φ t => cases s; exact fun h => sc_exists φ t d ρ h (sc_tm_mem t hρ)
  | exists_elimination s φ ψ =>
    intro h k
    exact st_use ((sc_exists_free φ d ρ).mp k) (fun ⟨x, hx, hp⟩ =>
      (sc_weaken ψ d ρ x).mp ((sc_forall (.imp φ (ψ.weakenFree s)) d ρ).mp h x hx hp))
  | equality_reflexivity t => exact (sc_eq_value t t d ρ).mpr (V.eq_refl _)
  | equality_substitution s t t' φ =>
    intro h k
    apply (sc_inst_value φ t' d ρ).mpr
    exact (sat_congr (gl_form φ)
      (ρ := (ρ.pushBound (t.eval ρ)).pushFree d) (τ := (ρ.pushBound (t'.eval ρ)).pushFree d)
      ⟨(fun i => match i with | .here => (sc_eq_value t t' d ρ).mp h | .there i => nomatch i),
        fun _ => V.eq_refl _⟩).mp ((sc_inst_value φ t d ρ).mp k)

/-- 重放原 Z 推导的全部六条规则；新参数可为任意已经进入闭包的对象。 -/
theorem hl_replay {f} {φ : OpenFormula ℒ f}
    (p : HilbertDerivation (Project.fo_theory SetTheory.Z) f φ)
    (d : V.{u}) (h : Sl_trans d) (ρ : Env.{u} [] f) (hρ : Sc_free (hl_range d) ρ) :
    sc_sat φ (hl_range d) ρ := by
  induction p with
  | logical_axiom p => exact sc_axiom p (hl_range d) ρ hρ
  | @theory_axiom f _ hp =>
    obtain ⟨s, hs, e⟩ := hp
    cases e
    cases f with
    | nil => exact hl_z d h s hs ρ
    | cons _ _ => exact (sc_rename (Project.fo_sentence s) _ _ (hl_range d) ρ FirstOrder.Env.empty
        (fun i => nomatch i) (fun i => nomatch i)).mpr (hl_z d h s hs FirstOrder.Env.empty)
  | modus_ponens _ _ ih ik => exact ik ρ hρ (ih ρ hρ)
  | @forall_generalization f s φ _ ih =>
    exact (sc_forall φ (hl_range d) ρ).mpr (fun x hx => ih (ρ.pushFree x)
      (fun i => match i with | .here => hx | .there i => hρ i))
  | @free_strengthening f s φ _ ih =>
    exact (sc_weaken φ (hl_range d) ρ V.empty).mp (ih (ρ.pushFree V.empty)
      (fun i => match i with | .here => hl_empty d | .there i => hρ i))
  | @free_substitution f f' θ φ _ ih =>
    exact (sc_subst φ _ _ (hl_range d) ρ (ρ.pullback (.free_map θ))
      (fun _ => rfl) (fun _ => rfl)).mpr (ih _ (fun i => sc_tm_mem (θ i) hρ))

/-- 收集池的成员证书直接接到原 Z 证明的自由参数，不再要求它属于旧载体。 -/
theorem hl_pool_replay {b f} {ψ : OpenFormula ℒ [.set]}
    (p : HilbertDerivation (Project.fo_theory SetTheory.Z) [.set] ψ)
    (φ : FirstOrder.Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f) (a : V.{u}) :
    sc_sat ψ (hl_range gl_space) (FirstOrder.Env.empty.pushFree (gl_pool φ ρ a)) :=
  hl_replay p gl_space sl_space_trans _ (fun i => match i with
    | .here => hl_power gl_space _ (gl_pool_bound φ ρ a)
    | .there i => nomatch i)

/-- 同一载体内的后续收集也直接产生原 Z 证明所需的参数证书。 -/
theorem hl_collect_replay {n} {ψ : OpenFormula ℒ [.set]}
    (p : HilbertDerivation (Project.fo_theory SetTheory.Z) [.set] ψ)
    (φ : Project.BinarySchema n) (r i w : V.{u}) (h : Sl_trans w)
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) :
    sc_sat ψ (hl_range w) (FirstOrder.Env.empty.pushFree (sc_collect φ r i w ρ a)) :=
  hl_replay p w h _ (fun j => match j with
    | .here => hl_power w _ (sc_collect_bound φ r i w ρ a)
    | .there j => nomatch j)

/-- info: 'YesMetaZFC.Model.Zermelo.hl_replay' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_replay
/-- info: 'YesMetaZFC.Model.Zermelo.hl_pool_replay' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_pool_replay
/-- info: 'YesMetaZFC.Model.Zermelo.hl_collect_replay' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_collect_replay
end YesMetaZFC.Model.Zermelo
