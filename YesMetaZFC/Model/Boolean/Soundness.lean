import YesMetaZFC.Model.Boolean.Bindings
import YesMetaZFC.Model.Boolean.Congruence
import YesMetaZFC.Model.Semantics.Background

/-! # 布尔值背景中的原 Hilbert 核可靠性

逐条核验原逻辑公理；有限联结词使用剩余律，量词使用确界，等词替换使用开放公式同余。
六规则证书接入公共相对可靠性，不引入新的推导关系。
-/

namespace YesMetaZFC.Model.Boolean.BV_str
open Logic Logic.FirstOrder
universe u v w x y
variable {σ : Signature.{u, v, w}} {B : Type y}
  (𝔹 : CB_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B)

/-- 每个原基础逻辑公理的布尔值为顶。 -/
theorem axiom_valid (L : BV_laws 𝔹.toBA_alg ℳ) {f} {φ : OpenFormula σ f}
    (h : HilbertBaseAxiom σ φ) (ρ : ℳ.Env 𝔹.toBA_alg [] f) :
    𝔹.le 𝔹.top (value 𝔹 ℳ φ ρ) := by
  cases h <;> try simp only [value_bot, value_top, value_neg, value_conj, value_disj,
    value_imp, value_iff, value_all, value_ex]
  case implication_distribution φ ψ χ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff, 𝔹.le_imp_iff]
    exact 𝔹.imp_use
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)) (𝔹.meet_le_right _ _))
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) (𝔹.meet_le_right _ _))
  case self_implication φ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff]; exact 𝔹.meet_le_left _ _
  case weakening φ ψ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff]; exact 𝔹.meet_le_left _ _
  case contradiction φ ψ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff, 𝔹.meet_neg]; exact 𝔹.bot_le _
  case classical φ =>
    rw [𝔹.valid_imp_iff]
    exact 𝔹.case_use (𝔹.meet_le_right _ _) (𝔹.imp_elim _ _)
  case explosion φ ψ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff, 𝔹.meet_comm, 𝔹.meet_neg]; exact 𝔹.bot_le _
  case case_analysis φ ψ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff]
    exact 𝔹.case_use
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)) (𝔹.meet_le_right _ _))
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) (𝔹.meet_le_right _ _))
  case truth_intro => exact 𝔹.le_refl _
  case falsum_elimination φ => rw [𝔹.valid_imp_iff]; exact 𝔹.bot_le _
  case negation_intro φ => rw [𝔹.valid_imp_iff]; exact 𝔹.le_refl _
  case negation_elimination φ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff, 𝔹.meet_neg]; exact 𝔹.le_refl _
  case conjunction_intro φ ψ => rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff]; exact 𝔹.le_refl _
  case conjunction_elim_left φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.meet_le_left _ _
  case conjunction_elim_right φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.meet_le_right _ _
  case disjunction_intro_left φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.le_join_left _ _
  case disjunction_intro_right φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.le_join_right _ _
  case disjunction_elimination φ ψ χ =>
    rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff, 𝔹.le_imp_iff]
    exact 𝔹.meet_join_le
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)) (𝔹.meet_le_right _ _))
      (𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) (𝔹.meet_le_right _ _))
  case biconditional_intro φ ψ => rw [𝔹.valid_imp_iff, 𝔹.le_imp_iff]; exact 𝔹.le_refl _
  case biconditional_elim_left φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.meet_le_left _ _
  case biconditional_elim_right φ ψ => rw [𝔹.valid_imp_iff]; exact 𝔹.meet_le_right _ _
  case forall_specialization s φ t =>
    rw [𝔹.valid_imp_iff, value_instantiate]
    exact 𝔹.iInf_le (fun a => value 𝔹 ℳ φ (ρ.pushBound a)) (t.eval ρ)
  case forall_distribution s φ ψ =>
    rw [𝔹.valid_imp_iff, value_forall, value_forall, value_forall, 𝔹.le_imp_iff, 𝔹.le_iInf_iff]
    intro a
    exact 𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.iInf_le _ a))
      (𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.iInf_le _ a))
  case vacuous_forall s φ =>
    rw [𝔹.valid_imp_iff, value_forall, 𝔹.le_iInf_iff]
    intro a; rw [value_weaken]; exact 𝔹.le_refl _
  case exists_introduction s φ t =>
    rw [𝔹.valid_imp_iff, value_instantiate]
    exact 𝔹.le_iSup (fun a => value 𝔹 ℳ φ (ρ.pushBound a)) (t.eval ρ)
  case exists_elimination s φ ψ =>
    rw [𝔹.valid_imp_iff, value_forall, value_exists, 𝔹.le_imp_iff, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
    intro a
    have h := 𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.iInf_le
      (fun b => value 𝔹 ℳ (.imp φ (ψ.weakenFree s)) (ρ.pushFree b)) a)) (𝔹.meet_le_right _ _)
    simpa only [value_weaken] using h
  case equality_substitution s t t' φ =>
    rw [𝔹.valid_imp_iff, value_equal, value_instantiate, value_instantiate, 𝔹.le_imp_iff]
    apply (value_congr 𝔹 ℳ L φ _ _ ?_).1
    constructor
    · intro s i
      cases i with
      | here => exact 𝔹.le_refl _
      | there i => nomatch i
    · intro s i
      change 𝔹.le _ (ℳ.eqv (ρ.freeVal i) (ρ.freeVal i))
      rw [L.eq_refl]; exact 𝔹.le_top _
  case equality_reflexivity t =>
    rw [value_equal, L.eq_refl]; exact 𝔹.le_refl _

abbrev background : Sem_background σ where
  context := (algebra 𝔹 ℳ).toSem_context
  valid p := ∀ ρ, 𝔹.le 𝔹.top (p ρ)

abbrev model : Sem_model (background 𝔹 ℳ) where
  app := (algebra 𝔹 ℳ).app
  rel := (algebra 𝔹 ℳ).rel

/-- 已证明的布尔背景六规则证书。 -/
theorem rules (L : BV_laws 𝔹.toBA_alg ℳ) : Sem_rules (model 𝔹 ℳ) where
  axiom_valid h := axiom_valid 𝔹 ℳ L h
  sentence_lift {f} {φ} h ρ := by
    change 𝔹.le 𝔹.top (value 𝔹 ℳ φ.fromSentence ρ)
    rw [value_sentence]; exact h FirstOrder.Env.empty
  mp h k ρ := 𝔹.imp_use (k ρ) (h ρ)
  generalize {f} {s} {φ} h ρ := by
    change 𝔹.le 𝔹.top (value 𝔹 ℳ (φ.forallFreeTop s) ρ)
    rw [value_forall, 𝔹.le_iInf_iff]; exact fun a => h (ρ.pushFree a)
  strengthen {f} {s} {φ} h ρ := by
    obtain ⟨a⟩ := ℳ.nonempty s
    have k := h (ρ.pushFree a)
    change 𝔹.le 𝔹.top (value 𝔹 ℳ (φ.weakenFree s) (ρ.pushFree a)) at k
    rwa [value_weaken] at k
  substitute {f} {f'} θ {φ} h ρ := by
    change 𝔹.le 𝔹.top (value 𝔹 ℳ (φ.substituteFree θ) ρ)
    rw [Formula.substituteFree, value_substitute]
    exact h (ρ.pullback (Substitution.free_map θ))

end YesMetaZFC.Model.Boolean.BV_str
