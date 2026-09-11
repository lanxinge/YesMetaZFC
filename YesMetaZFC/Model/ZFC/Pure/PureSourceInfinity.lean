import YesMetaZFC.Model.ZFC.Pure.PureSourceNumerals

/-! # 任意原模型中的内部 ω 与规范重扩张一致

原归纳集定义先由空集和后继对应传输。原 ω 的归纳核方程随后给出最小性，
从而确定同一个纯隶属最小归纳集；不使用外部自然数归纳覆盖模型的全部自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInfinity
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem inductive_spec (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (source : 𝒩.Carrier .set) :
    𝒩.relInterp .isInductiveSet (.cons source .nil) ↔
      mem 𝒩 (z 𝒩) source ∧ ∀ element, mem 𝒩 element source →
        mem 𝒩 (suc 𝒩 element) source := by
  have hProof := Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
    (infinity_inductive_set_definition_instance_derives (Γ := [])
      (.fvar .here : SetOpenTerm [.set]))
  have h := hProof.sound h𝒩 (templateEnv (.cons source .nil))
    (by intro formula hMember; cases hMember)
  simp only [is_inductive_set_definition_instance, is_inductive_set_condition,
    infinity_condition, Formula.satisfies_forallFreeTop, Formula.satisfies,
    Arguments.eval, Term.eval_weakenFree] at h
  exact h

theorem inductive_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (source : 𝒩.Carrier .set) :
    𝒩.relInterp .isInductiveSet (.cons source .nil) ↔
      (canonical h𝒩).relInterp .isInductiveSet (.cons source .nil) := by
  refine (inductive_spec h𝒩 source).trans
    (Iff.trans ?_ (inductive_spec (PureZFCModels.models (PureZFCModels.reduct_models h𝒩)) source).symm)
  change (mem 𝒩 (z 𝒩) source ∧ ∀ element, mem 𝒩 element source → mem 𝒩 (suc 𝒩 element) source) ↔
    (mem 𝒩 (z (canonical h𝒩)) source ∧ ∀ element, mem 𝒩 element source →
      mem 𝒩 (suc (canonical h𝒩) element) source)
  simp only [empty_agrees h𝒩, successor_agrees h𝒩]

theorem inductive_project (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (source : 𝒩.Carrier .set) :
    𝒩.relInterp .isInductiveSet (.cons source .nil) ↔
      (Project.FirstOrderSemantics.reduct (PureProjectEmbedding.reduct 𝒩)).IsInductive source :=
  (inductive_agrees h𝒩 source).trans
    (PureFinalInfinity.inductive_value (PureZFCModels.reduct_models h𝒩) source)

/-- 原无穷理论保证 ω 包含零且对后继封闭。 -/
theorem omega_closed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    mem 𝒩 (z 𝒩) (w 𝒩) ∧
      ∀ element, mem 𝒩 element (w 𝒩) → mem 𝒩 (suc 𝒩 element) (w 𝒩) := by
  have hProof : Derives intrinsic_zfc_theory [] (infinity_condition (ωₘ : SetTerm [] [])) :=
    Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
      infinity_omega_inductive_condition_derives
  have h := hProof.semantically_entails 𝒩 h𝒩
  simp only [Formula.TrueIn, infinity_condition, Formula.satisfies,
    Formula.satisfies_forallFreeTop] at h
  exact h

/-- 归纳核方程保证原 ω 属于纯隶属语义中的最小归纳集类。 -/
theorem omega_project (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    (Project.FirstOrderSemantics.reduct (PureProjectEmbedding.reduct 𝒩)).IsOmega (w 𝒩) := by
  have hDef := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
    (infinity_omega_definition_instance_derives (Γ := []) (ωₘ : SetTerm [] []))).semantically_entails 𝒩 h𝒩
  change (w 𝒩 = w 𝒩 ↔ 𝒩.relInterp .isInductiveSet (.cons (w 𝒩) .nil) ∧
    𝒩.funcInterp .inductiveCore (.cons (w 𝒩) .nil) = w 𝒩) at hDef
  have hOmega := hDef.mp rfl
  have hAxiom : inductive_core_definition_axiom.TrueIn 𝒩 :=
    h𝒩 _ (intrinsic_zfc_arithmetic_support.contains_infinity (Or.inr (Or.inl rfl)))
  have hCore := (forall_close_iff _).mp hAxiom
    (templateEnv (.cons (w 𝒩) (.cons (w 𝒩) .nil)))
  change (𝒩.relInterp .isInductiveSet (.cons (w 𝒩) .nil) →
    (w 𝒩 = 𝒩.funcInterp .inductiveCore (.cons (w 𝒩) .nil) ↔
      (inductive_core_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons (w 𝒩) (.cons (w 𝒩) .nil)) : Env 𝒩 [] [.set,.set]))) at hCore
  have hMembers := (PureFinalInfinity.core_semantics 𝒩 (w 𝒩) (w 𝒩)).mp
    ((hCore hOmega.1).mp hOmega.2.symm)
  refine ⟨(inductive_project h𝒩 (w 𝒩)).mp hOmega.1, ?_⟩
  intro source hSource element hElement
  exact ((hMembers element).mp hElement).2 source ((inductive_project h𝒩 source).mpr hSource)

theorem omega_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    w 𝒩 = w (canonical h𝒩) :=
  ((PureCompletedStage.realizes (PureZFCModels.reduct_models h𝒩)).function .omega .nil (w 𝒩)).mp
    ((PureOmegaAndReverse.omega_correct (PureZFCModels.reduct_models h𝒩) (w 𝒩)).mpr (omega_project h𝒩))

/-- 所有内部自然数的元素仍为内部自然数，包括非标准初始段中的元素。 -/
theorem member_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {number element : 𝒩.Carrier .set}
    (hNumber : mem 𝒩 number (w 𝒩)) (hElement : mem 𝒩 element number) :
    mem 𝒩 element (w 𝒩) :=
  (omega_project h𝒩).transitive
    (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩)) number hNumber element hElement

theorem natural_compare (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set}
    (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    left = right ∨ mem 𝒩 left right ∨ mem 𝒩 right left := by
  rcases (omega_project h𝒩).membershipWellOrder
    (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩)) |>.linear.compare
      left hLeft right hRight with hEqual | hLess | hGreater
  · exact Or.inl ((PureModel.project_models (PureZFCModels.reduct_models h𝒩)).1.eq_of_same_members
      left right hEqual)
  · exact Or.inr (Or.inl hLess)
  · exact Or.inr (Or.inr hGreater)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInfinity
