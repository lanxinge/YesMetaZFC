import YesMetaZFC.Model.ZFC.Pure.PureSourceInfinity

/-! # 后继链码域的边界及内部自然数覆盖

后继链码域不等于模型内部的自然数集合：ω 自身属于前者而不属于后者。因而不能
仅从这个码域条件推出配数定义所需的自然数 guard。当前 Rosser 已由证明图直接
要求输入码属于 ω；`natural_in_domain` 证明旧码域在这些输入上冗余。
本模块没有构造整个原理论的反模型，也没有否定 `PureRosser.Agreement`。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.RosserDomainBoundary
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInfinity
open _root_.YesMetaZFC.Automation.RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem domain_semantics (𝒩 : Structure.{0,0,0,x} signature) (point : 𝒩.Carrier .set) :
    (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
      (templateEnv (.cons point .nil) : Env 𝒩 [] [.set]) ↔
      (point = z 𝒩 ∨ mem 𝒩 (z 𝒩) point) ∧
        ∀ element, mem 𝒩 element point →
          suc 𝒩 element = point ∨ mem 𝒩 (suc 𝒩 element) point := Iff.rfl

/-- 码域本身只依赖已确定的空集、后继及隶属，故在规范重扩张前后保持。 -/
theorem domain_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (point : 𝒩.Carrier .set) :
    (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
      (templateEnv (.cons point .nil) : Env 𝒩 [] [.set]) ↔
    (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
      (templateEnv (.cons point .nil) : Env (PureSourceNumerals.canonical h𝒩) [] [.set]) := by
  refine (domain_semantics 𝒩 point).trans
    (Iff.trans ?_ (domain_semantics (PureSourceNumerals.canonical h𝒩) point).symm)
  change ((point = z 𝒩 ∨ mem 𝒩 (z 𝒩) point) ∧
    ∀ element, mem 𝒩 element point → suc 𝒩 element = point ∨ mem 𝒩 (suc 𝒩 element) point) ↔
    ((point = z (PureSourceNumerals.canonical h𝒩) ∨
      mem 𝒩 (z (PureSourceNumerals.canonical h𝒩)) point) ∧
    ∀ element, mem 𝒩 element point →
      suc (PureSourceNumerals.canonical h𝒩) element = point ∨
        mem 𝒩 (suc (PureSourceNumerals.canonical h𝒩) element) point)
  simp only [PureSourceNumerals.empty_agrees h𝒩, PureSourceNumerals.successor_agrees h𝒩]
  rfl

theorem omega_in_domain (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
      (templateEnv (.cons (w 𝒩) .nil) : Env 𝒩 [] [.set]) := by
  have h := omega_closed h𝒩
  exact (domain_semantics 𝒩 (w 𝒩)).mpr
    ⟨Or.inr h.1, fun element hMember => Or.inr (h.2 element hMember)⟩

theorem omega_not_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    ¬ mem 𝒩 (w 𝒩) (w 𝒩) :=
  _root_.YesMetaZFC.SetTheory.KP.mem_irrefl_d
    (_root_.YesMetaZFC.SetTheory.ZF.modelsKP
      (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩))) (w 𝒩)

/-- 这是任意原理论模型中的实际反例，不是标准模型上的样本检查。 -/
theorem domain_not_subset_naturals (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    ¬ (∀ point : 𝒩.Carrier .set,
      (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
        (templateEnv (.cons point .nil) : Env 𝒩 [] [.set]) → mem 𝒩 point (w 𝒩)) :=
  fun h => omega_not_natural h𝒩 (h (w 𝒩) (omega_in_domain h𝒩))

/-- 内部自然数全部满足旧码域；因此新证明图上的该码域约束是冗余的。 -/
theorem natural_in_domain (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {number : 𝒩.Carrier .set} (hNumber : mem 𝒩 number (w 𝒩)) :
    (successor_code_domain (.fvar .here : SetOpenTerm [.set])).satisfies
      (templateEnv (.cons number .nil) : Env 𝒩 [] [.set]) := by
  apply (domain_semantics 𝒩 number).mpr
  constructor
  · rcases natural_compare h𝒩 (omega_closed h𝒩).1 hNumber with hEqual | hLess | hGreater
    · exact Or.inl hEqual.symm
    · exact Or.inr hLess
    · exact False.elim (PureSourceNumerals.empty_spec h𝒩 number hGreater)
  · intro element hElement
    have hSuccessor := (omega_closed h𝒩).2 element (member_natural h𝒩 hNumber hElement)
    rcases natural_compare h𝒩 hSuccessor hNumber with hEqual | hLess | hGreater
    · exact Or.inl hEqual
    · exact Or.inr hLess
    · have hOrdinal := (omega_project h𝒩).members_areOrdinals
        (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩)) number hNumber
      have hSelf : mem 𝒩 number number := by
        rcases (PureSourceNumerals.successor_spec h𝒩 element number).mp hGreater with h | h
        · exact hOrdinal.transitive element hElement number h
        · exact h ▸ hElement
      exact False.elim (_root_.YesMetaZFC.SetTheory.KP.mem_irrefl_d
        (_root_.YesMetaZFC.SetTheory.ZF.modelsKP
          (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩))) number hSelf)

/-- 非自然数首参数使原配数定义的 guard 为假，整个定义实例自动成立。 -/
theorem pairing_instance_vacuous (𝒩 : Structure.{0,0,0,x} signature)
    (left right output : 𝒩.Carrier .set) (hLeft : ¬ mem 𝒩 left (w 𝒩)) :
    (godel_pairing_definition_instance
      (.fvar .here : SetOpenTerm [.set,.set,.set])
      (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
        (templateEnv (.cons left (.cons right (.cons output .nil)))) :=
  fun hGuard => False.elim (hLeft hGuard.1)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.RosserDomainBoundary
