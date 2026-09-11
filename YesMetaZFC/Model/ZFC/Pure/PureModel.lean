import YesMetaZFC.Model.FirstOrder.Theory
import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # 裸 ZFC 纯隶属模型中的基础集合构造
目标理论明确是原 Project ZFC 在纯签名 ℒ 中的像。基础存在性直接由原公理解释
得到，后续函数图定义不再把这些性质作为额外支撑公理加入。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureModel
open _root_.YesMetaZFC.SetTheory (PureSetLanguage)
open _root_.YesMetaZFC.SetTheory.Definitional.Project
set_option autoImplicit false
set_option maxRecDepth 4096
universe x

abbrev setSort := _root_.YesMetaZFC.SetTheory.SetSort.set
abbrev theory : Theory ℒ := fo_theory _root_.YesMetaZFC.SetTheory.ZFC
abbrev Carrier (M : Structure.{0, 0, 0, x} ℒ) := M.Carrier setSort

def membership (M : Structure.{0, 0, 0, x} ℒ) (left right : Carrier M) : Prop :=
  M.relInterp _root_.YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))

variable {M : Structure.{0, 0, 0, x} ℒ}

theorem extensionality (hM : Theory.Models M theory) (left right : Carrier M)
    (h : ∀ element, membership M element left ↔ membership M element right) : left = right := by
  have hAx := hM _ ⟨_, _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf .extensionality, rfl⟩
  simp only [Formula.TrueIn, fo_sentence, _root_.YesMetaZFC.SetTheory.Axioms.extensionality,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.ofFormula,
    fo_formula, fo_mem, fo_term, fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.extensionalEq,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.pairArguments] at hAx
  change (∀ left right : Carrier M,
    (∀ element, membership M element left ↔ membership M element right) → left = right) at hAx
  exact hAx left right h

/-- 当前纯语言模型直接接入既有 Project 集合论模型库。 -/
theorem project_models (hM : Theory.Models M theory) :
    (FirstOrderSemantics.reduct M).Models _root_.YesMetaZFC.SetTheory.ZFC :=
  (FirstOrderSemantics.models_iff ⟨extensionality hM⟩ _).mp hM

/-- 原 ZFC 的纯模型保留全部 ZF 公理模式，供集合构造直接消费。 -/
theorem project_modelsZF (hM : Theory.Models M theory) :
    (FirstOrderSemantics.reduct M).Models _root_.YesMetaZFC.SetTheory.ZF :=
  ⟨(project_models hM).1, fun _ h => (project_models hM).2 _ (.zf h)⟩

theorem empty (hM : Theory.Models M theory) :
    ∃ output : Carrier M, ∀ element, ¬ membership M element output := by
  have hAx := hM _ ⟨_, _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf .emptySet, rfl⟩
  simp only [Formula.TrueIn, fo_sentence, _root_.YesMetaZFC.SetTheory.Axioms.emptySet,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.ofFormula,
    fo_formula, fo_mem, fo_term, fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    ] at hAx
  change (∃ output : Carrier M, ∀ element, ¬ membership M element output) at hAx
  exact hAx

theorem pair (hM : Theory.Models M theory) (left right : Carrier M) :
    ∃ output : Carrier M, ∀ element, membership M element output ↔ element = left ∨ element = right := by
  have hAx := hM _ ⟨_, _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf .pairing, rfl⟩
  simp only [Formula.TrueIn, fo_sentence, _root_.YesMetaZFC.SetTheory.Axioms.pairing,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.ofFormula,
    fo_formula, fo_mem, fo_term, fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.extensionalEq,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.pairArguments] at hAx
  change (∀ left right : Carrier M, ∃ output : Carrier M,
    ∀ element, membership M element output ↔ element = left ∨ element = right) at hAx
  exact hAx left right

theorem union (hM : Theory.Models M theory) (family : Carrier M) :
    ∃ output : Carrier M, ∀ element, membership M element output ↔
      ∃ member, membership M member family ∧ membership M element member := by
  have hAx := hM _ ⟨_, _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf .union, rfl⟩
  simp only [Formula.TrueIn, fo_sentence, _root_.YesMetaZFC.SetTheory.Axioms.union,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.ofFormula,
    fo_formula, fo_mem, fo_term, fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.existsMem
    ] at hAx
  change (∀ family : Carrier M, ∃ output : Carrier M,
    ∀ element, membership M element output ↔
      ∃ member, membership M member family ∧ membership M element member) at hAx
  exact hAx family

theorem power (hM : Theory.Models M theory) (input : Carrier M) :
    ∃ output : Carrier M, ∀ subset, membership M subset output ↔
      ∀ element, membership M element subset → membership M element input := by
  have hAx := hM _ ⟨_, _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf .powerSet, rfl⟩
  simp only [Formula.TrueIn, fo_sentence, _root_.YesMetaZFC.SetTheory.Axioms.powerSet,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.ofFormula,
    fo_formula, fo_mem, fo_term, fo_bound_variable, Formula.satisfies, Arguments.eval, Term.eval,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.weaken,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.subset,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.pairArguments] at hAx
  change (∀ input : Carrier M, ∃ output : Carrier M,
    ∀ subset, membership M subset output ↔
      ∀ element, membership M element subset → membership M element input) at hAx
  exact hAx input

theorem singleton (hM : Theory.Models M theory) (input : Carrier M) :
    ∃ output : Carrier M, ∀ element, membership M element output ↔ element = input := by
  obtain ⟨output, hOutput⟩ := pair hM input input
  exact ⟨output, fun element => (hOutput element).trans (Iff.of_eq (or_self _))⟩

/-- 后继集合由配对与并集构造，未新增后继公理。 -/

theorem successor (hM : Theory.Models M theory) (input : Carrier M) :
    ∃ output : Carrier M, ∀ element, membership M element output ↔ membership M element input ∨ element = input := by
  obtain ⟨single, hSingle⟩ := singleton hM input
  obtain ⟨family, hFamily⟩ := pair hM input single
  obtain ⟨output, hOutput⟩ := union hM family
  refine ⟨output, fun element => (hOutput element).trans ?_⟩
  constructor
  · rintro ⟨member, hMember, hElement⟩
    rcases (hFamily member).mp hMember with h | h
    · exact Or.inl (h ▸ hElement)
    · exact Or.inr ((hSingle element).mp (h ▸ hElement))
  · intro h
    rcases h with h | h
    · exact ⟨input, (hFamily input).mpr (Or.inl rfl), h⟩
    · exact ⟨single, (hFamily single).mpr (Or.inr rfl), (hSingle element).mpr h⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureModel
