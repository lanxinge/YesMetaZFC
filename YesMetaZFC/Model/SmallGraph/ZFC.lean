import YesMetaZFC.Model.SmallGraph.Choice
import YesMetaZFC.Model.SmallGraph.Infinity
import YesMetaZFC.Model.ZFC.Pure.PureModel
import YesMetaZFC.Model.Semantics.Background
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.SetTheory.Collection

/-! # 原生小图模型与裸 ZFC 一致性

载体是已构造的良基小图双模拟商，属于预先固定的 `Type (u+1)`。
原 ZFC 的固定公理及任意有限参数的分离、收集模式逐句核验；一致性直接消费
该实际模型和原 Hilbert 推导可靠性，没有模型存在或一致性前提。
-/

namespace YesMetaZFC.Model.SmallGraph
open SetTheory SetTheory.Definitional.Project
open Logic.FirstOrder (Context)
open Logic.FirstOrder.FormalSystem.ProofT.ZFC
universe u

/-- 小图商上的实际纯一阶结构；没有代表元选择或不可计算数据字段。 -/
def sg_model : Logic.FirstOrder.Structure.{0, 0, 0, u+1} ℒ where
  Carrier _ := SG_set.{u}
  nonempty _ := ⟨SG_set.empty⟩
  funcInterp f := nomatch f
  relInterp | .membership, .cons x (.cons y .nil) => x ∈ y

abbrev sg_structure : SetTheory.Structure.{u+1} := FirstOrderSemantics.reduct sg_model

attribute [local implicit_reducible] sg_model FirstOrderSemantics.reduct
attribute [local simp] sg_structure FirstOrderSemantics.reduct sg_model

theorem sg_extensional : Extensional sg_structure.{u} :=
  ⟨fun _ _ h => SG_set.ext h⟩

attribute [local simp] Formula.satisfies_mem_iff Formula.satisfies_neg_iff
  Formula.satisfies_conj_iff Formula.satisfies_disj_iff Formula.satisfies_imp_iff
  Formula.satisfies_iff_iff Formula.satisfies_forall_iff Formula.satisfies_exists_iff
  Formula.satisfies_subset_iff

/-- 分离模式保留全部参数；只把正文的满足关系用作已经实现的分离谓词。 -/
theorem sg_separation {n : Nat} (φ : UnarySchema n) :
    sg_structure.{u}.SatisfiesSentence (Axioms.Schema.separation φ) := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.Schema.separation, Sentence.forallClosure, Formula.satisfies_forallClosure_iff]
  intro b
  apply (Axioms.Schema.separation_sat_iff_d _ φ).mpr
  exact fun x => SG_set.separation x (fun z =>
    Formula.satisfies (({ bound := b, free := f } : SetTheory.Env sg_structure n).push z) φ.body)

/-- 收集对任意二元正文成立，不附加函数性或唯一性。 -/
theorem sg_collection {n : Nat} (φ : BinarySchema n) :
    sg_structure.{u}.SatisfiesSentence (Axioms.Schema.collection φ) := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.Schema.collection, Sentence.forallClosure, Formula.satisfies_forallClosure_iff]
  intro b
  apply (Axioms.Schema.collection_sat_iff_d _ φ).mpr
  exact fun x => SG_set.collection x (fun a c =>
    Formula.satisfies ((({ bound := b, free := f } : SetTheory.Env sg_structure n).push a).push c)
      φ.body)

/-- 原 Project ZFC 的每条公理在实际小图商中成立。 -/
theorem sg_project_zfc : sg_structure.{u}.Models SetTheory.ZFC := by
  refine ⟨sg_extensional, fun s h => ?_⟩
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  cases h with
  | zf h =>
    cases h with
    | separation φ => exact sg_separation φ f
    | collection φ => exact sg_collection φ f
    | extensionality =>
      simpa [Axioms.extensionality, Sentence.ofFormula,
        Formula.satisfies_extensionalEq_iff_eq sg_extensional] using
        (fun x y (h : ∀ z : SG_set.{u}, z ∈ x ↔ z ∈ y) => SG_set.ext h)
    | emptySet =>
      simpa [Axioms.emptySet, Sentence.ofFormula] using
        (show ∃ x : SG_set.{u}, ∀ z, ¬ z ∈ x from ⟨SG_set.empty, SG_set.not_mem_empty⟩)
    | pairing =>
      simpa [Axioms.pairing, Sentence.ofFormula,
        Formula.satisfies_extensionalEq_iff_eq sg_extensional] using SG_set.pair.{u}
    | union =>
      simpa [Axioms.union, Sentence.ofFormula] using SG_set.union.{u}
    | powerSet =>
      simpa [Axioms.powerSet, Sentence.ofFormula] using SG_set.power.{u}
    | infinity =>
      simpa [Axioms.infinity, Sentence.ofFormula,
        Formula.satisfies_extensionalEq_iff_eq sg_extensional] using
        (Exists.intro SG_set.omega SG_set.infinity.{u})
    | foundation =>
      simpa [Axioms.foundation, Sentence.ofFormula] using SG_set.foundation.{u}
  | choice =>
    simpa [Axioms.choice, Sentence.ofFormula, Formula.extensionalNe,
      Formula.satisfies_extensionalEq_iff_eq sg_extensional] using
      (fun x (h : (∀ a, a ∈ x → ∃ b, b ∈ a) ∧
        ∀ a, a ∈ x → ∀ b, b ∈ x → a ≠ b → ¬ ∃ z, z ∈ a ∧ z ∈ b) =>
          SG_set.choice.{u} x h.1 h.2)

/-- 同一个载体和成员关系满足仓库现有的纯语言裸 ZFC 理论。 -/
theorem sg_models_zfc : Logic.FirstOrder.Theory.Models sg_model.{u} PureModel.theory :=
  (FirstOrderSemantics.models_iff sg_extensional SetTheory.ZFC).mpr sg_project_zfc

/-- Lean 元层由实际小图模型证明原裸 ZFC 一致；无额外数学前提。 -/
theorem zfc_consistent : Logic.FirstOrder.Derives.Consistent PureModel.theory ([] : Context ℒ []) :=
  Native.consistent sg_model.{0} sg_models_zfc

end YesMetaZFC.Model.SmallGraph
