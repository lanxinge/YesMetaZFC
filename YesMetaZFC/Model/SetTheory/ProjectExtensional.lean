import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.SetTheory.Axioms.ZF

/-! # 原外延性公理与纯语言约化

只读取外延性公理本身，避免在初等子模型和 ZF 反射中借用完整 ZFC 模型。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
open Logic.FirstOrder
universe u

theorem extensional_iff_l {M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ} :
    (fo_sentence SetTheory.Axioms.extensionality).TrueIn M ↔ Extensional (reduct M) := by
  simp only [Formula.TrueIn, fo_sentence, SetTheory.Axioms.extensionality,
    Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
    Project.Term.newest, Project.Term.weaken, Definitional.Term.newest, Definitional.Term.weaken,
    Definitional.Term.rename, Definitional.Term.bind, Project.Formula.extensionalEq,
    Project.Formula.pairArguments]
  change (∀ a b : Carrier M, (∀ c, (reduct M).mem c a ↔ (reduct M).mem c b) → a = b) ↔ _
  exact ⟨fun h => ⟨h⟩, fun h => h.eq_of_same_members⟩

end YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
