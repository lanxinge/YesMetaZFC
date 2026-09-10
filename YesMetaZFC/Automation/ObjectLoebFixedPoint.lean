import YesMetaZFC.Automation.ObjectDiagonalFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-! # 原证明图与 quotation 下的 Löb 固定点 -/
namespace YesMetaZFC.Automation.ObjectLoeb
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def reflectionTemplate_m (G : Delta0ProofGraph) (φ : SetSentence) : FormulaTemplate.Unary :=
  ⟨G.provability (.fvar .here) ⟶ₘ φ.weakenFree SetSort.set⟩

theorem reflection_apply_m (G : Delta0ProofGraph) (φ : SetSentence) (s : SetOpenTerm []) :
    reflectionTemplate_m G φ s = (G.provability s ⟶ₘ φ) := by
  unfold reflectionTemplate_m FormulaTemplate.apply_one FormulaTemplate.instantiate
  simp only [Formula.substituteMapped]
  congr 1
  · simp only [Delta0ProofGraph.provability, Formula.substituteMapped,
      FormulaTemplate.apply_two_substituteMapped, Term.substituteMapped,
      Term.substituteMapped_weakenBound, VariableSubstitution.liftBound,
      VariableSubstitution.cons]
  · have h₁ : (VariableSubstitution.empty : VariableSubstitution signature [] [] []) =
        (fun {τ} => VariableSubstitution.boundId (sort := τ)) := by
      funext τ x
      cases x
    have h₂ : (VariableSubstitution.cons s VariableSubstitution.empty :
        VariableSubstitution signature [SetSort.set] [] []) =
        (fun {τ} => VariableSubstitution.instantiateFreeTop s (sort := τ)) := by
      funext τ x
      cases x with
      | here => rfl
      | there x => cases x
    rw [h₂, h₁]
    exact Formula.substituteMapped_weakenFree_instantiateFreeTop SetSort.set s φ

/-- 具体固定点，保持原码域及结构 quotation。 -/
def fixedPoint_m (D : Delta0CodeDomain) (G : Delta0ProofGraph) (φ : SetSentence) : SetSentence :=
  ObjectDiagonal.fixedPoint D (reflectionTemplate_m G φ)

theorem fixed_point_m {T : SetTheory} (S : ObjectDiagonal.Support T)
    (G : Delta0ProofGraph) (φ : SetSentence) :
    Derives T [] (fixedPoint_m S.core.code_domain G φ ↔ₘ
      (G.provability (IntrinsicQuotation.quote (fixedPoint_m S.core.code_domain G φ)) ⟶ₘ φ)) := by
  simpa only [fixedPoint_m, reflection_apply_m] using
    ObjectDiagonal.fixedPoint_spec S (reflectionTemplate_m G φ)

end YesMetaZFC.Automation.ObjectLoeb
