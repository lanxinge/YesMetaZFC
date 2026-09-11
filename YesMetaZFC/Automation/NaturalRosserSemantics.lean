import YesMetaZFC.Automation.NaturalProofPresentation
import YesMetaZFC.Model.Interpretation.RelationalEnvironment

/-! # 自然数证明图的 Rosser 比较语义

模板语义先归约到参数值。内部 ω 传递且包含于比较码域时，自然数包装使比较式
精确成为自然数见证及其自然数初始段上的原证明图，不要求外部标准性。
-/
namespace YesMetaZFC.Automation.NaturalRosserSemantics
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev mem (𝒩 : Structure.{0,0,0,x} signature) (a b : 𝒩.Carrier .set) :=
  𝒩.relInterp .membership (.cons a (.cons b .nil))
abbrev omega (𝒩 : Structure.{0,0,0,x} signature) := 𝒩.funcInterp .omega .nil

theorem unary_satisfies (template : FormulaTemplate.Unary)
    {bound free : SetContext} (env : Env 𝒩 bound free) (term : SetTerm bound free) :
    (template term).satisfies env ↔ template.body.satisfies (templateEnv (.cons (term.eval env) .nil)) := by
  have hForm : template term = applyTemplate template.body (.cons term .nil) := by
    have hSub : (VariableSubstitution.cons term VariableSubstitution.empty :
        VariableSubstitution signature [.set] bound free) =
        (fun {_sort} entry => argumentsSubstitution (.cons term .nil) entry) := by
      funext sort entry
      cases entry with
      | here => rfl
      | there previous => cases previous
    exact congrArg (fun fs : VariableSubstitution signature [.set] bound free =>
      template.body.substituteMapped VariableSubstitution.empty fs) hSub
  rw [hForm]
  exact applyTemplate_satisfies env template.body (.cons term .nil)

theorem binary_satisfies (template : FormulaTemplate.Binary)
    {bound free : SetContext} (env : Env 𝒩 bound free) (left right : SetTerm bound free) :
    (template left right).satisfies env ↔
      template.body.satisfies (templateEnv (.cons (left.eval env) (.cons (right.eval env) .nil))) := by
  have hForm : template left right = applyTemplate template.body (.cons left (.cons right .nil)) := by
    have hSub : (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty) :
        VariableSubstitution signature [.set,.set] bound free) =
        (fun {_sort} entry => argumentsSubstitution (.cons left (.cons right .nil)) entry) := by
      funext sort entry
      cases entry with
      | here => rfl
      | there previous => cases previous with
        | here => rfl
        | there previous => cases previous
    exact congrArg (fun fs : VariableSubstitution signature [.set,.set] bound free =>
      template.body.substituteMapped VariableSubstitution.empty fs) hSub
  rw [hForm]
  exact applyTemplate_satisfies env template.body (.cons left (.cons right .nil))

theorem comparison_satisfies (G : Delta0ProofGraph) (D : Delta0CodeDomain)
    {bound free : SetContext} (env : Env 𝒩 bound free) (left right : SetTerm bound free) :
    (G.comparison D left right).satisfies env ↔
      ∃ code, D.condition.body.satisfies (templateEnv (.cons code .nil) : Env 𝒩 [] [.set]) ∧
        G.condition.body.satisfies (templateEnv (.cons code (.cons (left.eval env) .nil))) ∧
        ∀ smaller, mem 𝒩 smaller code →
          ¬ G.condition.body.satisfies (templateEnv (.cons smaller (.cons (right.eval env) .nil))) := by
  simp only [Delta0ProofGraph.comparison, Delta0ProofGraph.no_smaller,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, Formula.satisfies,
    unary_satisfies, binary_satisfies, Term.eval_weakenBound]
  rfl

theorem natural_graph_satisfies (G : Delta0ProofGraph) (code conclusion : 𝒩.Carrier .set) :
    (NaturalProofPresentation.graph G).condition.body.satisfies
      (templateEnv (.cons code (.cons conclusion .nil))) ↔
      mem 𝒩 code (omega 𝒩) ∧
        G.condition.body.satisfies (templateEnv (.cons code (.cons conclusion .nil))) := by
  simp only [NaturalProofPresentation.graph, NaturalProofPresentation.template,
    Formula.satisfies, binary_satisfies]
  rfl

/-- 外层见证和全部更小码只遍历内部自然数，旧码域不再增加约束。 -/
theorem natural_comparison_satisfies (G : Delta0ProofGraph) (D : Delta0CodeDomain)
    (hDomain : ∀ code, mem 𝒩 code (omega 𝒩) →
      D.condition.body.satisfies (templateEnv (.cons code .nil) : Env 𝒩 [] [.set]))
    (hTransitive : ∀ code smaller, mem 𝒩 code (omega 𝒩) → mem 𝒩 smaller code →
      mem 𝒩 smaller (omega 𝒩))
    {bound free : SetContext} (env : Env 𝒩 bound free) (left right : SetTerm bound free) :
    ((NaturalProofPresentation.graph G).comparison D left right).satisfies env ↔
      ∃ code, mem 𝒩 code (omega 𝒩) ∧
        G.condition.body.satisfies (templateEnv (.cons code (.cons (left.eval env) .nil))) ∧
        ∀ smaller, mem 𝒩 smaller code →
          ¬ G.condition.body.satisfies (templateEnv (.cons smaller (.cons (right.eval env) .nil))) := by
  rw [comparison_satisfies]
  simp only [NaturalProofPresentation.graph, NaturalProofPresentation.template,
    Formula.satisfies, binary_satisfies]
  constructor
  · rintro ⟨code, _, ⟨hCode, hProof⟩, hSmaller⟩
    exact ⟨code, hCode, hProof, fun smaller hLess hProof =>
      hSmaller smaller hLess ⟨hTransitive code smaller hCode hLess, hProof⟩⟩
  · rintro ⟨code, hCode, hProof, hSmaller⟩
    exact ⟨code, hDomain code hCode, ⟨hCode, hProof⟩,
      fun smaller hLess hProof => hSmaller smaller hLess hProof.2⟩

end YesMetaZFC.Automation.NaturalRosserSemantics
