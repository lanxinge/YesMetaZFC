import YesMetaZFC.Automation.ObjectProofNode
import YesMetaZFC.Automation.ObjectLocalDecisionSemantics

/-! # 六类证明节点的内部局部查询语义 -/
namespace YesMetaZFC.Automation.ObjectProofNode
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open RelationalTranslation ObjectHornSemantics NaturalRosserSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {T : SetTheory}

theorem localTest_satisfies (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (axiomTest : ObjectCheckedTrace.LocalTest T) (row : 𝒩.Carrier .set) :
    (localTest C S hSuccessor hPower hInfinity axiomTest).condition.body.satisfies
      (templateEnv (.cons row .nil)) ↔
      ∃ shape ∈ shapes, ∃ values : Fin shape.arity → 𝒩.Carrier .set,
        (∀ i, mem 𝒩 (values i) (𝒩.funcInterp .successor (.cons row .nil))) ∧
        row = exprValue 𝒩 values shape.head ∧
        ∀ query ∈ shape.queries,
          (queryTest C S hSuccessor hPower hInfinity axiomTest query.1).condition.body.satisfies
            (templateEnv (.cons (exprValue 𝒩 values query.2) .nil)) := by
  change (ObjectLocalDecision.template _).body.satisfies _ ↔ _
  rw [ObjectLocalDecision.template_satisfies]
  constructor
  · rintro ⟨rule, hRule, h⟩
    obtain ⟨shape, hShape, rfl⟩ := List.mem_map.mp hRule
    obtain ⟨values, hBound, hHead, hQueries⟩ := (local_rule_satisfies _ _).mp h
    exact ⟨shape, hShape, values, hBound, hHead,
      fun query hq => hQueries _ (List.mem_map.mpr ⟨query,hq,rfl⟩)⟩
  · rintro ⟨shape, hShape, values, hBound, hHead, hQueries⟩
    refine ⟨_, List.mem_map.mpr ⟨shape,hShape,rfl⟩,
      (local_rule_satisfies _ _).mpr ⟨values,hBound,hHead,?_⟩⟩
    intro query hq
    obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hq
    exact hQueries original hOriginal

end YesMetaZFC.Automation.ObjectProofNode
