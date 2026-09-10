import YesMetaZFC.Automation.ObjectHornSemantics

/-! # 局部规则表的模型语义入口 -/
namespace YesMetaZFC.Automation.ObjectLocalDecision
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {T : SetTheory}

theorem template_satisfies (rules : List (Rule T)) (row : 𝒩.Carrier .set) :
    (template rules).body.satisfies (templateEnv (.cons row .nil)) ↔
      ∃ rule ∈ rules, rule.template.body.satisfies (templateEnv (.cons row .nil)) := by
  rw [template, anyOf_satisfies]
  constructor
  · rintro ⟨formula, hFormula, h⟩
    obtain ⟨rule, hRule, rfl⟩ := List.mem_map.mp hFormula
    exact ⟨rule, hRule, h⟩
  · rintro ⟨rule, hRule, h⟩
    exact ⟨_, List.mem_map.mpr ⟨rule, hRule, rfl⟩, h⟩

end YesMetaZFC.Automation.ObjectLocalDecision
