import YesMetaZFC.Model.ZFC.Pure.PureArithmeticSpecifications

/-! # Gödel 配对的纯定义

按原两分支算术公式给出配对值。自然数三歧性保证恰有一个分支适用，
算术封闭性保证输出仍在模型内部 ω 中。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureGodelPairing
open PureModel PureNaturalInduction PureArithmeticStage PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable abbrev two (hℳ : Theory.Models ℳ theory) : Carrier ℳ := succ hℳ (succ hℳ (zero hℳ))
noncomputable def firstBranch (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) : Carrier ℳ :=
  arithmetic hℳ .addition (arithmetic hℳ .exponentiation right (two hℳ)) left
noncomputable def secondBranch (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) : Carrier ℳ :=
  arithmetic hℳ .addition (arithmetic hℳ .addition (arithmetic hℳ .exponentiation left (two hℳ)) left) right

def specification : Formula S [] [s,s,s] :=
  Nonlogical.BasicSetTheory.godel_pairing_condition (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

theorem specification_correct (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    specification.satisfies
      (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureArithmeticStage.expansion hℳ).model [] [s,s,s]) ↔
      membership ℳ output (omega hℳ) ∧ (membership ℳ left right → output = firstBranch hℳ left right) ∧
        ((right = left ∨ membership ℳ right left) → output = secondBranch hℳ left right) := by
  simp only [specification,Nonlogical.BasicSetTheory.godel_pairing_condition,
    Nonlogical.BasicSetTheory.natural_leq_condition,Formula.satisfies,
    Nonlogical.BasicSetTheory.membership_formula,Nonlogical.BasicSetTheory.natural_exponentiation_term,
    Nonlogical.BasicSetTheory.natural_addition_term,Nonlogical.BasicSetTheory.successor_term,
    Nonlogical.BasicSetTheory.empty_set_term,Nonlogical.BasicSetTheory.omega_term,
    Term.eval,Arguments.eval,Expansion.model,omega_eq hℳ,zero_eq hℳ,succ_eq hℳ,membership_correct hℳ]
  rfl

def body : Formula ℒ [] [setSort,setSort,setSort] :=
  .conj PureOrdinalArithmetic.naturalGuard (openFormula PureArithmeticStage.interpretation specification)
def graph : Formula ℒ [] [setSort,setSort,setSort] :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula body PureRelationFunctions.emptyFallback

theorem body_correct (hℳ : Theory.Models ℳ theory) (left right output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      (membership ℳ left (omega hℳ) ∧ membership ℳ right (omega hℳ)) ∧
      membership ℳ output (omega hℳ) ∧ (membership ℳ left right → output = firstBranch hℳ left right) ∧
        ((right = left ∨ membership ℳ right left) → output = secondBranch hℳ left right) :=
  and_congr (PureOrdinalArithmetic.guard_correct hℳ output left right)
    ((openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ)
      specification (.cons output (.cons left (.cons right .nil)))).trans (specification_correct hℳ left right output))

theorem compare (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    membership ℳ left right ∨ right = left ∨ membership ℳ right left := by
  rcases (omega_project hℳ).membershipWellOrder (project_modelsZF hℳ) |>.linear.compare left hLeft right hRight with hEqual | hLess | hGreater
  · exact Or.inr (Or.inl ((project_models hℳ).1.eq_of_same_members left right hEqual).symm)
  · exact Or.inl hLess
  · exact Or.inr (Or.inr hGreater)

theorem branches_disjoint (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hLess : membership ℳ left right)
    (hOther : right = left ∨ membership ℳ right left) : False := by
  have hOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) left hLeft
  rcases hOther with hEqual | hReverse
  · have hSelf : membership ℳ left left := hEqual ▸ hLess
    exact hOrdinal.wellOrder.linear.irrefl left hSelf hSelf
  · have hSelf := hOrdinal.transitive right hReverse left hLess
    exact hOrdinal.wellOrder.linear.irrefl left hSelf hSelf

theorem exists_body (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    ∃ output, body.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) := by
  classical
  have hTwo := succ_mem hℳ (succ_mem hℳ (zero_mem hℳ))
  by_cases hLess : membership ℳ left right
  · refine ⟨firstBranch hℳ left right,(body_correct hℳ left right _).mpr ⟨⟨hLeft,hRight⟩,?_,fun _ => rfl,?_⟩⟩
    · exact arithmetic_closed hℳ .addition (arithmetic_closed hℳ .exponentiation hRight hTwo) hLeft
    · intro hOther
      exact False.elim (branches_disjoint hℳ hLeft hLess hOther)
  · refine ⟨secondBranch hℳ left right,(body_correct hℳ left right _).mpr ⟨⟨hLeft,hRight⟩,?_,fun h => False.elim (hLess h),fun _ => rfl⟩⟩
    exact arithmetic_closed hℳ .addition
      (arithmetic_closed hℳ .addition (arithmetic_closed hℳ .exponentiation hLeft hTwo) hLeft) hRight

theorem functional (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons left (.cons right .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ body (.cons left (.cons right .nil))
  intro first second hFirst hSecond
  have hF := (body_correct hℳ left right first).mp hFirst
  have hS := (body_correct hℳ left right second).mp hSecond
  rcases compare hℳ hF.1.1 hF.1.2 with hLess | hOther
  · exact (hF.2.2.1 hLess).trans (hS.2.2.1 hLess).symm
  · exact (hF.2.2.2 hOther).trans (hS.2.2.2 hOther).symm

theorem agrees (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (PureArithmeticStage.expansion hℳ).model [] [s,s,s]) := by
  apply (PureRelationFunctions.totalized_agrees body (.cons left (.cons right .nil)) (exists_body hℳ hLeft hRight) output).trans
  exact (body_correct hℳ left right output).trans
    (Iff.trans ⟨And.right,fun h => ⟨⟨hLeft,hRight⟩,h⟩⟩ (specification_correct hℳ left right output).symm)

theorem dependencies_covered : formulaCovered PureArithmeticStage.functionCovered
    PureNaturalRelations.relationCovered specification = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureGodelPairing
