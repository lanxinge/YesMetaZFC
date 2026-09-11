import YesMetaZFC.Model.ZFC.Pure.PureAllSchemaStage

/-! # 基础逻辑公理集合及内部闭包

十二个模式的并集先由纯分离构造。全称闭合生成算子在内部 ω 上单调，
其最小不动点给出逻辑公理集合；最小性的唯一性不被误报为任意递归解释的唯一性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalClosure
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureAllSchemaStage.expansion hℳ

def baseCondition : Formula S [] [s] := base_logical_axiom_condition (.fvar .here)
def baseMember : Formula ℒ [] [setSort] := openFormula PureAllSchemaStage.interpretation baseCondition
def baseGraph : Formula ℒ [] [setSort] := PureFunctionDefinitions.comprehension baseMember

theorem base_condition_bounded (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ)
    (h : baseCondition.satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s])) :
    membership ℳ code (PureNaturalInduction.omega hℳ) := by
  change membership ℳ code (PureAllSchemaStage.oldValue hℳ .implicationDistribution) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .selfImplication) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .weakening) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .contradiction) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .classical) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .explosion) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .caseAnalysis) ∨
    membership ℳ code (PureAllSchemaStage.value hℳ .specialization) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .quantifierDistribution) ∨
    membership ℳ code (PureAllSchemaStage.value hℳ .vacuousQuantifier) ∨
    membership ℳ code (PureAllSchemaStage.value hℳ .equalitySubstitution) ∨
    membership ℳ code (PureAllSchemaStage.oldValue hℳ .equalityReflexivity) at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · exact PureAllSchemaStage.old_member_bounded hℳ .implicationDistribution code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .selfImplication code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .weakening code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .contradiction code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .classical code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .explosion code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .caseAnalysis code h
  · exact PureAllSchemaStage.member_bounded hℳ .specialization code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .quantifierDistribution code h
  · exact PureAllSchemaStage.member_bounded hℳ .vacuousQuantifier code h
  · exact PureAllSchemaStage.member_bounded hℳ .equalitySubstitution code h
  · exact PureAllSchemaStage.old_member_bounded hℳ .equalityReflexivity code h

theorem base_bounded (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ)
    (h : baseMember.satisfies (templateEnv (.cons code .nil))) : membership ℳ code (PureNaturalInduction.omega hℳ) :=
  base_condition_bounded hℳ code ((openFormula_correct (E hℳ) (PureAllSchemaStage.realizes hℳ) baseCondition (.cons code .nil)).mp h)

theorem base_functional (hℳ : Theory.Models ℳ theory) :
    ∃ output : Carrier ℳ, baseGraph.satisfies (templateEnv (.cons output .nil)) ∧
      ∀ other, baseGraph.satisfies (templateEnv (.cons other .nil)) → other = output :=
  PureSeparation.bounded_functional hℳ baseMember .nil (PureNaturalInduction.omega hℳ) (base_bounded hℳ)

theorem base_correct (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    baseGraph.satisfies (templateEnv (.cons output .nil)) ↔
      ∀ code, membership ℳ code output ↔ baseCondition.satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s]) := by
  apply (PureFunctionDefinitions.comprehension_correct baseMember .nil output).trans
  apply forall_congr'; intro code
  exact iff_congr Iff.rfl (openFormula_correct (E hℳ) (PureAllSchemaStage.realizes hℳ) baseCondition (.cons code .nil))

def generation : Formula S [] [s,s] := logical_axiom_code_generation_condition (.fvar (.there .here)) (.fvar .here)
def body : Formula ℒ [] [setSort,setSort] := openFormula PureAllSchemaStage.interpretation generation
def logicalGraph : Formula ℒ [] [setSort] := PureLeastFixedPoint.graph body

def closureSource : Formula S [] [s,s,s] := canonical_forall_closure_code_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def Closure (hℳ : Theory.Models ℳ theory) (source index target : Carrier ℳ) : Prop :=
  closureSource.satisfies
    (templateEnv (.cons source (.cons index (.cons target .nil))) : Env (E hℳ).model [] [s,s,s])

/-- 生成步骤的语义先在抽象源结构中化简。 -/
theorem generation_satisfaction (𝒩 : Structure.{0,0,0,x} S) (state code : 𝒩.Carrier s) :
    generation.satisfies (templateEnv (.cons code (.cons state .nil)) : Env 𝒩 [] [s,s]) ↔
      baseCondition.satisfies (templateEnv (.cons code .nil) : Env 𝒩 [] [s]) ∨
        ∃ source index, 𝒩.relInterp .membership (.cons source (.cons state .nil)) ∧
          closureSource.satisfies (templateEnv (.cons source (.cons index (.cons code .nil))) : Env 𝒩 [] [s,s,s]) := by
  rfl

theorem body_correct (hℳ : Theory.Models ℳ theory) (state code : Carrier ℳ) :
    PureLeastFixedPoint.Holds body .nil state code ↔
      baseCondition.satisfies (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s]) ∨
        ∃ source index, membership ℳ source state ∧ Closure hℳ source index code := by
  apply (openFormula_correct (E hℳ) (PureAllSchemaStage.realizes hℳ) generation (.cons code (.cons state .nil))).trans
  exact generation_satisfaction (E hℳ).model state code

theorem body_mono (hℳ : Theory.Models ℳ theory) (first second : Carrier ℳ)
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second) (code : Carrier ℳ) :
    PureLeastFixedPoint.Holds body .nil first code → PureLeastFixedPoint.Holds body .nil second code := by
  intro h
  apply (body_correct hℳ second code).mpr
  rcases (body_correct hℳ first code).mp h with h | ⟨source,index,hMember,hClosure⟩
  · exact Or.inl h
  · exact Or.inr ⟨source,index,hSubset source hMember,hClosure⟩

theorem syntax_map_values {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues PureAllSchemaStage.interpretation args = mapValues PureSyntaxStage.interpretation args := rfl

theorem universal_bounded (hℳ : Theory.Models ℳ theory) (code : Carrier ℳ) :
    membership ℳ ((universal_formula_code_term (.fvar .here)).eval (templateEnv (.cons code .nil) : Env (E hℳ).model [] [s])) (PureNaturalInduction.omega hℳ) := by
  let claim : Formula S [] [s] := membership_formula (universal_formula_code_term (.fvar .here)) omega_term
  have hOld : claim.satisfies (templateEnv (.cons code .nil) : Env (PureSyntaxStage.expansion hℳ).model [] [s]) := by
    have hOmega : (PureSyntaxStage.expansion hℳ).function .omega .nil = PureNaturalInduction.omega hℳ := PureSyntaxOperator.omega_eq hℳ
    change membership ℳ ((universal_formula_code_term (.fvar .here)).eval (templateEnv (.cons code .nil) : Env (PureSyntaxStage.expansion hℳ).model [] [s])) ((PureSyntaxStage.expansion hℳ).function .omega .nil)
    rw [hOmega]
    exact PureTotalCodeBounds.node hℳ (templateEnv (.cons code .nil) : Env (PureSyntaxStage.expansion hℳ).model [] [s]) .universal [(.fvar .here)]
  have hPure := (openFormula_correct (PureSyntaxStage.expansion hℳ) (PureSyntaxStage.realizes hℳ) claim (.cons code .nil)).mpr hOld
  have hNew := openFormula_correct (E hℳ) (PureAllSchemaStage.realizes hℳ) claim (.cons code .nil)
  have hTranslate : openFormula PureAllSchemaStage.interpretation claim = openFormula PureSyntaxStage.interpretation claim :=
    openFormula_congr PureSyntaxStage.interpretation PureAllSchemaStage.interpretation.function PureAllSchemaStage.interpretation.relation
      PureSyntaxStage.functionCovered PureSyntaxStage.relationCovered
      (by intro symbol h; cases symbol <;> first | rfl | contradiction)
      (by intro symbol h; cases symbol <;> first | rfl | contradiction) claim rfl
  rw [hTranslate,syntax_map_values] at hNew
  have hResult := hNew.mp hPure
  change membership ℳ _ ((PureAllSchemaStage.expansion hℳ).function .omega .nil) at hResult
  exact PureAllSchemaStage.omega_eq hℳ ▸ hResult

theorem closure_witness (𝒩 : Structure.{0,0,0,x} S) (source index target : 𝒩.Carrier s)
    (h : closureSource.satisfies (templateEnv (.cons source (.cons index (.cons target .nil))) : Env 𝒩 [] [s,s,s])) :
    ∃ code, target = (universal_formula_code_term (.fvar .here)).eval (templateEnv (.cons code .nil) : Env 𝒩 [] [s]) := by
  change (∃ code, _ ∧ (_ ∧ target = (universal_formula_code_term (.fvar .here)).eval
    (templateEnv (.cons code .nil) : Env 𝒩 [] [s]))) at h
  obtain ⟨code,_,_,hEq⟩ := h
  exact ⟨code,hEq⟩

theorem closure_bounded (hℳ : Theory.Models ℳ theory) (source index target : Carrier ℳ)
    (h : Closure hℳ source index target) : membership ℳ target (PureNaturalInduction.omega hℳ) := by
  obtain ⟨code,rfl⟩ := closure_witness (E hℳ).model source index target h
  exact universal_bounded hℳ code

theorem body_bounded (hℳ : Theory.Models ℳ theory) (state code : Carrier ℳ)
    (h : PureLeastFixedPoint.Holds body .nil state code) : membership ℳ code (PureNaturalInduction.omega hℳ) := by
  rcases (body_correct hℳ state code).mp h with h | ⟨source,index,_,hClosure⟩
  · exact base_condition_bounded hℳ code h
  · exact closure_bounded hℳ source index code hClosure

theorem logical_functional (hℳ : Theory.Models ℳ theory) :
    ∃ output : Carrier ℳ, logicalGraph.satisfies (templateEnv (.cons output .nil)) ∧
      ∀ other, logicalGraph.satisfies (templateEnv (.cons other .nil)) → other = output :=
  PureLeastFixedPoint.functional hℳ body .nil (PureNaturalInduction.omega hℳ) (body_bounded hℳ)

theorem logical_fixed (hℳ : Theory.Models ℳ theory) {output : Carrier ℳ}
    (h : logicalGraph.satisfies (templateEnv (.cons output .nil))) (code : Carrier ℳ) :
    membership ℳ code output ↔ generation.satisfies (templateEnv (.cons code (.cons output .nil)) : Env (E hℳ).model [] [s,s]) :=
  ((PureLeastFixedPoint.fixed hℳ body .nil (PureNaturalInduction.omega hℳ) (body_bounded hℳ) (body_mono hℳ) h).1 code).trans
    (openFormula_correct (E hℳ) (PureAllSchemaStage.realizes hℳ) generation (.cons code (.cons output .nil)))

theorem dependencies_covered : formulaCovered PureAllSchemaStage.functionCovered PureAllSchemaStage.relationCovered generation = true := rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLogicalClosure
