import YesMetaZFC.Model.ZFC.Pure.PureValueOperator

/-! # 项及项列求值关系的纯图

每组结构和赋值参数对应一个内部最小不动点。标签切片分别实现项值与项列值，
原正文中四个参数的保持在后续具体扩张中核验。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueFixedPoint
open PureModel PureNaturalInduction PureValueOperator
open PureSyntaxOperator (Kind tuple)
open PureSyntaxFixedPoint (tuple_injective)
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable def state (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment : Carrier ℳ) : Carrier ℳ :=
  Classical.choose (PureLeastFixedPoint.functional hℳ body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) (ambient hℳ carrier) (body_bounded hℳ carrier interpretation symbols assignment))
theorem state_graph (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment : Carrier ℳ) :
    (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons (state hℳ carrier interpretation symbols assignment) (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))) :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) (ambient hℳ carrier) (body_bounded hℳ carrier interpretation symbols assignment))).1
theorem state_unique (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment : Carrier ℳ) {other : Carrier ℳ}
    (h : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons other (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil))))))) : other = state hℳ carrier interpretation symbols assignment :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) (ambient hℳ carrier) (body_bounded hℳ carrier interpretation symbols assignment))).2 other h

theorem equation (hℳ : Theory.Models ℳ theory) (kind : Kind) (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    membership ℳ (tuple hℳ kind length code result) (state hℳ carrier interpretation symbols assignment) ↔
      Condition hℳ (state hℳ carrier interpretation symbols assignment) kind carrier interpretation symbols assignment length code result := by
  apply ((PureLeastFixedPoint.fixed hℳ body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) (ambient hℳ carrier) (body_bounded hℳ carrier interpretation symbols assignment)
    (body_mono hℳ carrier interpretation symbols assignment) (state_graph hℳ carrier interpretation symbols assignment)).1 _).trans
  apply (body_correct hℳ carrier interpretation symbols assignment _ _).trans
  constructor
  · rintro ⟨other,l,c,r,hEqual,hCondition⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ := tuple_injective hℳ hEqual
    exact hCondition
  · intro h
    exact ⟨kind,length,code,result,rfl,h⟩

def termQuerySource : Formula S [] [s,s,s] :=
  membership_formula (PureSyntaxOperator.tupleTerm .term empty_set_term (.fvar (.there .here)) (.fvar (.there (.there .here)))) (.fvar .here)
def termQuery : Formula ℒ [] [setSort,setSort,setSort] := openFormula PureRelatedStage.interpretation termQuerySource

theorem term_query_correct (hℳ : Theory.Models ℳ theory) (candidate code result : Carrier ℳ) :
    termQuery.satisfies (templateEnv (.cons candidate (.cons code (.cons result .nil)))) ↔ membership ℳ (tuple hℳ .term (zero hℳ) code result) candidate := by
  apply (openFormula_correct (E hℳ) (PureValueOperator.realizes hℳ) termQuerySource (.cons candidate (.cons code (.cons result .nil)))).trans
  change membership ℳ ((PureSyntaxOperator.tupleTerm .term empty_set_term (.fvar (.there .here)) (.fvar (.there (.there .here)))).eval
    (templateEnv (.cons candidate (.cons code (.cons result .nil))) : Env (E hℳ).model [] [s,s,s])) candidate ↔ _
  rw [tuple_eval hℳ]
  change membership ℳ (tuple hℳ .term ((E hℳ).function .emptySet .nil) code result) candidate ↔ _
  rw [zero_eq hℳ]

def termGraph : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) .nil))))))
    (applyTemplate termQuery (.cons (.bvar .here) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) .nil))))

theorem term_graph_correct (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment code result : Carrier ℳ) :
    termGraph.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons code (.cons result .nil))))))) ↔ membership ℳ (tuple hℳ .term (zero hℳ) code result) (state hℳ carrier interpretation symbols assignment) := by
  change (∃ candidate, _ ∧ _) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have hCandidate' : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))) := (applyTemplate_satisfies _ _ _).mp hCandidate
    have hMember' : termQuery.satisfies (templateEnv (.cons candidate (.cons code (.cons result .nil)))) := (applyTemplate_satisfies _ _ _).mp hMember
    exact state_unique hℳ carrier interpretation symbols assignment hCandidate' ▸ (term_query_correct hℳ candidate code result).mp hMember'
  · intro h
    refine ⟨state hℳ carrier interpretation symbols assignment,?_,?_⟩
    · exact (applyTemplate_satisfies _ _ _).mpr (state_graph hℳ carrier interpretation symbols assignment)
    · exact (applyTemplate_satisfies _ _ _).mpr ((term_query_correct hℳ _ code result).mpr h)

def listQuerySource : Formula S [] [s,s,s,s] :=
  membership_formula (PureSyntaxOperator.tupleTerm .termList (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))) (.fvar .here)
def listQuery : Formula ℒ [] [setSort,setSort,setSort,setSort] := openFormula PureRelatedStage.interpretation listQuerySource

theorem list_query_correct (hℳ : Theory.Models ℳ theory) (candidate length code result : Carrier ℳ) :
    listQuery.satisfies (templateEnv (.cons candidate (.cons length (.cons code (.cons result .nil))))) ↔ membership ℳ (tuple hℳ .termList length code result) candidate := by
  apply (openFormula_correct (E hℳ) (PureValueOperator.realizes hℳ) listQuerySource (.cons candidate (.cons length (.cons code (.cons result .nil))))).trans
  change membership ℳ ((PureSyntaxOperator.tupleTerm .termList (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))).eval
    (templateEnv (.cons candidate (.cons length (.cons code (.cons result .nil)))) : Env (E hℳ).model [] [s,s,s,s])) candidate ↔ _
  rw [tuple_eval hℳ]
  rfl

def listGraph : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) .nil))))))
    (applyTemplate listQuery (.cons (.bvar .here) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) (.cons (.fvar (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))

theorem list_graph_correct (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    listGraph.satisfies (templateEnv (.cons carrier (.cons interpretation (.cons symbols (.cons assignment (.cons length (.cons code (.cons result .nil)))))))) ↔ membership ℳ (tuple hℳ .termList length code result) (state hℳ carrier interpretation symbols assignment) := by
  change (∃ candidate, _ ∧ _) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have hCandidate' : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))) := (applyTemplate_satisfies _ _ _).mp hCandidate
    have hMember' : listQuery.satisfies (templateEnv (.cons candidate (.cons length (.cons code (.cons result .nil))))) := (applyTemplate_satisfies _ _ _).mp hMember
    exact state_unique hℳ carrier interpretation symbols assignment hCandidate' ▸ (list_query_correct hℳ candidate length code result).mp hMember'
  · intro h
    refine ⟨state hℳ carrier interpretation symbols assignment,?_,?_⟩
    · exact (applyTemplate_satisfies _ _ _).mpr (state_graph hℳ carrier interpretation symbols assignment)
    · exact (applyTemplate_satisfies _ _ _).mpr ((list_query_correct hℳ _ length code result).mpr h)
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueFixedPoint
