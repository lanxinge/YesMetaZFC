import YesMetaZFC.Model.ZFC.Pure.PureNaturalTuple
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding

/-! # 语法变换的纯最小不动点

原递归正文仅正向查询候选关系；其全部坐标由原 ω guard 限定。
在内部有限笛卡尔积上分离最小闭合集合，元组单射性恢复精确递归方程。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxTransform
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureSyntaxStage.expansion hℳ

theorem omega_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .omega .nil = omega hℳ := PureSyntaxOperator.omega_eq hℳ

def selected : RelationSymbol → Bool
  | .syntaxTransform => true
  | _ => false

def replace : PredicateExpansion.Replacements S s := fun state symbol args =>
  match symbol,args with
  | .syntaxTransform,(.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) => membership_formula (PureNaturalTuple.term [a0,a1,a2,a3,a4,a5,a6]) state
  | symbol,args => .rel symbol args

noncomputable def relations (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) : PredicateExpansion.Relations (E hℳ).model := fun symbol args =>
  match symbol,args with
  | .syntaxTransform,(.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) => membership ℳ (PureNaturalTuple.value hℳ [a0,a1,a2,a3,a4,a5,a6]) state
  | symbol,args => (E hℳ).relation symbol args

theorem replace_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (state : Term S bound free s) (symbol : RelationSymbol)
    (args : Arguments S bound free (S.relDomain symbol)) :
    (replace state symbol args).satisfies env ↔ relations hℳ (state.eval env) symbol (args.eval env) := by
  cases symbol
  case syntaxTransform =>
    match args with
    | (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))) =>
      change membership ℳ ((PureNaturalTuple.term [a0,a1,a2,a3,a4,a5,a6]).eval env) (state.eval env) ↔ _
      rw [PureNaturalTuple.eval hℳ]
      rfl
  all_goals rfl

def condition : Formula S [] [s,s,s,s,s,s,s] := FormalSystem.syntax_transform_condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
noncomputable def Condition (hℳ : Theory.Models ℳ theory) (state a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) : Prop :=
  PredicateExpansion.evaluate (relations hℳ state) (templateEnv (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil)))))))) condition

theorem positive : PredicateExpansion.positive selected condition = true := rfl

theorem condition_mono (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second)
    (a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) : Condition hℳ first a0 a1 a2 a3 a4 a5 a6 → Condition hℳ second a0 a1 a2 a3 a4 a5 a6 := by
  apply PredicateExpansion.monotone selected (relations hℳ first) (relations hℳ second) ?_ ?_ _ _ positive
  · intro symbol args
    cases symbol
    case syntaxTransform =>
      cases args with | cons a0 tail0 =>
      cases tail0 with | cons a1 tail1 =>
      cases tail1 with | cons a2 tail2 =>
      cases tail2 with | cons a3 tail3 =>
      cases tail3 with | cons a4 tail4 =>
      cases tail4 with | cons a5 tail5 =>
      cases tail5 with | cons a6 tail6 =>
      cases tail6
      exact hSubset _
    all_goals exact id
  · intro symbol hSelected args
    cases symbol <;> first | rfl | contradiction

def step : Formula S [] [s,s] :=
  .existsE s <| .existsE s <| .existsE s <| .existsE s <| .existsE s <| .existsE s <| .existsE s <| 
  let original := applyTemplate condition (.cons (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.bvar (.there (.there (.there (.there (.there .here)))))) (.cons (.bvar (.there (.there (.there (.there .here))))) (.cons (.bvar (.there (.there (.there .here)))) (.cons (.bvar (.there (.there .here))) (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))))))
  (Formula.conj (.equal (.fvar .here) (PureNaturalTuple.term [(.bvar (.there (.there (.there (.there (.there (.there .here))))))),(.bvar (.there (.there (.there (.there (.there .here)))))),(.bvar (.there (.there (.there (.there .here))))),(.bvar (.there (.there (.there .here)))),(.bvar (.there (.there .here))),(.bvar (.there .here)),(.bvar .here)]))
    (PredicateExpansion.expand replace (.fvar (.there .here)) original))
def body : Formula ℒ [] [setSort,setSort] := openFormula PureSyntaxStage.interpretation step

theorem body_correct (hℳ : Theory.Models ℳ theory) (state output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body .nil state output ↔
      ∃ a0 a1 a2 a3 a4 a5 a6, output = PureNaturalTuple.value hℳ [a0,a1,a2,a3,a4,a5,a6] ∧ Condition hℳ state a0 a1 a2 a3 a4 a5 a6 := by
  apply (openFormula_correct (E hℳ) (PureSyntaxStage.realizes hℳ) step (.cons output (.cons state .nil))).trans
  change (∃ a0 a1 a2 a3 a4 a5 a6, output = (PureNaturalTuple.term [(.bvar (.there (.there (.there (.there (.there (.there .here))))))),(.bvar (.there (.there (.there (.there (.there .here)))))),(.bvar (.there (.there (.there (.there .here))))),(.bvar (.there (.there (.there .here)))),(.bvar (.there (.there .here))),(.bvar (.there .here)),(.bvar .here)]).eval (((((((((templateEnv (.cons output (.cons state .nil)) : Env (E hℳ).model [] [s,s])).pushBound a0).pushBound a1).pushBound a2).pushBound a3).pushBound a4).pushBound a5).pushBound a6) ∧
    (PredicateExpansion.expand replace (.fvar (.there .here)) (applyTemplate condition (.cons (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.bvar (.there (.there (.there (.there (.there .here)))))) (.cons (.bvar (.there (.there (.there (.there .here))))) (.cons (.bvar (.there (.there (.there .here)))) (.cons (.bvar (.there (.there .here))) (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil))))))))).satisfies (((((((((templateEnv (.cons output (.cons state .nil)) : Env (E hℳ).model [] [s,s])).pushBound a0).pushBound a1).pushBound a2).pushBound a3).pushBound a4).pushBound a5).pushBound a6)) ↔ _
  apply exists_congr; intro a0
  apply exists_congr; intro a1
  apply exists_congr; intro a2
  apply exists_congr; intro a3
  apply exists_congr; intro a4
  apply exists_congr; intro a5
  apply exists_congr; intro a6
  apply and_congr
  · change output = (PureNaturalTuple.term [(.bvar (.there (.there (.there (.there (.there (.there .here))))))),(.bvar (.there (.there (.there (.there (.there .here)))))),(.bvar (.there (.there (.there (.there .here))))),(.bvar (.there (.there (.there .here)))),(.bvar (.there (.there .here))),(.bvar (.there .here)),(.bvar .here)]).eval (((((((((templateEnv (.cons output (.cons state .nil)) : Env (E hℳ).model [] [s,s])).pushBound a0).pushBound a1).pushBound a2).pushBound a3).pushBound a4).pushBound a5).pushBound a6) ↔ _
    rw [PureNaturalTuple.eval hℳ]
    rfl
  · apply (PredicateExpansion.expand_correct replace (relations hℳ) (replace_correct hℳ) _ _ _).trans
    exact PredicateExpansion.evaluate_applyTemplate (relations hℳ state) _ _ _

theorem body_mono (hℳ : Theory.Models ℳ theory) (first second : Carrier ℳ)
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second) (output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body .nil first output → PureLeastFixedPoint.Holds body .nil second output := by
  intro h
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,hEq,h⟩ := (body_correct hℳ first output).mp h
  exact (body_correct hℳ second output).mpr ⟨a0,a1,a2,a3,a4,a5,a6,hEq,condition_mono hℳ hSubset a0 a1 a2 a3 a4 a5 a6 h⟩

theorem condition_bounded (hℳ : Theory.Models ℳ theory) (state a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ)
    (h : Condition hℳ state a0 a1 a2 a3 a4 a5 a6) : ∀ field, field ∈ [a0,a1,a2,a3,a4,a5,a6] → membership ℳ field (omega hℳ) := by
  change ((((membership ℳ a0 ((E hℳ).function .omega .nil) ∧ membership ℳ a1 ((E hℳ).function .omega .nil)) ∧ (membership ℳ a2 ((E hℳ).function .omega .nil) ∧ membership ℳ a3 ((E hℳ).function .omega .nil))) ∧ (membership ℳ a4 ((E hℳ).function .omega .nil) ∧ (membership ℳ a5 ((E hℳ).function .omega .nil) ∧ membership ℳ a6 ((E hℳ).function .omega .nil)))) ∧ _) ∧ _ at h
  have hg := h.1.1
  rw [omega_eq hℳ] at hg
  intro field hField
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hField
  rcases hField with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.1.1.1
  · exact hg.1.1.2
  · exact hg.1.2.1
  · exact hg.1.2.2
  · exact hg.2.1
  · exact hg.2.2.1
  · exact hg.2.2.2

theorem body_bounded (hℳ : Theory.Models ℳ theory) (state output : Carrier ℳ)
    (h : PureLeastFixedPoint.Holds body .nil state output) : membership ℳ output (PureNaturalTuple.ambient hℳ 7) := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,rfl,hCondition⟩ := (body_correct hℳ state output).mp h
  exact PureNaturalTuple.bounded hℳ [a0,a1,a2,a3,a4,a5,a6] (condition_bounded hℳ state a0 a1 a2 a3 a4 a5 a6 hCondition)

noncomputable def state (hℳ : Theory.Models ℳ theory) : Carrier ℳ :=
  Classical.choose (PureLeastFixedPoint.functional hℳ body .nil (PureNaturalTuple.ambient hℳ 7) (body_bounded hℳ))
theorem state_graph (hℳ : Theory.Models ℳ theory) :
    (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons (state hℳ) .nil)) :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body .nil (PureNaturalTuple.ambient hℳ 7) (body_bounded hℳ))).1
theorem state_unique (hℳ : Theory.Models ℳ theory) {other : Carrier ℳ}
    (hOther : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons other .nil))) : other = state hℳ :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body .nil (PureNaturalTuple.ambient hℳ 7) (body_bounded hℳ))).2 other hOther

theorem equation (hℳ : Theory.Models ℳ theory) (a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) :
    membership ℳ (PureNaturalTuple.value hℳ [a0,a1,a2,a3,a4,a5,a6]) (state hℳ) ↔ Condition hℳ (state hℳ) a0 a1 a2 a3 a4 a5 a6 := by
  apply ((PureLeastFixedPoint.fixed hℳ body .nil (PureNaturalTuple.ambient hℳ 7) (body_bounded hℳ) (body_mono hℳ) (state_graph hℳ)).1 _).trans
  apply (body_correct hℳ _ _).trans
  constructor
  · rintro ⟨b0,b1,b2,b3,b4,b5,b6,hEq,h⟩
    have hList := PureNaturalTuple.injective hℳ (first := [a0,a1,a2,a3,a4,a5,a6]) (second := [b0,b1,b2,b3,b4,b5,b6]) rfl hEq
    simp only [List.cons.injEq] at hList
    rcases hList with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩
    exact h
  · intro h
    exact ⟨a0,a1,a2,a3,a4,a5,a6,rfl,h⟩

def querySource : Formula S [] [s,s,s,s,s,s,s,s] := membership_formula
  (PureNaturalTuple.term [(.fvar (.there .here)),(.fvar (.there (.there .here))),(.fvar (.there (.there (.there .here)))),(.fvar (.there (.there (.there (.there .here))))),(.fvar (.there (.there (.there (.there (.there .here)))))),(.fvar (.there (.there (.there (.there (.there (.there .here))))))),(.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))]) (.fvar .here)
def query : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort,setSort,setSort,setSort] := openFormula PureSyntaxStage.interpretation querySource
def graph : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) .nil))
    (applyTemplate query (.cons (.bvar .here) (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) (.cons (.fvar (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))))

theorem query_correct (hℳ : Theory.Models ℳ theory) (candidate a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) :
    query.satisfies (templateEnv (.cons candidate (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))))) ↔ membership ℳ (PureNaturalTuple.value hℳ [a0,a1,a2,a3,a4,a5,a6]) candidate := by
  apply (openFormula_correct (E hℳ) (PureSyntaxStage.realizes hℳ) querySource (.cons candidate (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))))).trans
  change membership ℳ ((PureNaturalTuple.term [(.fvar (.there .here)),(.fvar (.there (.there .here))),(.fvar (.there (.there (.there .here)))),(.fvar (.there (.there (.there (.there .here))))),(.fvar (.there (.there (.there (.there (.there .here)))))),(.fvar (.there (.there (.there (.there (.there (.there .here))))))),(.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))]).eval
    (templateEnv (.cons candidate (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil)))))))) : Env (E hℳ).model [] [s,s,s,s,s,s,s,s])) candidate ↔ _
  rw [PureNaturalTuple.eval hℳ]
  rfl

theorem graph_correct (hℳ : Theory.Models ℳ theory) (a0 a1 a2 a3 a4 a5 a6 : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil)))))))) ↔ membership ℳ (PureNaturalTuple.value hℳ [a0,a1,a2,a3,a4,a5,a6]) (state hℳ) := by
  change (∃ candidate, _ ∧ _) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,h⟩
    have hCandidate' : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate .nil)) := (applyTemplate_satisfies _ _ _).mp hCandidate
    have h' : query.satisfies (templateEnv (.cons candidate (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 (.cons a6 .nil))))))))) := (applyTemplate_satisfies _ _ _).mp h
    exact state_unique hℳ hCandidate' ▸ (query_correct hℳ candidate a0 a1 a2 a3 a4 a5 a6).mp h'
  · intro h
    refine ⟨state hℳ,?_,?_⟩
    · exact (applyTemplate_satisfies _ _ _).mpr (state_graph hℳ)
    · exact (applyTemplate_satisfies _ _ _).mpr ((query_correct hℳ _ a0 a1 a2 a3 a4 a5 a6).mpr h)

theorem dependencies_covered : formulaCovered PureSyntaxStage.functionCovered PureSyntaxStage.relationCovered step = true := rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxTransform
