import YesMetaZFC.Model.ZFC.Pure.PureRelatedSyntaxOperator

/-! # 每个符号集上的相关语法不动点

符号集是图的参数，不需要把全部符号集收集为一个集合。元组查询与单射性
复用普通语法识别层；各切片满足带同一符号集参数的原递归方程。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxFixedPoint
open PureModel PureNaturalInduction PureRelatedSyntaxOperator
open PureSyntaxOperator (Kind tuple ambient)
open PureSyntaxFixedPoint (query2 query3 query2_correct query3_correct tuple_injective)
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable def state (hℳ : Theory.Models ℳ theory) (symbols : Carrier ℳ) : Carrier ℳ :=
  Classical.choose (PureLeastFixedPoint.functional hℳ body (.cons symbols .nil) (ambient hℳ) (body_bounded hℳ symbols))

theorem state_graph (hℳ : Theory.Models ℳ theory) (symbols : Carrier ℳ) :
    (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons (state hℳ symbols) (.cons symbols .nil))) :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body (.cons symbols .nil) (ambient hℳ) (body_bounded hℳ symbols))).1

theorem state_unique (hℳ : Theory.Models ℳ theory) (symbols : Carrier ℳ) {other : Carrier ℳ}
    (hOther : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons other (.cons symbols .nil)))) : other = state hℳ symbols :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body (.cons symbols .nil) (ambient hℳ) (body_bounded hℳ symbols))).2 other hOther

theorem equation (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols depth length code : Carrier ℳ) :
    membership ℳ (tuple hℳ kind depth length code) (state hℳ symbols) ↔ Condition hℳ (state hℳ symbols) kind symbols depth length code := by
  apply ((PureLeastFixedPoint.fixed hℳ body (.cons symbols .nil) (ambient hℳ) (body_bounded hℳ symbols)
    (body_mono hℳ symbols) (state_graph hℳ symbols)).1 _).trans
  apply (body_correct hℳ symbols _ _).trans
  constructor
  · rintro ⟨other,d,l,c,hEqual,hCondition⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ := tuple_injective hℳ hEqual
    exact hCondition
  · intro hCondition
    exact ⟨kind,depth,length,code,rfl,hCondition⟩

def graph2 (kind : Kind) : Formula ℒ [] [setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) (.cons (.fvar .here) .nil)))
    (applyTemplate (query2 kind) (.cons (.bvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) .nil))))

def graph3 : Formula ℒ [] [setSort,setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) (.cons (.fvar .here) .nil)))
    (applyTemplate query3 (.cons (.bvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) .nil)))))

theorem graph2_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols depth code : Carrier ℳ) :
    (graph2 kind).satisfies (templateEnv (.cons symbols (.cons depth (.cons code .nil)))) ↔
      membership ℳ (tuple hℳ kind depth (zero hℳ) code) (state hℳ symbols) := by
  simp only [graph2,Formula.satisfies,applyTemplate_satisfies]
  change (∃ candidate, (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate (.cons symbols .nil))) ∧
    (query2 kind).satisfies (templateEnv (.cons candidate (.cons depth (.cons code .nil))))) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have h := (query2_correct hℳ kind candidate depth code).mp hMember
    exact state_unique hℳ symbols hCandidate ▸ h
  · intro hMember
    exact ⟨state hℳ symbols,state_graph hℳ symbols,(query2_correct hℳ kind _ depth code).mpr hMember⟩

theorem graph3_correct (hℳ : Theory.Models ℳ theory) (symbols depth length code : Carrier ℳ) :
    graph3.satisfies (templateEnv (.cons symbols (.cons depth (.cons length (.cons code .nil))))) ↔
      membership ℳ (tuple hℳ .termList depth length code) (state hℳ symbols) := by
  simp only [graph3,Formula.satisfies,applyTemplate_satisfies]
  change (∃ candidate, (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate (.cons symbols .nil))) ∧
    query3.satisfies (templateEnv (.cons candidate (.cons depth (.cons length (.cons code .nil)))))) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have h := (query3_correct hℳ candidate depth length code).mp hMember
    exact state_unique hℳ symbols hCandidate ▸ h
  · intro hMember
    exact ⟨state hℳ symbols,state_graph hℳ symbols,(query3_correct hℳ _ depth length code).mpr hMember⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxFixedPoint
