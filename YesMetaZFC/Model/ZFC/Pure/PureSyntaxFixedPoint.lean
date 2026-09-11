import YesMetaZFC.Model.ZFC.Pure.PureSyntaxOperator

/-! # 三个语法识别关系的实际纯图

最小不动点集合的三个标签切片分别解释项、参数列和公式。标签及元组的
单射性保证共同生成方程精确分解为三个原递归方程。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxFixedPoint
open PureModel PureNaturalInduction PureSyntaxOperator PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable def state (hℳ : Theory.Models ℳ theory) : Carrier ℳ :=
  Classical.choose (PureLeastFixedPoint.functional hℳ body .nil (ambient hℳ) (body_bounded hℳ))

theorem state_graph (hℳ : Theory.Models ℳ theory) :
    (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons (state hℳ) .nil)) :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body .nil (ambient hℳ) (body_bounded hℳ))).1

theorem state_unique (hℳ : Theory.Models ℳ theory) {other : Carrier ℳ}
    (hOther : (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons other .nil))) : other = state hℳ :=
  (Classical.choose_spec (PureLeastFixedPoint.functional hℳ body .nil (ambient hℳ) (body_bounded hℳ))).2 other hOther

theorem tag_injective (hℳ : Theory.Models ℳ theory) {first second : Kind} (hEqual : tag hℳ first = tag hℳ second) : first = second := by
  have hZeroSucc (input : Carrier ℳ) : zero hℳ ≠ succ hℳ input := by
    intro h
    exact zero_spec hℳ input
      ((congrArg (membership ℳ input) h.symm).mp ((succ_spec hℳ input input).mpr (Or.inr rfl)))
  have hOneTwo : succ hℳ (zero hℳ) ≠ succ hℳ (succ hℳ (zero hℳ)) := by
    intro h
    -- 只改写隶属关系的右参数，固定替换目标，避免展开整个模型来猜测 motive。
    have hSelf : membership ℳ (succ hℳ (zero hℳ)) (succ hℳ (zero hℳ)) :=
      (congrArg (membership ℳ (succ hℳ (zero hℳ))) h.symm).mp
        ((succ_spec hℳ (succ hℳ (zero hℳ)) (succ hℳ (zero hℳ))).mpr (Or.inr rfl))
    have hOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) _ (succ_mem hℳ (zero_mem hℳ))
    exact hOrdinal.wellOrder.linear.irrefl _ hSelf hSelf
  have hTerm : tag hℳ .term = zero hℳ := zero_eq hℳ
  have hList : tag hℳ .termList = succ hℳ (zero hℳ) := by
    change (E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil) = _
    rw [succ_eq hℳ,zero_eq hℳ]
  have hFormula : tag hℳ .formula = succ hℳ (succ hℳ (zero hℳ)) := by
    change (E hℳ).function .successor (.cons ((E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil)) .nil) = _
    simp only [succ_eq hℳ,zero_eq hℳ]
  -- 三个标签的九种比较已确定；避免逐分支试探不适用的不等式。
  cases first <;> cases second <;> simp only [hTerm, hList, hFormula] at hEqual
  · rfl
  · exact False.elim (hZeroSucc (zero hℳ) hEqual)
  · exact False.elim (hZeroSucc (succ hℳ (zero hℳ)) hEqual)
  · exact False.elim (hZeroSucc (zero hℳ) hEqual.symm)
  · rfl
  · exact False.elim (hOneTwo hEqual)
  · exact False.elim (hZeroSucc (succ hℳ (zero hℳ)) hEqual.symm)
  · exact False.elim (hOneTwo hEqual.symm)
  · rfl

theorem tuple_injective (hℳ : Theory.Models ℳ theory) {first second : Kind} {d l c d' l' c' : Carrier ℳ}
    (hEqual : tuple hℳ first d l c = tuple hℳ second d' l' c') : first = second ∧ d = d' ∧ l = l' ∧ c = c' := by
  have hOuter := pair_injective hℳ hEqual
  have hDepth := pair_injective hℳ hOuter.2
  have hTail := pair_injective hℳ hDepth.2
  exact ⟨tag_injective hℳ (first := first) (second := second) hOuter.1, hDepth.1, hTail⟩

theorem equation (hℳ : Theory.Models ℳ theory) (kind : Kind) (depth length code : Carrier ℳ) :
    membership ℳ (tuple hℳ kind depth length code) (state hℳ) ↔ Condition hℳ (state hℳ) kind depth length code := by
  apply ((PureLeastFixedPoint.fixed hℳ body .nil (ambient hℳ) (body_bounded hℳ) (body_mono hℳ) (state_graph hℳ)).1 _).trans
  apply (body_correct hℳ _ _).trans
  constructor
  · rintro ⟨other,d,l,c,hEqual,hCondition⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ := tuple_injective hℳ
      (first := kind) (second := other) (d := depth) (l := length) (c := code)
      (d' := d) (l' := l) (c' := c) hEqual
    exact hCondition
  · intro hCondition
    exact ⟨kind,depth,length,code,rfl,hCondition⟩

def query2Source (kind : Kind) : Formula S [] [s,s,s] :=
    (membership_formula (tupleTerm kind (.fvar (.there .here)) ∅ₘ (.fvar (.there (.there .here)))) (.fvar .here))

def query3Source : Formula S [] [s,s,s,s] :=
    (membership_formula (tupleTerm .termList (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))) (.fvar .here))

def query2 (kind : Kind) : Formula ℒ [] [setSort,setSort,setSort] :=
  openFormula PureRoundTwoStage.interpretation (query2Source kind)
def query3 : Formula ℒ [] [setSort,setSort,setSort,setSort] :=
  openFormula PureRoundTwoStage.interpretation query3Source

def graph2 (kind : Kind) : Formula ℒ [] [setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) .nil))
    (applyTemplate (query2 kind) (.cons (.bvar .here) (.cons (.fvar .here) (.cons (.fvar (.there .here)) .nil))))
def graph3 : Formula ℒ [] [setSort,setSort,setSort] :=
  .existsE setSort <| .conj
    (applyTemplate (PureLeastFixedPoint.graph body) (.cons (.bvar .here) .nil))
    (applyTemplate query3 (.cons (.bvar .here) (.cons (.fvar .here) (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) .nil)))))

theorem query2_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (candidate depth code : Carrier ℳ) :
    (query2 kind).satisfies (templateEnv (.cons candidate (.cons depth (.cons code .nil)))) ↔
      membership ℳ (tuple hℳ kind depth (zero hℳ) code) candidate := by
  apply (openFormula_correct (E hℳ) (PureRoundTwoStage.realizes hℳ) (query2Source kind) (.cons candidate (.cons depth (.cons code .nil)))).trans
  change membership ℳ ((tupleTerm kind (.fvar (.there .here)) ∅ₘ (.fvar (.there (.there .here)))).eval
    (templateEnv (.cons candidate (.cons depth (.cons code .nil))) : Env (E hℳ).model [] [s,s,s])) candidate ↔ _
  rw [tuple_eval hℳ]
  change membership ℳ (tuple hℳ kind depth ((E hℳ).function .emptySet .nil) code) candidate ↔ _
  rw [zero_eq hℳ]

theorem query3_correct (hℳ : Theory.Models ℳ theory) (candidate depth length code : Carrier ℳ) :
    query3.satisfies (templateEnv (.cons candidate (.cons depth (.cons length (.cons code .nil))))) ↔
      membership ℳ (tuple hℳ .termList depth length code) candidate := by
  apply (openFormula_correct (E hℳ) (PureRoundTwoStage.realizes hℳ) query3Source (.cons candidate (.cons depth (.cons length (.cons code .nil))))).trans
  change membership ℳ ((tupleTerm .termList (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))).eval
    (templateEnv (.cons candidate (.cons depth (.cons length (.cons code .nil)))) : Env (E hℳ).model [] [s,s,s,s])) candidate ↔ _
  rw [tuple_eval hℳ]
  rfl

theorem graph2_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (depth code : Carrier ℳ) :
    (graph2 kind).satisfies (templateEnv (.cons depth (.cons code .nil))) ↔
      membership ℳ (tuple hℳ kind depth (zero hℳ) code) (state hℳ) := by
  simp only [graph2,Formula.satisfies,applyTemplate_satisfies]
  change (∃ candidate, (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate .nil)) ∧
    (query2 kind).satisfies (templateEnv (.cons candidate (.cons depth (.cons code .nil))))) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have h := (query2_correct hℳ kind candidate depth code).mp hMember
    exact state_unique hℳ hCandidate ▸ h
  · intro hMember
    exact ⟨state hℳ,state_graph hℳ,(query2_correct hℳ kind _ depth code).mpr hMember⟩

theorem graph3_correct (hℳ : Theory.Models ℳ theory) (depth length code : Carrier ℳ) :
    graph3.satisfies (templateEnv (.cons depth (.cons length (.cons code .nil)))) ↔
      membership ℳ (tuple hℳ .termList depth length code) (state hℳ) := by
  simp only [graph3,Formula.satisfies,applyTemplate_satisfies]
  change (∃ candidate, (PureLeastFixedPoint.graph body).satisfies (templateEnv (.cons candidate .nil)) ∧
    query3.satisfies (templateEnv (.cons candidate (.cons depth (.cons length (.cons code .nil)))))) ↔ _
  constructor
  · rintro ⟨candidate,hCandidate,hMember⟩
    have h := (query3_correct hℳ candidate depth length code).mp hMember
    exact state_unique hℳ hCandidate ▸ h
  · intro hMember
    exact ⟨state hℳ,state_graph hℳ,(query3_correct hℳ _ depth length code).mpr hMember⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxFixedPoint
