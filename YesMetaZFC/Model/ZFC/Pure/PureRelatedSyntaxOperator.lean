import YesMetaZFC.Model.Interpretation.PredicateExpansion
import YesMetaZFC.Model.ZFC.Pure.PureRoundThreeSpecifications
import YesMetaZFC.Model.ZFC.Pure.PureLeastFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding

/-! # 带符号集参数的相关语法正算子

三个关系用带标签的四元 Kuratowski 元组存入一个集合。原递归正文中的原子
统一改写为该集合的成员关系，符号集作为自由参数保留，其余依赖均由第二轮的实际解释覆盖。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxOperator
open PureModel PureNaturalInduction PureArithmeticSpecifications
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
open _root_.YesMetaZFC.Automation
-- 本算子只使用第二轮已完成的基础符号；覆盖证明在文件末尾给出。
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureRoundTwoStage.expansion hℳ

open PureSyntaxOperator (Kind tupleTerm tuple tag pair ambient pair_mem_product tag_natural)

theorem zero_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .emptySet .nil = zero hℳ :=
  PureSyntaxOperator.zero_eq hℳ
theorem omega_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .omega .nil = omega hℳ :=
  PureSyntaxOperator.omega_eq hℳ

theorem tuple_eval (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (kind : Kind) (depth length code : Term S bound free s) :
    (tupleTerm kind depth length code).eval env = tuple hℳ kind (depth.eval env) (length.eval env) (code.eval env) := by
  cases kind <;> rfl

def selected : RelationSymbol → Bool
  | .isRelatedTermCodeAt | .isRelatedTermListCodeAt | .isRelatedFormulaCodeAt => true
  | _ => false

/-- 当前算子的符号集在外层固定，递归原子只查询该候选切片。
完整关系解释按实参选择切片；`PureRelatedSyntaxStage.condition_satisfaction`
核验原正文所有递归调用保持此符号集，不能将此替换用作任意正文的参数擦除。 -/
def replace : PredicateExpansion.Replacements S s := fun state symbol args =>
  match symbol,args with
  | .isRelatedTermCodeAt,.cons _symbols (.cons depth (.cons code .nil)) => membership_formula (tupleTerm .term depth ∅ₘ code) state
  | .isRelatedTermListCodeAt,.cons _symbols (.cons depth (.cons length (.cons code .nil))) => membership_formula (tupleTerm .termList depth length code) state
  | .isRelatedFormulaCodeAt,.cons _symbols (.cons depth (.cons code .nil)) => membership_formula (tupleTerm .formula depth ∅ₘ code) state
  | symbol,args => .rel symbol args

noncomputable def relations (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) : PredicateExpansion.Relations (E hℳ).model := fun symbol args =>
  match symbol,args with
  | .isRelatedTermCodeAt,.cons _symbols (.cons depth (.cons code .nil)) => membership ℳ (tuple hℳ .term depth (zero hℳ) code) state
  | .isRelatedTermListCodeAt,.cons _symbols (.cons depth (.cons length (.cons code .nil))) => membership ℳ (tuple hℳ .termList depth length code) state
  | .isRelatedFormulaCodeAt,.cons _symbols (.cons depth (.cons code .nil)) => membership ℳ (tuple hℳ .formula depth (zero hℳ) code) state
  | symbol,args => (E hℳ).relation symbol args

theorem replace_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (state : Term S bound free s) (symbol : RelationSymbol)
    (args : Arguments S bound free (S.relDomain symbol)) :
    (replace state symbol args).satisfies env ↔ relations hℳ (state.eval env) symbol (args.eval env) := by
  cases symbol
  case isRelatedTermCodeAt =>
    match args with
    | .cons _symbols (.cons depth (.cons code .nil)) =>
      change membership ℳ ((tupleTerm .term depth ∅ₘ code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      change membership ℳ (tuple hℳ .term (depth.eval env) ((E hℳ).function .emptySet .nil) (code.eval env)) (state.eval env) ↔ _
      rw [zero_eq hℳ]
      rfl
  case isRelatedTermListCodeAt =>
    match args with
    | .cons _symbols (.cons depth (.cons length (.cons code .nil))) =>
      change membership ℳ ((tupleTerm .termList depth length code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      rfl
  case isRelatedFormulaCodeAt =>
    match args with
    | .cons _symbols (.cons depth (.cons code .nil)) =>
      change membership ℳ ((tupleTerm .formula depth ∅ₘ code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      change membership ℳ (tuple hℳ .formula (depth.eval env) ((E hℳ).function .emptySet .nil) (code.eval env)) (state.eval env) ↔ _
      rw [zero_eq hℳ]
      rfl
  all_goals rfl

def condition (kind : Kind) : Formula S [] [s,s,s,s] :=
  let symbols : Term S [] [s,s,s,s] s := .fvar (.there (.there (.there .here)))
  let depth : Term S [] [s,s,s,s] s := .fvar .here
  let length : Term S [] [s,s,s,s] s := .fvar (.there .here)
  let code : Term S [] [s,s,s,s] s := .fvar (.there (.there .here))
  match kind with
  | .term => .conj (.equal length ∅ₘ) (FormalSystem.related_term_code_at_condition symbols depth code)
  | .termList => FormalSystem.related_term_list_code_at_condition symbols depth length code
  | .formula => .conj (.equal length ∅ₘ) (FormalSystem.related_formula_code_at_condition symbols depth code)

noncomputable def Condition (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) (kind : Kind) (symbols depth length code : Carrier ℳ) : Prop :=
  PredicateExpansion.evaluate (relations hℳ state) (templateEnv (.cons depth (.cons length (.cons code (.cons symbols .nil))))) (condition kind)

theorem condition_positive (kind : Kind) : PredicateExpansion.positive selected (condition kind) = true := by cases kind <;> rfl

theorem condition_mono (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second)
    (kind : Kind) (symbols depth length code : Carrier ℳ) :
    Condition hℳ first kind symbols depth length code → Condition hℳ second kind symbols depth length code := by
  apply PredicateExpansion.monotone selected (relations hℳ first) (relations hℳ second) ?_ ?_ _ _ (condition_positive kind)
  · intro symbol args
    cases symbol
    all_goals first
    | exact id
    | cases args with | cons _symbols tail =>
      cases tail with | cons depth tail =>
      cases tail with | cons middle tail =>
      first
      | cases tail; exact hSubset _
      | cases tail with | cons code tail =>
        cases tail; exact hSubset _
  · intro symbol hSelected args
    cases symbol <;> first | rfl | contradiction

def branch (kind : Kind) : Formula S [] [s,s,s] :=
  let symbols : Term S [] [s,s,s,s,s,s] s := .fvar (.there (.there (.there (.there (.there .here)))))
  let code : Term S [] [s,s,s,s,s,s] s := .fvar .here
  let length : Term S [] [s,s,s,s,s,s] s := .fvar (.there .here)
  let depth : Term S [] [s,s,s,s,s,s] s := .fvar (.there (.there .here))
  let output : Term S [] [s,s,s,s,s,s] s := .fvar (.there (.there (.there .here)))
  let state : Term S [] [s,s,s,s,s,s] s := .fvar (.there (.there (.there (.there .here))))
  let original := applyTemplate (condition kind) (.cons depth (.cons length (.cons code (.cons symbols .nil))))
  (Formula.conj (.equal output (tupleTerm kind depth length code)) (PredicateExpansion.expand replace state original)).existsFreeTop s |>.existsFreeTop s |>.existsFreeTop s

def step : Formula S [] [s,s,s] := .disj (branch .term) (.disj (branch .termList) (branch .formula))
def body : Formula ℒ [] [setSort,setSort,setSort] := openFormula PureRoundTwoStage.interpretation step

noncomputable def Step (hℳ : Theory.Models ℳ theory) (symbols state output : Carrier ℳ) : Prop :=
  ∃ kind depth length code, output = tuple hℳ kind depth length code ∧ Condition hℳ state kind symbols depth length code


theorem branch_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (symbols state output : Carrier ℳ) :
    (branch kind).satisfies (templateEnv (.cons output (.cons state (.cons symbols .nil))) : Env (E hℳ).model [] [s,s,s]) ↔
      ∃ depth length code, output = tuple hℳ kind depth length code ∧ Condition hℳ state kind symbols depth length code := by
  simp only [branch,Formula.satisfies_existsFreeTop,Formula.satisfies]
  apply exists_congr; intro depth
  apply exists_congr; intro length
  apply exists_congr; intro code
  apply and_congr
  · change output = (tupleTerm kind (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).eval
      ((((templateEnv (.cons output (.cons state (.cons symbols .nil))) : Env (E hℳ).model [] [s,s,s]).pushFree depth).pushFree length).pushFree code) ↔ _
    rw [tuple_eval hℳ]
    rfl
  · apply (PredicateExpansion.expand_correct replace (relations hℳ) (replace_correct hℳ) _ _ _).trans
    exact PredicateExpansion.evaluate_applyTemplate (relations hℳ state) _ _ _

theorem body_correct (hℳ : Theory.Models ℳ theory) (symbols state output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons state (.cons symbols .nil)))) ↔ Step hℳ symbols state output := by
  apply (openFormula_correct (E hℳ) (PureRoundTwoStage.realizes hℳ) step (.cons output (.cons state (.cons symbols .nil)))).trans
  change ((branch .term).satisfies _ ∨ (branch .termList).satisfies _ ∨ (branch .formula).satisfies _) ↔ _
  rw [branch_correct hℳ,branch_correct hℳ,branch_correct hℳ]
  constructor
  · intro h
    rcases h with h | h | h
    · exact ⟨.term,h⟩
    · exact ⟨.termList,h⟩
    · exact ⟨.formula,h⟩
  · rintro ⟨kind,h⟩
    cases kind
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem body_mono (hℳ : Theory.Models ℳ theory) (symbols first second : Carrier ℳ)
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second) (output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body (.cons symbols .nil) first output → PureLeastFixedPoint.Holds body (.cons symbols .nil) second output := by
  intro hOutput
  obtain ⟨kind,depth,length,code,hEqual,hCondition⟩ := (body_correct hℳ symbols first output).mp hOutput
  exact (body_correct hℳ symbols second output).mpr ⟨kind,depth,length,code,hEqual,condition_mono hℳ hSubset kind symbols depth length code hCondition⟩

theorem condition_bounded (hℳ : Theory.Models ℳ theory) {state : Carrier ℳ} (kind : Kind) {symbols depth length code : Carrier ℳ}
    (hCondition : Condition hℳ state kind symbols depth length code) :
    membership ℳ depth (omega hℳ) ∧ membership ℳ length (omega hℳ) ∧ membership ℳ code (omega hℳ) := by
  cases kind
  · change (length = (E hℳ).function .emptySet .nil ∧ (membership ℳ depth ((E hℳ).function .omega .nil) ∧
      membership ℳ code ((E hℳ).function .omega .nil)) ∧ _) at hCondition
    rw [zero_eq hℳ,omega_eq hℳ] at hCondition
    exact ⟨hCondition.2.1.1,hCondition.1.symm ▸ zero_mem hℳ,hCondition.2.1.2⟩
  · change ((membership ℳ depth ((E hℳ).function .omega .nil) ∧ membership ℳ length ((E hℳ).function .omega .nil)) ∧
      membership ℳ code ((E hℳ).function .omega .nil)) ∧ _ at hCondition
    rw [omega_eq hℳ] at hCondition
    exact ⟨hCondition.1.1.1,hCondition.1.1.2,hCondition.1.2⟩
  · change (length = (E hℳ).function .emptySet .nil ∧ (membership ℳ depth ((E hℳ).function .omega .nil) ∧
      membership ℳ code ((E hℳ).function .omega .nil)) ∧ _) at hCondition
    rw [zero_eq hℳ,omega_eq hℳ] at hCondition
    exact ⟨hCondition.2.1.1,hCondition.1.symm ▸ zero_mem hℳ,hCondition.2.1.2⟩

theorem body_bounded (hℳ : Theory.Models ℳ theory) (symbols state output : Carrier ℳ)
    (hOutput : PureLeastFixedPoint.Holds body (.cons symbols .nil) state output) : membership ℳ output (ambient hℳ) := by
  obtain ⟨kind,depth,length,code,rfl,hCondition⟩ := (body_correct hℳ symbols state output).mp hOutput
  have h := condition_bounded hℳ kind hCondition
  exact pair_mem_product hℳ (tag_natural hℳ kind) (pair_mem_product hℳ h.1 (pair_mem_product hℳ h.2.1 h.2.2))

theorem dependencies_covered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered step = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelatedSyntaxOperator
