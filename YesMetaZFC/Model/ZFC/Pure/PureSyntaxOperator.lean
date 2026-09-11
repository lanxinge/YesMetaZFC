import YesMetaZFC.Model.Interpretation.PredicateExpansion
import YesMetaZFC.Model.ZFC.Pure.PureRoundTwoSpecifications
import YesMetaZFC.Model.ZFC.Pure.PureLeastFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding

/-! # 项、参数列、公式识别的共同正算子

三个关系用带标签的四元 Kuratowski 元组存入一个集合。原递归正文中的原子
统一改写为该集合的成员关系，所有其他符号保持第二轮的实际解释。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxOperator
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
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureRoundTwoStage.expansion hℳ

inductive Kind where
  | term | termList | formula
  deriving DecidableEq

def tagTerm {bound free : SortContext S} : Kind → Term S bound free s
  | .term => ∅ₘ
  | .termList => Sₘ(∅ₘ)
  | .formula => Sₘ(Sₘ(∅ₘ))

def tupleTerm {bound free : SortContext S} (kind : Kind) (depth length code : Term S bound free s) : Term S bound free s :=
  ordered_pair_term (tagTerm kind) (ordered_pair_term depth (ordered_pair_term length code))

noncomputable abbrev pair (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :=
  (E hℳ).function .orderedPair (.cons left (.cons right .nil))
noncomputable def tag (hℳ : Theory.Models ℳ theory) (kind : Kind) : Carrier ℳ :=
  (tagTerm kind).eval (templateEnv .nil : Env (E hℳ).model [] [])
noncomputable def tuple (hℳ : Theory.Models ℳ theory) (kind : Kind) (depth length code : Carrier ℳ) :=
  pair hℳ (tag hℳ kind) (pair hℳ depth (pair hℳ length code))

theorem zero_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .emptySet .nil = zero hℳ :=
  (PureRoundTwoStage.function_preserved hℳ .emptySet rfl _).trans (PureConcatenationStage.zero_eq hℳ)
theorem omega_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .omega .nil = omega hℳ :=
  (PureRoundTwoStage.function_preserved hℳ .omega rfl _).trans (PureConcatenationStage.omega_eq hℳ)
theorem succ_eq (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) :
    (E hℳ).function .successor (.cons input .nil) = succ hℳ input :=
  (PureRoundTwoStage.function_preserved hℳ .successor rfl _).trans (PureConcatenationStage.succ_eq hℳ input)

theorem tag_eval (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (kind : Kind) : (tagTerm kind).eval env = tag hℳ kind := by cases kind <;> rfl

theorem tuple_eval (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (kind : Kind) (depth length code : Term S bound free s) :
    (tupleTerm kind depth length code).eval env = tuple hℳ kind (depth.eval env) (length.eval env) (code.eval env) := by
  change pair hℳ ((tagTerm kind).eval env) (pair hℳ (depth.eval env) (pair hℳ (length.eval env) (code.eval env))) = _
  rw [tag_eval hℳ]
  rfl

def selected : RelationSymbol → Bool
  | .isTermCodeAt | .isTermListCodeAt | .isFormulaCodeAt => true
  | _ => false

def replace : PredicateExpansion.Replacements S s := fun state symbol args =>
  match symbol,args with
  | .isTermCodeAt,.cons depth (.cons code .nil) => membership_formula (tupleTerm .term depth ∅ₘ code) state
  | .isTermListCodeAt,.cons depth (.cons length (.cons code .nil)) => membership_formula (tupleTerm .termList depth length code) state
  | .isFormulaCodeAt,.cons depth (.cons code .nil) => membership_formula (tupleTerm .formula depth ∅ₘ code) state
  | symbol,args => .rel symbol args

noncomputable def relations (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) : PredicateExpansion.Relations (E hℳ).model := fun symbol args =>
  match symbol,args with
  | .isTermCodeAt,.cons depth (.cons code .nil) => membership ℳ (tuple hℳ .term depth (zero hℳ) code) state
  | .isTermListCodeAt,.cons depth (.cons length (.cons code .nil)) => membership ℳ (tuple hℳ .termList depth length code) state
  | .isFormulaCodeAt,.cons depth (.cons code .nil) => membership ℳ (tuple hℳ .formula depth (zero hℳ) code) state
  | symbol,args => (E hℳ).relation symbol args

theorem replace_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (state : Term S bound free s) (symbol : RelationSymbol)
    (args : Arguments S bound free (S.relDomain symbol)) :
    (replace state symbol args).satisfies env ↔ relations hℳ (state.eval env) symbol (args.eval env) := by
  cases symbol
  case isTermCodeAt =>
    match args with
    | .cons depth (.cons code .nil) =>
      change membership ℳ ((tupleTerm .term depth ∅ₘ code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      change membership ℳ (tuple hℳ .term (depth.eval env) ((E hℳ).function .emptySet .nil) (code.eval env)) (state.eval env) ↔ _
      rw [zero_eq hℳ]
      rfl
  case isTermListCodeAt =>
    match args with
    | .cons depth (.cons length (.cons code .nil)) =>
      change membership ℳ ((tupleTerm .termList depth length code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      rfl
  case isFormulaCodeAt =>
    match args with
    | .cons depth (.cons code .nil) =>
      change membership ℳ ((tupleTerm .formula depth ∅ₘ code).eval env) (state.eval env) ↔ _
      rw [tuple_eval hℳ]
      change membership ℳ (tuple hℳ .formula (depth.eval env) ((E hℳ).function .emptySet .nil) (code.eval env)) (state.eval env) ↔ _
      rw [zero_eq hℳ]
      rfl
  all_goals rfl

def condition (kind : Kind) : Formula S [] [s,s,s] :=
  let depth : Term S [] [s,s,s] s := .fvar .here
  let length : Term S [] [s,s,s] s := .fvar (.there .here)
  let code : Term S [] [s,s,s] s := .fvar (.there (.there .here))
  match kind with
  | .term => .conj (.equal length ∅ₘ) (FormalSystem.term_code_at_condition depth code)
  | .termList => FormalSystem.term_list_code_at_condition depth length code
  | .formula => .conj (.equal length ∅ₘ) (FormalSystem.formula_code_at_condition depth code)

noncomputable def Condition (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) (kind : Kind) (depth length code : Carrier ℳ) : Prop :=
  PredicateExpansion.evaluate (relations hℳ state) (templateEnv (.cons depth (.cons length (.cons code .nil)))) (condition kind)

theorem condition_positive (kind : Kind) : PredicateExpansion.positive selected (condition kind) = true := by cases kind <;> rfl

theorem condition_mono (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second)
    (kind : Kind) (depth length code : Carrier ℳ) :
    Condition hℳ first kind depth length code → Condition hℳ second kind depth length code := by
  apply PredicateExpansion.monotone selected (relations hℳ first) (relations hℳ second) ?_ ?_ _ _ (condition_positive kind)
  · intro symbol args
    cases symbol
    all_goals first
    | exact id
    | cases args with | cons depth tail =>
      cases tail with | cons middle tail =>
      first
      | cases tail; exact hSubset _
      | cases tail with | cons code tail =>
        cases tail; exact hSubset _
  · intro symbol hSelected args
    cases symbol <;> first | rfl | contradiction

def branch (kind : Kind) : Formula S [] [s,s] :=
  let code : Term S [] [s,s,s,s,s] s := .fvar .here
  let length : Term S [] [s,s,s,s,s] s := .fvar (.there .here)
  let depth : Term S [] [s,s,s,s,s] s := .fvar (.there (.there .here))
  let output : Term S [] [s,s,s,s,s] s := .fvar (.there (.there (.there .here)))
  let state : Term S [] [s,s,s,s,s] s := .fvar (.there (.there (.there (.there .here))))
  let original := applyTemplate (condition kind) (.cons depth (.cons length (.cons code .nil)))
  (Formula.conj (.equal output (tupleTerm kind depth length code)) (PredicateExpansion.expand replace state original)).existsFreeTop s |>.existsFreeTop s |>.existsFreeTop s

def step : Formula S [] [s,s] := .disj (branch .term) (.disj (branch .termList) (branch .formula))
def body : Formula ℒ [] [setSort,setSort] := openFormula PureRoundTwoStage.interpretation step

noncomputable def Step (hℳ : Theory.Models ℳ theory) (state output : Carrier ℳ) : Prop :=
  ∃ kind depth length code, output = tuple hℳ kind depth length code ∧ Condition hℳ state kind depth length code


theorem branch_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (state output : Carrier ℳ) :
    (branch kind).satisfies (templateEnv (.cons output (.cons state .nil)) : Env (E hℳ).model [] [s,s]) ↔
      ∃ depth length code, output = tuple hℳ kind depth length code ∧ Condition hℳ state kind depth length code := by
  simp only [branch,Formula.satisfies_existsFreeTop,Formula.satisfies]
  apply exists_congr; intro depth
  apply exists_congr; intro length
  apply exists_congr; intro code
  apply and_congr
  · change output = (tupleTerm kind (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).eval
      ((((templateEnv (.cons output (.cons state .nil)) : Env (E hℳ).model [] [s,s]).pushFree depth).pushFree length).pushFree code) ↔ _
    rw [tuple_eval hℳ]
    rfl
  · apply (PredicateExpansion.expand_correct replace (relations hℳ) (replace_correct hℳ) _ _ _).trans
    exact PredicateExpansion.evaluate_applyTemplate (relations hℳ state) _ _ _

theorem body_correct (hℳ : Theory.Models ℳ theory) (state output : Carrier ℳ) :
    body.satisfies (templateEnv (.cons output (.cons state .nil))) ↔ Step hℳ state output := by
  apply (openFormula_correct (E hℳ) (PureRoundTwoStage.realizes hℳ) step (.cons output (.cons state .nil))).trans
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

theorem body_mono (hℳ : Theory.Models ℳ theory) (first second : Carrier ℳ)
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second) (output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body .nil first output → PureLeastFixedPoint.Holds body .nil second output := by
  intro hOutput
  obtain ⟨kind,depth,length,code,hEqual,hCondition⟩ := (body_correct hℳ first output).mp hOutput
  exact (body_correct hℳ second output).mpr ⟨kind,depth,length,code,hEqual,condition_mono hℳ hSubset kind depth length code hCondition⟩

theorem pair_code (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) : PureKuratowski.Code ℳ (pair hℳ left right) left right :=
  (PureRelationDefinitions.orderedPair_correct _ left right).mp
    (((PureRoundTwoStage.realizes hℳ).function .orderedPair (.cons left (.cons right .nil)) _).mpr rfl)

theorem pair_injective (hℳ : Theory.Models ℳ theory) {a b c d : Carrier ℳ} (hEqual : pair hℳ a b = pair hℳ c d) : a = c ∧ b = d :=
  PureKuratowski.code_injective (hEqual ▸ pair_code hℳ a b) (pair_code hℳ c d)

theorem tag_natural (hℳ : Theory.Models ℳ theory) (kind : Kind) : membership ℳ (tag hℳ kind) (omega hℳ) := by
  cases kind
  · change membership ℳ ((E hℳ).function .emptySet .nil) _
    rw [zero_eq hℳ]; exact zero_mem hℳ
  · change membership ℳ ((E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil)) _
    rw [succ_eq hℳ,zero_eq hℳ]; exact succ_mem hℳ (zero_mem hℳ)
  · change membership ℳ ((E hℳ).function .successor (.cons ((E hℳ).function .successor (.cons ((E hℳ).function .emptySet .nil) .nil)) .nil)) _
    simp only [succ_eq hℳ,zero_eq hℳ]
    exact succ_mem hℳ (succ_mem hℳ (zero_mem hℳ))

theorem condition_bounded (hℳ : Theory.Models ℳ theory) {state : Carrier ℳ} (kind : Kind) {depth length code : Carrier ℳ}
    (hCondition : Condition hℳ state kind depth length code) :
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

noncomputable abbrev product (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :=
  (E hℳ).function .cartesianProduct (.cons left (.cons right .nil))
noncomputable def ambient (hℳ : Theory.Models ℳ theory) :=
  product hℳ (omega hℳ) (product hℳ (omega hℳ) (product hℳ (omega hℳ) (omega hℳ)))

theorem pair_mem_product (hℳ : Theory.Models ℳ theory) {a b left right : Carrier ℳ}
    (hLeft : membership ℳ a left) (hRight : membership ℳ b right) : membership ℳ (pair hℳ a b) (product hℳ left right) :=
  ((PureMappingDefinitions.cartesian_correct _ left right).mp
    (((PureRoundTwoStage.realizes hℳ).function .cartesianProduct (.cons left (.cons right .nil)) _).mpr rfl) _).mpr
      ⟨a,hLeft,b,hRight,pair_code hℳ a b⟩

theorem body_bounded (hℳ : Theory.Models ℳ theory) (state output : Carrier ℳ)
    (hOutput : PureLeastFixedPoint.Holds body .nil state output) : membership ℳ output (ambient hℳ) := by
  obtain ⟨kind,depth,length,code,rfl,hCondition⟩ := (body_correct hℳ state output).mp hOutput
  have h := condition_bounded hℳ kind hCondition
  exact pair_mem_product hℳ (tag_natural hℳ kind) (pair_mem_product hℳ h.1 (pair_mem_product hℳ h.2.1 h.2.2))

theorem dependencies_covered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered step = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSyntaxOperator
