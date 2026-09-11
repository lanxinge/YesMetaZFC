import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRelatedStage
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureTotalCodeBounds

/-! # 固定结构及赋值参数上的互递归求值算子

四个外层参数逐组保留，不收集模型中的全部结构。项值落在载体内，项列输出
由原总化码构造落在内部 ω，故带标签的三坐标关系有统一集合界。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueOperator
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation
open Nonlogical.BasicSetTheory FormalSystem
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
open PureSyntaxOperator (Kind tupleTerm tuple tag pair_mem_product product tag_natural)

/-- 只对第三轮的三个新函数选择值，保留基础函数的既定取值。 -/
noncomputable def E (hℳ : Theory.Models ℳ theory) : Expansion PureRelatedStage.interpretation ℳ where
  function symbol args := match symbol with
    | .relatedNonlogicalSymbolSet => (PureRelatedStage.expansion hℳ).function .relatedNonlogicalSymbolSet args
    | .relatedTermSet => (PureRelatedStage.expansion hℳ).function .relatedTermSet args
    | .relatedFormulaSet => (PureRelatedStage.expansion hℳ).function .relatedFormulaSet args
    | symbol => (PureRoundTwoStage.expansion hℳ).function symbol args
  relation := (PureRelatedStage.expansion hℳ).relation

theorem round_two_map_values {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues PureRelatedStage.interpretation args = mapValues PureRoundTwoStage.interpretation args := rfl

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (E hℳ) where
  function symbol args output := by
    cases symbol
    case relatedNonlogicalSymbolSet => exact (PureRelatedStage.realizes hℳ).function _ args output
    case relatedTermSet => exact (PureRelatedStage.realizes hℳ).function _ args output
    case relatedFormulaSet => exact (PureRelatedStage.realizes hℳ).function _ args output
    all_goals
      rw [round_two_map_values]
      exact (PureRoundTwoStage.realizes hℳ).function _ args output
  relation symbol args := (PureRelatedStage.realizes hℳ).relation symbol args

theorem zero_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .emptySet .nil = zero hℳ := PureSyntaxOperator.zero_eq hℳ
theorem omega_eq (hℳ : Theory.Models ℳ theory) : (E hℳ).function .omega .nil = omega hℳ := PureSyntaxOperator.omega_eq hℳ
theorem succ_eq (hℳ : Theory.Models ℳ theory) (input : Carrier ℳ) : (E hℳ).function .successor (.cons input .nil) = succ hℳ input := PureSyntaxOperator.succ_eq hℳ input

theorem tuple_eval (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (kind : Kind) (length code result : Term S bound free s) :
    (tupleTerm kind length code result).eval env = tuple hℳ kind (length.eval env) (code.eval env) (result.eval env) := by cases kind <;> rfl

def selected : RelationSymbol → Bool
  | .termValue | .termListValue => true
  | _ => false
def replace : PredicateExpansion.Replacements S s := fun state symbol args =>
  match symbol,args with
  | .termValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons code (.cons result .nil))))) =>
    membership_formula (tupleTerm .term empty_set_term code result) state
  | .termListValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons length (.cons code (.cons result .nil)))))) =>
    membership_formula (tupleTerm .termList length code result) state
  | symbol,args => .rel symbol args
noncomputable def relations (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) : PredicateExpansion.Relations (E hℳ).model := fun symbol args =>
  match symbol,args with
  | .termValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons code (.cons result .nil))))) =>
    membership ℳ (tuple hℳ .term (zero hℳ) code result) state
  | .termListValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons length (.cons code (.cons result .nil)))))) =>
    membership ℳ (tuple hℳ .termList length code result) state
  | symbol,args => (E hℳ).relation symbol args

/-- 原子替换的语义先在抽象源结构中核验，避免把模型选择项展开进证明。 -/
def sourceTuple (𝒩 : Structure.{0,0,0,x} S) (kind : Kind) (length code result : 𝒩.Carrier s) : 𝒩.Carrier s :=
  (tupleTerm kind (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).eval
    (templateEnv (.cons length (.cons code (.cons result .nil))) : Env 𝒩 [] [s,s,s])
def sourceRelations (𝒩 : Structure.{0,0,0,x} S) (state : 𝒩.Carrier s) : PredicateExpansion.Relations 𝒩 := fun symbol args =>
  match symbol,args with
  | .termValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons code (.cons result .nil))))) =>
    𝒩.relInterp .membership (.cons (sourceTuple 𝒩 .term (𝒩.funcInterp .emptySet .nil) code result) (.cons state .nil))
  | .termListValue,.cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons length (.cons code (.cons result .nil)))))) =>
    𝒩.relInterp .membership (.cons (sourceTuple 𝒩 .termList length code result) (.cons state .nil))
  | symbol,args => 𝒩.relInterp symbol args

theorem source_replace_correct (𝒩 : Structure.{0,0,0,x} S) {bound free : SortContext S}
    (env : Env 𝒩 bound free) (state : Term S bound free s) (symbol : RelationSymbol)
    (args : Arguments S bound free (S.relDomain symbol)) :
    (replace state symbol args).satisfies env ↔ sourceRelations 𝒩 (state.eval env) symbol (args.eval env) := by
  cases symbol
  case termValue =>
    match args with
    | .cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons code (.cons result .nil))))) => rfl
  case termListValue =>
    match args with
    | .cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons length (.cons code (.cons result .nil)))))) => rfl
  all_goals rfl

theorem source_relations_actual (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ)
    (symbol : RelationSymbol) (args : Values (E hℳ).model.Carrier (S.relDomain symbol)) :
    sourceRelations (E hℳ).model state symbol args ↔ relations hℳ state symbol args := by
  cases symbol
  case termValue =>
    match args with
    | .cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons code (.cons result .nil))))) =>
      change membership ℳ ((tupleTerm .term empty_set_term (.fvar .here) (.fvar (.there .here))).eval
        (templateEnv (.cons code (.cons result .nil)) : Env (E hℳ).model [] [s,s])) state ↔ _
      rw [tuple_eval hℳ]
      change membership ℳ (tuple hℳ .term ((E hℳ).function .emptySet .nil) code result) state ↔ _
      rw [zero_eq hℳ]; rfl
  case termListValue =>
    match args with
    | .cons _carrier (.cons _interpretation (.cons _symbols (.cons _assignment (.cons length (.cons code (.cons result .nil)))))) =>
      change membership ℳ ((tupleTerm .termList (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).eval
        (templateEnv (.cons length (.cons code (.cons result .nil))) : Env (E hℳ).model [] [s,s,s])) state ↔ _
      rw [tuple_eval hℳ]; rfl
  all_goals rfl

theorem replace_correct (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (state : Term S bound free s) (symbol : RelationSymbol)
    (args : Arguments S bound free (S.relDomain symbol)) :
    (replace state symbol args).satisfies env ↔ relations hℳ (state.eval env) symbol (args.eval env) :=
  (source_replace_correct (E hℳ).model env state symbol args).trans
    (source_relations_actual hℳ (state.eval env) symbol (args.eval env))

def condition (kind : Kind) : Formula S [] [s,s,s,s,s,s,s] :=
  let carrier := (.fvar (.there (.there (.there .here))))
  let interpretation := (.fvar (.there (.there (.there (.there .here)))))
  let symbols := (.fvar (.there (.there (.there (.there (.there .here))))))
  let assignment := (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
  let length := (.fvar .here)
  let code := (.fvar (.there .here))
  let result := (.fvar (.there (.there .here)))
  match kind with
  | .term => .conj (.equal length empty_set_term) (term_value_condition carrier interpretation symbols assignment code result)
  | .termList => term_list_value_condition carrier interpretation symbols assignment length code result
  | .formula => .falsum
noncomputable def Condition (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) (kind : Kind)
    (carrier interpretation symbols assignment length code result : Carrier ℳ) : Prop :=
  PredicateExpansion.evaluate (relations hℳ state) (templateEnv (.cons length (.cons code (.cons result (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))))) (condition kind)
theorem positive (kind : Kind) : PredicateExpansion.positive selected (condition kind) = true := by cases kind <;> rfl

theorem condition_mono (hℳ : Theory.Models ℳ theory) {first second : Carrier ℳ}
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second)
    (kind : Kind) (carrier interpretation symbols assignment length code result : Carrier ℳ) :
    Condition hℳ first kind carrier interpretation symbols assignment length code result → Condition hℳ second kind carrier interpretation symbols assignment length code result := by
  apply PredicateExpansion.monotone selected (relations hℳ first) (relations hℳ second) ?_ ?_ _ _ (positive kind)
  · intro symbol args
    cases symbol
    case termValue =>
      cases args with | cons a0 tail0 =>
      cases tail0 with | cons a1 tail1 =>
      cases tail1 with | cons a2 tail2 =>
      cases tail2 with | cons a3 tail3 =>
      cases tail3 with | cons a4 tail4 =>
      cases tail4 with | cons a5 tail5 =>
      cases tail5
      exact hSubset _
    case termListValue =>
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

def branch (kind : Kind) : Formula S [] [s,s,s,s,s,s] :=
  .existsE s <| .existsE s <| .existsE s <|
  .conj (.equal (.fvar .here) (tupleTerm kind (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))
    (PredicateExpansion.expand replace (.fvar (.there .here)) (applyTemplate (condition kind) (.cons (.bvar (.there (.there .here))) (.cons (.bvar (.there .here)) (.cons (.bvar .here) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) .nil)))))))))
def step : Formula S [] [s,s,s,s,s,s] := .disj (branch .term) (.disj (branch .termList) (branch .formula))
def body : Formula ℒ [] [setSort,setSort,setSort,setSort,setSort,setSort] := openFormula PureRelatedStage.interpretation step

noncomputable def Step (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment state output : Carrier ℳ) : Prop :=
  ∃ kind length code result, output = tuple hℳ kind length code result ∧ Condition hℳ state kind carrier interpretation symbols assignment length code result

theorem branch_correct (hℳ : Theory.Models ℳ theory) (kind : Kind) (carrier interpretation symbols assignment state output : Carrier ℳ) :
    (branch kind).satisfies (templateEnv (.cons output (.cons state (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))) : Env (E hℳ).model [] [s,s,s,s,s,s]) ↔
      ∃ length code result, output = tuple hℳ kind length code result ∧ Condition hℳ state kind carrier interpretation symbols assignment length code result := by
  change (∃ length code result, _ ∧ _) ↔ _
  apply exists_congr; intro length
  apply exists_congr; intro code
  apply exists_congr; intro result
  apply and_congr
  · change output = (tupleTerm kind (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).eval
      ((((templateEnv (.cons output (.cons state (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))))) : Env (E hℳ).model [] [s,s,s,s,s,s]).pushBound length).pushBound code).pushBound result) ↔ _
    rw [tuple_eval hℳ]; rfl
  · apply (PredicateExpansion.expand_correct replace (relations hℳ) (replace_correct hℳ) _ _ _).trans
    exact PredicateExpansion.evaluate_applyTemplate (relations hℳ state) _ _ _

theorem body_correct (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment state output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) state output ↔ Step hℳ carrier interpretation symbols assignment state output := by
  apply (openFormula_correct (E hℳ) (realizes hℳ) step (.cons output (.cons state (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil))))))).trans
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

theorem body_mono (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment first second : Carrier ℳ)
    (hSubset : ∀ element, membership ℳ element first → membership ℳ element second) (output : Carrier ℳ) :
    PureLeastFixedPoint.Holds body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) first output → PureLeastFixedPoint.Holds body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) second output := by
  intro h
  obtain ⟨kind,length,code,result,hEqual,h⟩ := (body_correct hℳ carrier interpretation symbols assignment first output).mp h
  exact (body_correct hℳ carrier interpretation symbols assignment second output).mpr
    ⟨kind,length,code,result,hEqual,condition_mono hℳ hSubset kind carrier interpretation symbols assignment length code result h⟩

noncomputable def resultRange (hℳ : Theory.Models ℳ theory) (carrier : Carrier ℳ) : Carrier ℳ :=
  (E hℳ).function .binaryUnion (.cons carrier (.cons (omega hℳ) .nil))
theorem resultRange_correct (hℳ : Theory.Models ℳ theory) (carrier result : Carrier ℳ) :
    membership ℳ result (resultRange hℳ carrier) ↔ membership ℳ result carrier ∨ membership ℳ result (omega hℳ) :=
  (PureRelationSetOperations.binaryUnion_correct hℳ _ carrier (omega hℳ)).mp
    (((realizes hℳ).function .binaryUnion (.cons carrier (.cons (omega hℳ) .nil)) _).mpr rfl) result
noncomputable def ambient (hℳ : Theory.Models ℳ theory) (carrier : Carrier ℳ) :=
  product hℳ (omega hℳ) (product hℳ (omega hℳ) (product hℳ (omega hℳ) (resultRange hℳ carrier)))

theorem term_set_bounded (hℳ : Theory.Models ℳ theory) (symbols code : Carrier ℳ)
    (h : membership ℳ code ((E hℳ).function .relatedTermSet (.cons symbols .nil))) : membership ℳ code (omega hℳ) :=
  PureRelatedSyntaxSets.member_bounded hℳ .term symbols code
    (((PureFunctionDefinitions.comprehension_correct (PureRelatedSyntaxSets.member .term) (.cons symbols .nil) _).mp
      (((realizes hℳ).function .relatedTermSet (.cons symbols .nil) _).mpr rfl) code).mp h)

/-- 原项列构造无论字段是否合法，都由所选总化编码返回内部自然数。 -/
abbrev structural_nil_code_term {bound free : SortContext S} : Term S bound free s := structural_list_code_term []
abbrev structural_cons_code_term {bound free : SortContext S} (head tail : Term S bound free s) : Term S bound free s :=
  structural_raw_node_code_term .listCons (godel_pairing_term head tail)

theorem nil_bounded (hℳ : Theory.Models ℳ theory) :
    membership ℳ ((structural_nil_code_term : Term S [] [] s).eval (templateEnv .nil : Env (E hℳ).model [] [])) (omega hℳ) :=
  PureTotalCodeBounds.raw_node hℳ (templateEnv .nil : Env (PureSyntaxStage.expansion hℳ).model [] []) .listNil empty_set_term
theorem cons_bounded (hℳ : Theory.Models ℳ theory) (head tail : Carrier ℳ) :
    membership ℳ ((structural_cons_code_term (.fvar .here) (.fvar (.there .here))).eval
      (templateEnv (.cons head (.cons tail .nil)) : Env (E hℳ).model [] [s,s])) (omega hℳ) :=
  PureTotalCodeBounds.raw_node hℳ (templateEnv (.cons head (.cons tail .nil)) : Env (PureSyntaxStage.expansion hℳ).model [] [s,s]) .listCons (godel_pairing_term (.fvar .here) (.fvar (.there .here)))

theorem condition_bounded (hℳ : Theory.Models ℳ theory) (state : Carrier ℳ) (kind : Kind)
    (carrier interpretation symbols assignment length code result : Carrier ℳ) (h : Condition hℳ state kind carrier interpretation symbols assignment length code result) :
    membership ℳ length (omega hℳ) ∧ membership ℳ code (omega hℳ) ∧ membership ℳ result (resultRange hℳ carrier) := by
  cases kind
  case term =>
    change (length = (E hℳ).function .emptySet .nil ∧ (_ ∧ ((membership ℳ code ((E hℳ).function .relatedTermSet (.cons symbols .nil)) ∧ membership ℳ result carrier) ∧ _))) at h
    have hLength := h.1
    rw [zero_eq hℳ] at hLength
    exact ⟨hLength.symm ▸ zero_mem hℳ,term_set_bounded hℳ symbols code h.2.2.1.1,
      (resultRange_correct hℳ carrier result).mpr (Or.inl h.2.2.1.2)⟩
  case termList =>
    change ((length = (E hℳ).function .emptySet .nil ∧ (code = (structural_nil_code_term : Term S [] [] s).eval (templateEnv .nil : Env (E hℳ).model [] []) ∧ result = (structural_nil_code_term : Term S [] [] s).eval (templateEnv .nil : Env (E hℳ).model [] []))) ∨
      ∃ previous head tail headValue tailValues, (((membership ℳ previous ((E hℳ).function .omega .nil) ∧ length = (E hℳ).function .successor (.cons previous .nil)) ∧
        (code = (structural_cons_code_term (.fvar .here) (.fvar (.there .here))).eval (templateEnv (.cons head (.cons tail .nil)) : Env (E hℳ).model [] [s,s]) ∧
        result = (structural_cons_code_term (.fvar .here) (.fvar (.there .here))).eval (templateEnv (.cons headValue (.cons tailValues .nil)) : Env (E hℳ).model [] [s,s]))) ∧ _)) at h
    rcases h with ⟨hLength,rfl,rfl⟩ | ⟨previous,head,tail,headValue,tailValues,⟨⟨hPrevious,hLength⟩,hCode,hResult⟩,_⟩
    · rw [zero_eq hℳ] at hLength
      exact ⟨hLength.symm ▸ zero_mem hℳ,nil_bounded hℳ,(resultRange_correct hℳ carrier _).mpr (Or.inr (nil_bounded hℳ))⟩
    · rw [omega_eq hℳ] at hPrevious
      rw [succ_eq hℳ] at hLength
      exact ⟨hLength.symm ▸ succ_mem hℳ hPrevious,hCode.symm ▸ cons_bounded hℳ head tail,
        (resultRange_correct hℳ carrier result).mpr (Or.inr (hResult.symm ▸ cons_bounded hℳ headValue tailValues))⟩
  case formula => exact False.elim h

theorem body_bounded (hℳ : Theory.Models ℳ theory) (carrier interpretation symbols assignment state output : Carrier ℳ)
    (h : PureLeastFixedPoint.Holds body (.cons carrier (.cons interpretation (.cons symbols (.cons assignment .nil)))) state output) : membership ℳ output (ambient hℳ carrier) := by
  obtain ⟨kind,length,code,result,rfl,hCondition⟩ := (body_correct hℳ carrier interpretation symbols assignment state output).mp h
  have h := condition_bounded hℳ state kind carrier interpretation symbols assignment length code result hCondition
  exact pair_mem_product hℳ (tag_natural hℳ kind) (pair_mem_product hℳ h.1 (pair_mem_product hℳ h.2.1 h.2.2))

theorem dependencies_covered : formulaCovered PureRelatedStage.functionCovered PureRelatedStage.relationCovered step = true := rfl
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureValueOperator
