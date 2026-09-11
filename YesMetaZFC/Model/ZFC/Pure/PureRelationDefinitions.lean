import YesMetaZFC.Model.ZFC.Pure.PureFunctionDefinitions
import YesMetaZFC.Model.ZFC.Pure.PureKuratowski
import YesMetaZFC.Model.Interpretation.TotalizedGraph

/-! # 有序对、关系和函数的纯语言定义

所有语法均在当前类型化纯签名 ℒ 上构造。关系谓词完全展开到隶属与等号；函数图
以输出为首槽，合法输入精确保留原规格，非法输入规范返回空集。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationDefinitions
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x

abbrev PureTerm (bound free : SortContext ℒ) := Term ℒ bound free setSort

def mem {bound free : SortContext ℒ} (left right : PureTerm bound free) : Formula ℒ bound free :=
  .rel _root_.YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))

def pair {bound free : SortContext ℒ} (output left right : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate (PureFunctionDefinitions.graph .unorderedPair) (.cons output (.cons left (.cons right .nil)))

def single {bound free : SortContext ℒ} (output element : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate (PureFunctionDefinitions.graph .singleton) (.cons output (.cons element .nil))

theorem pair_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (output left right : PureTerm bound free) :
    (pair output left right).satisfies env ↔ PureKuratowski.Pair ℳ (output.eval env) (left.eval env) (right.eval env) := by
  exact (applyTemplate_satisfies env _ _).trans (PureFunctionDefinitions.pair_correct _ _ _)

theorem single_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (output element : PureTerm bound free) :
    (single output element).satisfies env ↔ PureKuratowski.Single ℳ (output.eval env) (element.eval env) := by
  exact (applyTemplate_satisfies env _ _).trans (PureFunctionDefinitions.singleton_correct _ _)

def orderedPairGraph : Formula ℒ [] [setSort, setSort, setSort] :=
  .existsE setSort <| .existsE setSort <|
    .conj (single (.bvar (.there .here)) (.fvar (.there .here)))
      (.conj (pair (.bvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
        (pair (.fvar .here) (.bvar (.there .here)) (.bvar .here)))

theorem orderedPair_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (output left right : Carrier ℳ) :
    orderedPairGraph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      PureKuratowski.Code ℳ output left right := by
  simp only [orderedPairGraph, Formula.satisfies, pair_satisfies, single_satisfies]
  rfl

def code {bound free : SortContext ℒ} (output left right : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate orderedPairGraph (.cons output (.cons left (.cons right .nil)))

theorem code_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (output left right : PureTerm bound free) :
    (code output left right).satisfies env ↔ PureKuratowski.Code ℳ (output.eval env) (left.eval env) (right.eval env) :=
  (applyTemplate_satisfies env _ _).trans (orderedPair_correct _ _ _)

def isOrderedPairGraph : Formula ℒ [] [setSort] :=
  .existsE setSort <| .existsE setSort <|
    code (.fvar .here) (.bvar (.there .here)) (.bvar .here)

def isOrderedPair {bound free : SortContext ℒ} (input : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate isOrderedPairGraph (.cons input .nil)

theorem isOrderedPair_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (input : PureTerm bound free) :
    (isOrderedPair input).satisfies env ↔ ∃ left right, PureKuratowski.Code ℳ (input.eval env) left right := by
  rw [isOrderedPair, applyTemplate_satisfies]
  simp only [isOrderedPairGraph, Formula.satisfies, code_satisfies]
  rfl

def pairMemberGraph : Formula ℒ [] [setSort, setSort, setSort] :=
  .existsE setSort <| .conj (code (.bvar .here) (.fvar .here) (.fvar (.there .here)))
    (mem (.bvar .here) (.fvar (.there (.there .here))))

def pairMember {bound free : SortContext ℒ} (left right relation : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate pairMemberGraph (.cons left (.cons right (.cons relation .nil)))

theorem pairMember_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (left right relation : PureTerm bound free) :
    (pairMember left right relation).satisfies env ↔
      PureKuratowski.PairMember ℳ (left.eval env) (right.eval env) (relation.eval env) := by
  rw [pairMember, applyTemplate_satisfies]
  simp only [pairMemberGraph, Formula.satisfies, code_satisfies]
  rfl

def isRelationGraph : Formula ℒ [] [setSort] :=
  .forallE setSort <| .imp (mem (.bvar .here) (.fvar .here)) (isOrderedPair (.bvar .here))

def isRelation {bound free : SortContext ℒ} (input : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate isRelationGraph (.cons input .nil)

theorem isRelation_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (input : PureTerm bound free) :
    (isRelation input).satisfies env ↔ PureKuratowski.IsRelation ℳ (input.eval env) := by
  rw [isRelation, applyTemplate_satisfies]
  simp only [isRelationGraph, Formula.satisfies, isOrderedPair_satisfies]
  rfl

def isFunctionGraph : Formula ℒ [] [setSort] :=
  .conj (isRelation (.fvar .here)) <|
    .forallE setSort <| .forallE setSort <| .forallE setSort <|
      .imp (.conj (pairMember (.bvar (.there (.there .here))) (.bvar (.there .here)) (.fvar .here))
        (pairMember (.bvar (.there (.there .here))) (.bvar .here) (.fvar .here)))
        (.equal (.bvar (.there .here)) (.bvar .here))

def isFunction {bound free : SortContext ℒ} (input : PureTerm bound free) : Formula ℒ bound free :=
  applyTemplate isFunctionGraph (.cons input .nil)

theorem isFunction_satisfies {ℳ : Structure.{0, 0, 0, x} ℒ} {bound free : SortContext ℒ}
    (env : Env ℳ bound free) (input : PureTerm bound free) :
    (isFunction input).satisfies env ↔ PureKuratowski.IsFunction ℳ (input.eval env) := by
  rw [isFunction, applyTemplate_satisfies]
  simp only [isFunctionGraph, Formula.satisfies, isRelation_satisfies, pairMember_satisfies, and_imp]
  rfl

def leftBody : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| code (.fvar (.there .here)) (.fvar .here) (.bvar .here)

def rightBody : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| code (.fvar (.there .here)) (.bvar .here) (.fvar .here)

def applicationBody : Formula ℒ [] [setSort, setSort, setSort] :=
  .conj (isFunction (.fvar (.there .here)))
    (pairMember (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))

theorem left_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (output input : Carrier ℳ) :
    leftBody.satisfies (templateEnv (.cons output (.cons input .nil))) ↔ PureKuratowski.Left ℳ output input := by
  simp only [leftBody, Formula.satisfies, code_satisfies]
  rfl

theorem right_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (output input : Carrier ℳ) :
    rightBody.satisfies (templateEnv (.cons output (.cons input .nil))) ↔ PureKuratowski.Right ℳ output input := by
  simp only [rightBody, Formula.satisfies, code_satisfies]
  rfl

theorem application_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (output function input : Carrier ℳ) :
    applicationBody.satisfies (templateEnv (.cons output (.cons function (.cons input .nil)))) ↔
      PureKuratowski.Application ℳ output function input := by
  simp only [applicationBody, Formula.satisfies, isFunction_satisfies, pairMember_satisfies]
  rfl

def subsetGraph : Formula ℒ [] [setSort, setSort] :=
  .forallE setSort <| .imp (mem (.bvar .here) (.fvar .here)) (mem (.bvar .here) (.fvar (.there .here)))

theorem subset_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (left right : Carrier ℳ) :
    subsetGraph.satisfies (templateEnv (.cons left (.cons right .nil))) ↔
      ∀ element, membership ℳ element left → membership ℳ element right := Iff.rfl

/-- 已有纯定义的关系以原扩展签名为索引。 -/
inductive RelationPrimitive : Nonlogical.BasicSetTheory.RelationSymbol → Type where
  | membership : RelationPrimitive .membership
  | subset : RelationPrimitive .subset
  | isOrderedPair : RelationPrimitive .isOrderedPair
  | isRelation : RelationPrimitive .isRelation
  | isFunction : RelationPrimitive .isFunction

def relationGraph {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : RelationPrimitive symbol) :
    Formula ℒ [] ((Nonlogical.BasicSetTheory.signature.relDomain symbol).map (fun _ => setSort)) :=
  match primitive with
  | .membership => mem (.fvar .here) (.fvar (.there .here))
  | .subset => subsetGraph
  | .isOrderedPair => isOrderedPairGraph
  | .isRelation => isRelationGraph
  | .isFunction => isFunctionGraph

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationDefinitions
