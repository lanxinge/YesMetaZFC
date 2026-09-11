import YesMetaZFC.Model.ZFC.Pure.PureNaturalRelations
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticSemantics

/-! # 第二轮统一扩张中的原规格

极值函数和自然数关系使用同一个具体扩张。第一轮已完成定义的解释保持不变，
这里将原极值 guard 接到扩张实际选择的函数值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageTwoSemantics
open PureModel PureOrderExtrema
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion PureNaturalRelations.interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (PureNaturalRelations.functional hℳ)

theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) :=
  expansion_realizes (PureNaturalRelations.functional hℳ)

/-- 第二轮新增关系不会改变第一轮关系的原正文。 -/
theorem inherited_definition_correct (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureRoundOneRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (Nonlogical.BasicSetTheory.signature.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureRoundOneRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureRoundOneRelations.condition primitive)
    (PureNaturalRelations.inherited_graph_equation primitive) args

theorem minimum_of_wellOrder (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ)
    (hOrder : (expansion hℳ).relation .isWellOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (expansion hℳ).model element subset → Mem (expansion hℳ).model element carrier)
    (hNonempty : subset ≠ (expansion hℳ).function .emptySet .nil) :
    output = (expansion hℳ).function .minimum (.cons relation (.cons subset .nil)) ↔
      Extreme (expansion hℳ).model .minimum relation subset output := by
  apply ((realizes hℳ).function .minimum (.cons relation (.cons subset .nil)) output).symm.trans
  exact (PureOrderExtrema.minimum_spec_of_wellOrder hℳ relation carrier subset output hOrder hSubset hNonempty).trans
    (specification_correct (PureStageSemantics.expansion hℳ).model .minimum output relation subset)

theorem minimum_of_naturalOrder (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ)
    (hOrder : (expansion hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (expansion hℳ).model element subset → Mem (expansion hℳ).model element carrier)
    (hNonempty : subset ≠ (expansion hℳ).function .emptySet .nil) :
    output = (expansion hℳ).function .minimum (.cons relation (.cons subset .nil)) ↔
      Extreme (expansion hℳ).model .minimum relation subset output := by
  apply ((realizes hℳ).function .minimum (.cons relation (.cons subset .nil)) output).symm.trans
  exact (PureOrderExtrema.spec_of_naturalOrder hℳ .minimum relation carrier subset output hOrder hSubset hNonempty).trans
    (specification_correct (PureStageSemantics.expansion hℳ).model .minimum output relation subset)

theorem maximum_of_naturalOrder (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ)
    (hOrder : (expansion hℳ).relation .isNaturalDiscreteLinearOrder (.cons relation (.cons carrier .nil)))
    (hSubset : ∀ element, Mem (expansion hℳ).model element subset → Mem (expansion hℳ).model element carrier)
    (hNonempty : subset ≠ (expansion hℳ).function .emptySet .nil) :
    output = (expansion hℳ).function .maximum (.cons relation (.cons subset .nil)) ↔
      Extreme (expansion hℳ).model .maximum relation subset output := by
  apply ((realizes hℳ).function .maximum (.cons relation (.cons subset .nil)) output).symm.trans
  exact (PureOrderExtrema.spec_of_naturalOrder hℳ .maximum relation carrier subset output hOrder hSubset hNonempty).trans
    (specification_correct (PureStageSemantics.expansion hℳ).model .maximum output relation subset)


/-- 统一扩张满足原良序最小元的每一个定义实例。 -/
theorem minimum_definition_correct (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.minimum_linear_order_definition_instance
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons subset (.cons carrier (.cons relation .nil)))) :
        Env (expansion hℳ).model [] [s, s, s, s]) := by
  simp only [Nonlogical.BasicSetTheory.minimum_linear_order_definition_instance, Formula.satisfies]
  intro h
  exact (minimum_of_wellOrder hℳ relation carrier subset output h.1 h.2.1 h.2.2).trans
    (specification_correct (expansion hℳ).model .minimum output relation subset).symm

/-- 自然离散序的两个原极值定义分别由相应存在性给出。 -/
theorem minimum_natural_definition_correct (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.minimum_natural_order_definition_instance
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons subset (.cons carrier (.cons relation .nil)))) :
        Env (expansion hℳ).model [] [s, s, s, s]) := by
  simp only [Nonlogical.BasicSetTheory.minimum_natural_order_definition_instance, Formula.satisfies]
  intro h
  exact (minimum_of_naturalOrder hℳ relation carrier subset output h.1 h.2.1 h.2.2).trans
    (specification_correct (expansion hℳ).model .minimum output relation subset).symm

theorem maximum_natural_definition_correct (hℳ : Theory.Models ℳ theory)
    (relation carrier subset output : Carrier ℳ) :
    (Nonlogical.BasicSetTheory.maximum_natural_order_definition_instance
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons subset (.cons carrier (.cons relation .nil)))) :
        Env (expansion hℳ).model [] [s, s, s, s]) := by
  simp only [Nonlogical.BasicSetTheory.maximum_natural_order_definition_instance, Formula.satisfies]
  intro h
  exact (maximum_of_naturalOrder hℳ relation carrier subset output h.1 h.2.1 h.2.2).trans
    (specification_correct (expansion hℳ).model .maximum output relation subset).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStageTwoSemantics
