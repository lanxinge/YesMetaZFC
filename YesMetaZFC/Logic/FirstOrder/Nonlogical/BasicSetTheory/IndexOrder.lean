import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderProductMapping

/-!
# 最小差异点与指数序

本模块把最小差异点与指数序直接写成内在类型对象语言公式。指数序的存在性使用
参数化分离 schema，不再为固定变量编号维护闭分离公理、良构证明或证书边界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 最小差异点 -/

def minimum_difference_spec {bound free : SetContext}
    (sourceRelation sourceCarrier firstFunction secondFunction candidate :
      SetTerm bound free) : SetFormula bound free :=
  let earlier : SetTerm (SetSort.set :: bound) free := .bvar .here
  let sourceRelation' := sourceRelation.weakenBound SetSort.set
  let sourceCarrier' := sourceCarrier.weakenBound SetSort.set
  let firstFunction' := firstFunction.weakenBound SetSort.set
  let secondFunction' := secondFunction.weakenBound SetSort.set
  (candidate ∈ₘ sourceCarrier) ∧ₘ
    (((firstFunction ·ₘ candidate) ≠ₘ (secondFunction ·ₘ candidate)) ∧ₘ
      (((earlier ∈ₘ sourceCarrier') ∧ₘ
          (⟨earlier, candidate.weakenBound SetSort.set⟩ₘ ∈ₘ sourceRelation')) ⟶ₘ
        ((firstFunction' ·ₘ earlier) ≐ₘ (secondFunction' ·ₘ earlier))).forallE
        SetSort.set)

def minimum_difference_definition_instance {bound free : SetContext}
    (sourceRelation sourceCarrier target
      firstFunction secondFunction candidate : SetTerm bound free) :
    SetFormula bound free :=
  (is_well_order_formula sourceRelation sourceCarrier ∧ₘ
      ((is_mapping_formula firstFunction sourceCarrier target ∧ₘ
          is_mapping_formula secondFunction sourceCarrier target) ∧ₘ
        (firstFunction ≠ₘ secondFunction))) ⟶ₘ
    ((candidate ≐ₘ min_diffₘ(sourceRelation, sourceCarrier, firstFunction, secondFunction)) ↔ₘ
      minimum_difference_spec sourceRelation sourceCarrier
        firstFunction secondFunction candidate)

def minimum_difference_definition_axiom : SetSentence :=
  let free :=
    [SetSort.set, SetSort.set, SetSort.set,
      SetSort.set, SetSort.set, SetSort.set]
  let sourceRelation : SetOpenTerm free :=
    .fvar (.there (.there (.there (.there (.there .here)))))
  let sourceCarrier : SetOpenTerm free :=
    .fvar (.there (.there (.there (.there .here))))
  let target : SetOpenTerm free :=
    .fvar (.there (.there (.there .here)))
  let firstFunction : SetOpenTerm free :=
    .fvar (.there (.there .here))
  let secondFunction : SetOpenTerm free :=
    .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (minimum_difference_definition_instance
      sourceRelation sourceCarrier target
      firstFunction secondFunction candidate)

/-! ## 指数序 -/

def index_order_member_condition {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation functionPair :
      SetTerm bound free) : SetFormula bound free :=
  let point : SetTerm bound (SetSort.set :: free) := .fvar .here
  let functionPair' := functionPair.weakenFree SetSort.set
  let firstFunction : SetTerm bound (SetSort.set :: free) :=
    (functionPair')₀ₘ
  let secondFunction : SetTerm bound (SetSort.set :: free) :=
    (functionPair')₁ₘ
  let point' : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let functionPair'' := functionPair'.weakenFree SetSort.set
  let firstFunction' : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    (functionPair'')₀ₘ
  let secondFunction' : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    (functionPair'')₁ₘ
  let sourceRelation' := sourceRelation.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let sourceCarrier' := sourceCarrier.weakenFree SetSort.set
    |>.weakenFree SetSort.set
  let earlier : SetTerm bound (SetSort.set :: SetSort.set :: free) :=
    .fvar .here
  let minimality :=
    (((earlier ∈ₘ sourceCarrier') ∧ₘ
        (⟨earlier, point'⟩ₘ ∈ₘ sourceRelation')) ⟶ₘ
      ((firstFunction' ·ₘ earlier) ≐ₘ
        (secondFunction' ·ₘ earlier))).forallFreeTop SetSort.set
  let point_body :=
    (point ∈ₘ sourceCarrier.weakenFree SetSort.set) ∧ₘ
      (((firstFunction ·ₘ point) ≠ₘ (secondFunction ·ₘ point)) ∧ₘ
        (minimality ∧ₘ
          (⟨firstFunction ·ₘ point, secondFunction ·ₘ point⟩ₘ ∈ₘ
            targetRelation.weakenFree SetSort.set)))
  point_body.existsFreeTop SetSort.set

def index_order_spec {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  let functionPair : SetTerm bound (SetSort.set :: free) := .fvar .here
  let sourceCarrier' := sourceCarrier.weakenFree SetSort.set
  let targetCarrier' := targetCarrier.weakenFree SetSort.set
  membership_specification candidate
    ((functionPair ∈ₘ (Mapₘ(sourceCarrier', targetCarrier') ×ₘ
        Mapₘ(sourceCarrier', targetCarrier'))) ∧ₘ
      index_order_member_condition
        (sourceRelation.weakenFree SetSort.set)
        sourceCarrier'
        (targetRelation.weakenFree SetSort.set)
        functionPair)

def index_order_separation_exists {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier :
      SetTerm bound free) : SetFormula bound free :=
  let candidate : SetTerm bound (SetSort.set :: free) := .fvar .here
  (index_order_spec
    (sourceRelation.weakenFree SetSort.set)
    (sourceCarrier.weakenFree SetSort.set)
    (targetRelation.weakenFree SetSort.set)
    (targetCarrier.weakenFree SetSort.set)
    candidate).existsFreeTop SetSort.set

def index_order_predicate {free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier :
      SetOpenTerm free) : SetPredicate free where
  body :=
    let functionPair : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest
        (σ := signature) (free := free) SetSort.set
    let sourceCarrier' := sourceCarrier.weakenFree SetSort.set
    let targetCarrier' := targetCarrier.weakenFree SetSort.set
    ((functionPair ∈ₘ (Mapₘ(sourceCarrier', targetCarrier') ×ₘ
        Mapₘ(sourceCarrier', targetCarrier'))) ∧ₘ
      index_order_member_condition
        (sourceRelation.weakenFree SetSort.set)
        sourceCarrier'
        (targetRelation.weakenFree SetSort.set)
        functionPair).abstractFreeTop

def index_order_definition_instance {bound free : SetContext}
    (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm bound free) : SetFormula bound free :=
  (is_well_order_formula sourceRelation sourceCarrier ∧ₘ
      is_well_order_formula targetRelation targetCarrier) ⟶ₘ
    ((candidate ≐ₘ idx_ordₘ(
        sourceRelation, sourceCarrier,
        targetRelation, targetCarrier)) ↔ₘ
      index_order_spec sourceRelation sourceCarrier
        targetRelation targetCarrier candidate)

def index_order_definition_axiom : SetSentence :=
  let free :=
    [SetSort.set, SetSort.set, SetSort.set,
      SetSort.set, SetSort.set]
  let sourceRelation : SetOpenTerm free :=
    .fvar (.there (.there (.there (.there .here))))
  let sourceCarrier : SetOpenTerm free :=
    .fvar (.there (.there (.there .here)))
  let targetRelation : SetOpenTerm free :=
    .fvar (.there (.there .here))
  let targetCarrier : SetOpenTerm free :=
    .fvar (.there .here)
  let candidate : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (index_order_definition_instance
      sourceRelation sourceCarrier targetRelation targetCarrier candidate)

/-! ## 理论组合与嵌入 -/

def minimum_difference_theory : SetTheory :=
  Theory.insert minimum_difference_definition_axiom order_operator_theory

def index_order_separation_theory : SetTheory :=
  fun sentence =>
    (∃ (free : SetContext)
      (sourceRelation sourceCarrier targetRelation targetCarrier :
        SetOpenTerm free),
      sentence =
        (index_order_predicate sourceRelation sourceCarrier
          targetRelation targetCarrier).separation_axiom) ∨
    minimum_difference_theory sentence

def index_order_theory : SetTheory :=
  Theory.insert index_order_definition_axiom index_order_separation_theory

derive_theory_subset order_operator_theory ⊆ minimum_difference_theory

derive_theory_subset minimum_difference_theory ⊆ index_order_separation_theory

derive_theory_subset index_order_separation_theory ⊆ index_order_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
