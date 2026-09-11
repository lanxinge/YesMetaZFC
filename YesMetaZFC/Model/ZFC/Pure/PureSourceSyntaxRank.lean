import YesMetaZFC.Automation.ObjectSyntaxReflection
import YesMetaZFC.Model.ZFC.Pure.PureSourceHornElimination

/-! # 一般语法规则在任意源模型中的秩下降

行的固定外壳可由编码单射性反演；秩和所有字段均可为非标准自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceSyntaxRank
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceHornConstruction
open _root_.YesMetaZFC.Automation ObjectSyntaxReflection ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Value (𝒩 : Structure.{0,0,0,x} signature) (row : Row (𝒩.Carrier .set)) : 𝒩.Carrier .set :=
  node 𝒩 row.tag row.fields
def Natural (𝒩 : Structure.{0,0,0,x} signature) (row : Row (𝒩.Carrier .set)) : Prop :=
  ∀ value ∈ row.fields, mem 𝒩 value (w 𝒩)

theorem value_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {row : Row (𝒩.Carrier .set)} (hr : Natural 𝒩 row) : mem 𝒩 (Value 𝒩 row) (w 𝒩) :=
  node_natural h𝒩 row.tag hr

theorem input_natural {row : Row (𝒩.Carrier .set)} (hr : Natural 𝒩 row) :
    mem 𝒩 row.input (w 𝒩) := hr _ row.input_mem

theorem map_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    (values : Fin n → 𝒩.Carrier .set) (hv : ∀ i, mem 𝒩 (values i) (w 𝒩)) (row : Row (ObjectHorn.Expr n)) :
    Natural 𝒩 (row.map (exprValue 𝒩 values)) := by
  intro value hValue
  rw [Row.map_fields] at hValue
  obtain ⟨expr, _, rfl⟩ := List.mem_map.mp hValue
  exact PureSourceHorn.expr_natural h𝒩 hv expr

theorem value_map {n : Nat} (values : Fin n → 𝒩.Carrier .set) (row : Row (ObjectHorn.Expr n)) :
    Value 𝒩 (row.map (exprValue 𝒩 values)) = exprValue 𝒩 values row.expr := by
  rw [Value, Row.map_tag, Row.map_fields, Row.expr, expr_node]

theorem rank_unique (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : Row (𝒩.Carrier .set)} (hl : Natural 𝒩 left) (hr : Natural 𝒩 right)
    (he : Value 𝒩 left = Value 𝒩 right) : left.input = right.input := by
  obtain ⟨ht, hf⟩ := PureSourceCodingInversion.node_injective h𝒩 hl hr he
  cases left <;> cases right <;>
    simp_all [Row.tag, Row.fields, Row.input]

theorem below_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    (values : Fin n → 𝒩.Carrier .set) (hv : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {child parent : ObjectHorn.Expr n} (h : Below child parent) :
    mem 𝒩 (exprValue 𝒩 values child) (exprValue 𝒩 values parent) := by
  obtain ⟨index, body, rfl, rfl, hi⟩ := h
  exact expr_bound h𝒩 hv body hi

/-- 只反演一条原规则；每个子行仍读取原内部轨迹。 -/
theorem rule_ranked (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ ObjectFormulaSyntax.rules)
    (values : Fin rule.arity → 𝒩.Carrier .set) (hv : ∀ i, mem 𝒩 (values i) (w 𝒩)) :
    ∃ head : Row (𝒩.Carrier .set), Natural 𝒩 head ∧ Value 𝒩 head = exprValue 𝒩 values rule.head ∧
      ∀ premise ∈ rule.premises, ∃ child : Row (𝒩.Carrier .set), Natural 𝒩 child ∧
        Value 𝒩 child = exprValue 𝒩 values premise ∧ mem 𝒩 child.input head.input := by
  obtain ⟨head, he, hChildren⟩ := ranked rule hRule
  refine ⟨head.map (exprValue 𝒩 values), map_natural h𝒩 values hv head, ?_, ?_⟩
  · rw [value_map, he]
  · intro premise hp
    obtain ⟨child, hc, hd⟩ := hChildren premise hp
    refine ⟨child.map (exprValue 𝒩 values), map_natural h𝒩 values hv child, ?_, ?_⟩
    · rw [value_map, hc]
    · simpa only [Row.map_input] using below_value h𝒩 values hv hd

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceSyntaxRank
