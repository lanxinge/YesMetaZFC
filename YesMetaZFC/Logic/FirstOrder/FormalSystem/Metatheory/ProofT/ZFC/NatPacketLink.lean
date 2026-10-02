import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatDecode

/-!
# 支撑理论上版本一传输包的真实对象连接

输入使用原始 `NatPacket` 自然数，输出使用新对象树码；二者不被认作同一个数。
正负出口直接使用实际包解码器，无额外的规范包或预先成功解码假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.NatPacketLink
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def condition : FormulaTemplate.Binary := ObjectPacket.template

theorem condition_delta0 {bound free : SetContext} (packet treeCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition packet treeCode) := by
  rw [condition, ObjectPacket.template_apply]
  exact ObjectPacket.condition_delta0 _ _

theorem positive (packet : Nat) (input : Tree) (h : NatPacket.decode packet = some input) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(treeValue input) : Code)) := by
  rw [condition, ObjectPacket.template_apply]
  exact ObjectPacket.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity packet input h

theorem negative (packet : Nat) (input : Tree) (h : NatPacket.decode packet ≠ some input) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (numₘ(treeValue input) : Code)) := by
  rw [condition, ObjectPacket.template_apply]
  exact ObjectPacket.negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport packet input h

theorem positive_at_tree (packet : Nat) (input : Tree) (h : NatPacket.decode packet = some input) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (tree input)) := by
  rw [condition, ObjectPacket.template_apply]
  exact ObjectPacket.positive_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity packet input h

theorem negative_at_tree (packet : Nat) (input : Tree) (h : NatPacket.decode packet ≠ some input) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (tree input)) := by
  rw [condition, ObjectPacket.template_apply]
  exact ObjectPacket.negative_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport packet input h

/-- 正文包依次经过原始解析、六处重命名、核心模板和参数全称闭合。 -/
def schemaRun (kind : SchemaTemplate.Kind) (n packet : Nat) : Option Tree :=
  (NatPacket.decode packet).bind (SchemaClosure.run kind n)

theorem schemaRun_encode (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) :
    schemaRun kind n (NatPacket.encode input) = SchemaClosure.run kind n input := by
  simp only [schemaRun, NatPacket.decode_encode, Option.bind_some]

theorem schema_separation {n : Nat} (schema : Project.UnarySchema n) :
    schemaRun .separation n (NatPacket.encode (ProjectEncode.formula schema.body)) =
      some (ProjectEncode.formula (Axioms.Schema.separation schema).formula) := by
  rw [schemaRun_encode, SchemaClosure.run_separation]

theorem schema_collection {n : Nat} (schema : Project.BinarySchema n) :
    schemaRun .collection n (NatPacket.encode (ProjectEncode.formula schema.body)) =
      some (ProjectEncode.formula (Axioms.Schema.collection schema).formula) := by
  rw [schemaRun_encode, SchemaClosure.run_collection]

theorem schema_replacement {n : Nat} (schema : Project.BinarySchema n) :
    schemaRun .replacement n (NatPacket.encode (ProjectEncode.formula schema.body)) =
      some (ProjectEncode.formula (Axioms.Schema.replacement schema).formula) := by
  rw [schemaRun_encode, SchemaClosure.run_replacement]

/-- 当前自然数证明解码器的最外层解析直接得到同一个对象连接证明。 -/
theorem proof_packet {packet : Nat} {certificate : IntrinsicClosedProofCertificate}
    (h : intrinsic_zfc_nat_decode packet = some certificate) :
    ∃ input, NatPacket.decode packet = some input ∧
      Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (tree input)) := by
  obtain ⟨input, hPacket, _⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨input, hPacket, positive_at_tree packet input hPacket⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.NatPacketLink
