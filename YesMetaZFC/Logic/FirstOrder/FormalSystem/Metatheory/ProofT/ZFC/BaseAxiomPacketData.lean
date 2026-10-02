import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomCanonical
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteTable

/-! # 完整 ZFC 基础公理包的独立规格

规格直接调用原证书解码器，输出当前类型安全内核 AST；固定表和两类模式
只在对象图层分支。本层不包含外层支撑公理和，也不改变原有标签约定。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation
set_option autoImplicit false

def conclusion (certificate : ZFCAxiomCertificate) : Tree :=
  SyntaxEncode.formula (project_sentence certificate.sentence)

def decode (packet : Nat) : Option ZFCAxiomCertificate :=
  (NatPacket.decode packet).bind zfc_base_axiom_decode

def run (packet : Nat) : Option Tree := (decode packet).map conclusion

def fixedCertificates : List ZFCAxiomCertificate :=
  [.extensionality, .emptySet, .pairing, .union, .powerSet, .infinity, .foundation, .choice]

def fixedEntry (certificate : ZFCAxiomCertificate) : ObjectFiniteTable.Entry :=
  (NatPacket.encode (zfc_base_axiom_encode certificate), conclusion certificate)

def fixedEntries : List ObjectFiniteTable.Entry := fixedCertificates.map fixedEntry

@[simp] theorem decode_encode (certificate : ZFCAxiomCertificate) :
    decode (NatPacket.encode (zfc_base_axiom_encode certificate)) = some certificate := by
  simp [decode]

@[simp] theorem run_encode (certificate : ZFCAxiomCertificate) :
    run (NatPacket.encode (zfc_base_axiom_encode certificate)) = some (conclusion certificate) := by
  simp [run]

/-- 成功包与规范编码相等；不需要额外的标准性或规范性假设。 -/
theorem decode_eq_some_iff (packet : Nat) (certificate : ZFCAxiomCertificate) :
    decode packet = some certificate ↔ NatPacket.encode (zfc_base_axiom_encode certificate) = packet := by
  constructor
  · intro h
    obtain ⟨input, hPacket, hCertificate⟩ := Option.bind_eq_some_iff.mp h
    rw [zfc_base_axiom_encode_of_decode hCertificate]
    exact NatPacket.encode_of_decode hPacket
  · intro h
    rw [← h]
    exact decode_encode certificate

theorem run_eq_some_iff (packet : Nat) (output : Tree) :
    run packet = some output ↔ ∃ certificate,
      NatPacket.encode (zfc_base_axiom_encode certificate) = packet ∧ conclusion certificate = output := by
  simp only [run, Option.map_eq_some_iff, decode_eq_some_iff]

theorem schema_actual (packet : Nat) :
    SchemaPacket.actual packet = (decode packet).bind SchemaPacket.schemaConclusion := by
  simp [SchemaPacket.actual, decode, Option.bind_assoc]

/-- 旧模式图的成功严格包含在完整基础公理规格的成功中。 -/
theorem schema_success (packet : Nat) (output : Tree) (h : SchemaPacket.run packet = some output) :
    run packet = some output := by
  rw [SchemaPacket.run_eq_actual, schema_actual] at h
  obtain ⟨certificate, hCertificate, hOutput⟩ := Option.bind_eq_some_iff.mp h
  have hConclusion : conclusion certificate = output := by
    cases certificate <;> simp [SchemaPacket.schemaConclusion] at hOutput
    all_goals exact hOutput
  simp [run, hCertificate, hConclusion]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
