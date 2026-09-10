import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQuantifiers
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSchemaGraphs
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPacketReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomNumber

/-! # 原 schema 查询完整管线的内部正反射

表生成、正文重命名、闭句、quotation 转换与传输包解码按实际有界公式组合。
覆盖分离、收集和替换的所有传输包分支，以及原有限公理表。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalSchemaReflection
open Nonlogical.BasicSetTheory InternalPositiveFormula InternalNumeralReflection
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedAxioms.basis ReducedAxiomNumber.entries
attribute [local irreducible] Positive Evaluates
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
variable {bound free : SetContext}
include h𝒩

theorem pattern (shape : CodePattern.Pattern) {first second : SetTerm bound free}
    (hf : Evaluates 𝒩 first) (hs : Evaluates 𝒩 second) : Evaluates 𝒩 (shape.term first second) := by
  induction shape with
  | literal n => exact numeral h𝒩 n
  | first => exact hf
  | second => exact hs
  | successor body ih => exact successor h𝒩 ih
  | pairing left right ihl ihr => exact pairing h𝒩 ihl ihr

theorem treeTable (entries : List ObjectFiniteTable.Entry) {input output : SetTerm bound free}
    (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (ObjectFiniteTable.condition entries input output) := by
  apply anyOf h𝒩
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  apply conj h𝒩 (equal h𝒩 hi (numeral h𝒩 entry.1)) (equal h𝒩 ?_ ho)
  exact tree h𝒩 entry.2

theorem treeTemplate {n : Nat} (program : List (Nat × ObjectTreeTemplate.Template n))
    {tag output : SetTerm bound free} {inputs : Fin n → SetTerm bound free}
    (ht : Evaluates 𝒩 tag) (hi : ∀ i, Evaluates 𝒩 (inputs i)) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (ObjectTreeTemplate.graph program tag inputs output) := by
  apply anyOf h𝒩
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  exact conj h𝒩 (equal h𝒩 ht (numeral h𝒩 _)) (equal h𝒩 (expression h𝒩 entry.2.expr inputs hi) ho)

theorem joinMatrix (kind : SchemaTemplate.Kind) {env : Fin 7 → SetTerm bound free}
    {n input output : SetTerm bound free} (he : ∀ i, Evaluates 𝒩 (env i))
    (hn : Evaluates 𝒩 n) (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaJoin.matrix kind env n input output) := by
  apply allOf h𝒩
  intro formula hf
  simp only [SchemaJoin.checks, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl)
  · apply horn h𝒩 _ (fun _ => schema_table_positive h𝒩) (node h𝒩 1 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨numeral h𝒩 _, hn, he _, fun _ h => nomatch h⟩
  · apply horn h𝒩 _ (fun _ => schema_rename_positive h𝒩) (node h𝒩 5 ?_)
    simp only [List.forall_mem_cons]
    exact
      ⟨shift h𝒩 _ hn, he _, hi, he _, fun _ h => nomatch h⟩
  · exact treeTemplate h𝒩 _ (numeral h𝒩 _) (fun i => he _) (he _)
  · apply horn h𝒩 _ (fun _ => iteration_positive h𝒩) (node h𝒩 0 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨numeral h𝒩 9, hn, he _, ho, fun _ h => nomatch h⟩

theorem join {tag n input output : SetTerm bound free}
    (ht : Evaluates 𝒩 tag) (hn : Evaluates 𝒩 n) (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaJoin.condition tag n input output) := by
  apply anyOf h𝒩
  intro formula hf
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hf
  apply conj h𝒩 (equal h𝒩 ht (numeral h𝒩 _))
  exact instantiate (SchemaJoin.boundedTemplate kind)
    (quantify h𝒩 7 (fvar _) (joinMatrix h𝒩 kind (fun _ => bvar _) (fvar _) (fvar _) (fvar _))) _
    (evaluates_cons (successor h𝒩 (pairing h𝒩 (tableBound h𝒩 hn) ho))
      (evaluates_cons hn (evaluates_cons hi (evaluates_cons ho evaluates_empty))))

theorem kernelMatrix (kind : SchemaTemplate.Kind) {middle n input output : SetTerm bound free}
    (hm : Evaluates 𝒩 middle) (hn : Evaluates 𝒩 n) (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaKernelJoin.matrix kind middle n input output) := by
  apply conj h𝒩 (join h𝒩 (numeral h𝒩 _) hn hi hm) (horn h𝒩 _ (fun _ => project_quotation_positive h𝒩) (node h𝒩 0 ?_))
  simp only [List.forall_mem_cons]
  exact ⟨hm, ho, fun _ h => nomatch h⟩

theorem kernel (kind : SchemaTemplate.Kind) {n input output : SetTerm bound free}
    (hn : Evaluates 𝒩 n) (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaKernelJoin.condition kind n input output) :=
  ternary (SchemaKernelJoin.template kind)
    (quantify h𝒩 1 (successor h𝒩 (fvar _)) (kernelMatrix h𝒩 kind (bvar _) (fvar _) (fvar _) (fvar _))) hn hi ho

theorem packetMatrix (tag : Nat) (kind : SchemaTemplate.Kind) {env : Fin 3 → SetTerm bound free}
    {packet output : SetTerm bound free} (he : ∀ i, Evaluates 𝒩 (env i))
    (hp : Evaluates 𝒩 packet) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaPacket.matrix tag kind env packet output) := by
  apply allOf h𝒩
  intro formula hf
  simp only [SchemaPacket.checks, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · apply horn h𝒩 _ (fun _ => packet_positive h𝒩) (node h𝒩 5 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨hp, he 0, fun _ h => nomatch h⟩
  · exact equal h𝒩 (he 0) (pattern h𝒩 _ (he 1) (he 2))
  · exact kernel h𝒩 kind (he 1) (he 2) ho

theorem packet {input output : SetTerm bound free} (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (SchemaPacket.condition input output) := by
  apply anyOf h𝒩
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  exact ternary (SchemaPacket.boundedTemplate entry.1 entry.2)
    (quantify h𝒩 3 (fvar _) (packetMatrix h𝒩 entry.1 entry.2 (fun _ => bvar _) (fvar _) (fvar _)))
    (successor h𝒩 (tableBound h𝒩 hi)) hi ho

theorem baseAxiom {input output : SetTerm bound free} (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (BaseAxiomPacket.condition input output) := by
  apply anyOf h𝒩
  intro formula hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact treeTable h𝒩 _ hi ho
  · exact packet h𝒩 hi ho

theorem axiomCondition {input output : SetTerm bound free} (hi : Evaluates 𝒩 input) (ho : Evaluates 𝒩 output) :
    Positive 𝒩 (ReducedAxiomNumber.condition input output) := disj h𝒩 (baseAxiom h𝒩 hi ho) (treeTable h𝒩 _ hi ho)


end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalSchemaReflection
