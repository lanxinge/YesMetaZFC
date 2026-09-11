import YesMetaZFC.Model.ZFC.Pure.PureSourceFormula
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomNumber

/-! # 实际公理检查公式的对应

模式中的重命名表、正文和闭句中间码都由原公式的自然数界控制。
有限公理表保留为抽象列表，不展开具体的大型 quotation。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceSchemas
open Nonlogical.BasicSetTheory PureSourceFormula PureSourceNumerals PureFinalArithmetic
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
attribute [local irreducible] ReducedAxioms.basis ReducedAxiomNumber.entries
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory}
variable {bound free : SetContext}

theorem pattern (shape : CodePattern.Pattern) {first second : SetTerm bound free}
    (hf : Natural h𝒩 first) (hs : Natural h𝒩 second) : Natural h𝒩 (shape.term first second) := by
  induction shape with
  | literal n => exact numeral n
  | first => exact hf
  | second => exact hs
  | successor body ih => exact successor ih
  | pairing left right ihl ihr => exact pairing ihl ihr

theorem treeTable (entries : List ObjectFiniteTable.Entry) {input output : SetTerm bound free}
    (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (ObjectFiniteTable.condition entries input output) := by
  apply anyOf
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  apply conj (equal hi (numeral entry.1)) (equal ?_ ho)
  intro env other _
  have evalClosed (M : Structure.{0,0,0,x} signature) (e : Env M bound free)
      (term : SetTerm [] []) : (FixedAxiomTable.row_term term).eval e = term.eval (Env.empty : Env M [] []) := by
    have heq : FixedAxiomTable.row_term (bound := bound) (free := free) term =
        term.substitute (.map VariableSubstitution.empty VariableSubstitution.empty) := by
      change term.embedClosed bound free = term.substituteMapped VariableSubstitution.empty VariableSubstitution.empty
      have ht := Term.embedClosed_substituteMapped (sourceBound := []) (sourceFree := [])
        (targetBound := bound) (targetFree := free) term VariableSubstitution.empty VariableSubstitution.empty
      rw [show term.embedClosed [] [] = term from FixedAxiomTable.row_term_empty term] at ht
      exact ht.symm
    rw [heq, Term.eval_substitute]
    congr 1
    exact Env.ext (fun entry => nomatch entry) (fun entry => nomatch entry)
  rw [evalClosed, evalClosed]
  have source := (IntrinsicQuotation.tree_evaluate intrinsic_zfc_certificate_core entry.2).semantically_entails 𝒩 h𝒩
  have target := (IntrinsicQuotation.tree_evaluate intrinsic_zfc_certificate_core entry.2).semantically_entails
    (canonical h𝒩) (PureZFCModels.models (PureZFCModels.reduct_models h𝒩))
  change (IntrinsicQuotation.tree entry.2).eval (Env.empty : Env 𝒩 [] []) = _ at source
  change (IntrinsicQuotation.tree entry.2).eval (Env.empty : Env (canonical h𝒩) [] []) = _ at target
  rw [source, target]
  exact ⟨PureSourceCoding.numeral_natural h𝒩 _, numeral_agrees h𝒩 _⟩

theorem treeTemplate {n : Nat} (program : List (Nat × ObjectTreeTemplate.Template n))
    {tag output : SetTerm bound free} {inputs : Fin n → SetTerm bound free}
    (ht : Natural h𝒩 tag) (hi : ∀ i, Natural h𝒩 (inputs i)) (ho : Natural h𝒩 output) :
    Stable h𝒩 (ObjectTreeTemplate.graph program tag inputs output) := by
  apply anyOf
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  exact conj (equal ht (numeral _)) (equal (expression entry.2.expr inputs hi) ho)

theorem joinMatrix (kind : SchemaTemplate.Kind) {env : Fin 7 → SetTerm bound free}
    {n input output : SetTerm bound free} (he : ∀ i, Natural h𝒩 (env i))
    (hn : Natural h𝒩 n) (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaJoin.matrix kind env n input output) := by
  apply allOf
  intro formula hf
  simp only [SchemaJoin.checks, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl)
  · apply horn _ (node 1 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨numeral _, hn, he _, fun _ h => nomatch h⟩
  · apply horn _ (node 5 ?_)
    simp only [List.forall_mem_cons]
    exact
      ⟨shift _ hn, he _, hi, he _, fun _ h => nomatch h⟩
  · exact treeTemplate _ (numeral _) (fun i => he _) (he _)
  · apply horn _ (node 0 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨numeral 9, hn, he _, ho, fun _ h => nomatch h⟩

theorem join {tag n input output : SetTerm bound free}
    (ht : Natural h𝒩 tag) (hn : Natural h𝒩 n) (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaJoin.condition tag n input output) := by
  apply anyOf
  intro formula hf
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hf
  apply conj (equal ht (numeral _))
  exact instantiate (SchemaJoin.boundedTemplate kind)
    (quantify 7 (fvar _) (joinMatrix kind (fun _ => bvar _) (fvar _) (fvar _) (fvar _))) _
    (natural_cons (successor (pairing (tableBound hn) ho))
      (natural_cons hn (natural_cons hi (natural_cons ho natural_empty))))

theorem kernelMatrix (kind : SchemaTemplate.Kind) {middle n input output : SetTerm bound free}
    (hm : Natural h𝒩 middle) (hn : Natural h𝒩 n) (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaKernelJoin.matrix kind middle n input output) := by
  apply conj (join (numeral _) hn hi hm) (horn _ (node 0 ?_))
  simp only [List.forall_mem_cons]
  exact ⟨hm, ho, fun _ h => nomatch h⟩

theorem kernel (kind : SchemaTemplate.Kind) {n input output : SetTerm bound free}
    (hn : Natural h𝒩 n) (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaKernelJoin.condition kind n input output) :=
  ternary (SchemaKernelJoin.template kind)
    (quantify 1 (successor (fvar _)) (kernelMatrix kind (bvar _) (fvar _) (fvar _) (fvar _))) hn hi ho

theorem packetMatrix (tag : Nat) (kind : SchemaTemplate.Kind) {env : Fin 3 → SetTerm bound free}
    {packet output : SetTerm bound free} (he : ∀ i, Natural h𝒩 (env i))
    (hp : Natural h𝒩 packet) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaPacket.matrix tag kind env packet output) := by
  apply allOf
  intro formula hf
  simp only [SchemaPacket.checks, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · apply horn _ (node 5 ?_)
    simp only [List.forall_mem_cons]
    exact ⟨hp, he 0, fun _ h => nomatch h⟩
  · exact equal (he 0) (pattern _ (he 1) (he 2))
  · exact kernel kind (he 1) (he 2) ho

theorem packet {input output : SetTerm bound free} (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (SchemaPacket.condition input output) := by
  apply anyOf
  intro formula hf
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hf
  exact ternary (SchemaPacket.boundedTemplate entry.1 entry.2)
    (quantify 3 (fvar _) (packetMatrix entry.1 entry.2 (fun _ => bvar _) (fvar _) (fvar _)))
    (successor (tableBound hi)) hi ho

theorem baseAxiom {input output : SetTerm bound free} (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (BaseAxiomPacket.condition input output) := by
  apply anyOf
  intro formula hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact treeTable _ hi ho
  · exact packet hi ho

theorem axiomCondition {input output : SetTerm bound free} (hi : Natural h𝒩 input) (ho : Natural h𝒩 output) :
    Stable h𝒩 (ReducedAxiomNumber.condition input output) := disj (baseAxiom hi ho) (treeTable _ hi ho)

theorem axiomTest : PureSourceHorn.UnaryAgreement h𝒩 ReducedAxiomNumber.localTest.condition :=
  binaryTest intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.contains_successor ReducedAxiomNumber.binaryTest (axiomCondition (fvar _) (fvar _))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceSchemas
