import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotationDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection

/-! # 带上下文和结论标注的完整证明树

每个节点保存 free 长度和当前 AST 结论码。局部检查只读取子节点头部，
递归检查另外验证子证明；这样 MP、量词、加强和代入的连接证据不会隐含在元层。
本层只定义实际编码与局部计算，不把局部布尔计算冒充对象表示。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
open Nonlogical.BasicSetTheory NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation.ObjectHorn
open _root_.YesMetaZFC.Automation.ObjectCodeProjection
set_option autoImplicit false

def encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) : Nat :=
  let result : Nat × List Nat := match proof with
    | .logical_axiom certificate => (0, [treeValue (LogicalAxiomEncode.encode certificate)])
    | .theory_axiom certificate => (1, [NatPacket.encode (codec.encode certificate)])
    | .modus_ponens premise implication => (2, [encode codec premise, encode codec implication])
    | .forall_generalization premise => (3, [encode codec premise])
    | .free_strengthening premise => (4, [encode codec premise])
    | @ProofCertificate.free_substitution _ _ source _ subst _ premise =>
      (5, [source.length,
        listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue),
        encode codec premise])
  nodeValue result.1 (free.length :: treeValue (SyntaxEncode.formula formula) :: result.2)

@[simp] theorem encode_free {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) : field (encode codec proof) 0 = free.length := by
  cases proof <;> simp [encode]

@[simp] theorem encode_formula {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) :
    field (encode codec proof) 1 = treeValue (SyntaxEncode.formula formula) := by
  cases proof <;> simp [encode]

theorem context_of_length (free : SetContext) : List.replicate free.length SetSort.set = free := by
  induction free with
  | nil => rfl
  | cons sort tail ih => cases sort; simp only [List.length_cons, List.replicate_succ, ih]

theorem encode_substitution_source {T : SetTheory} {axioms : AxiomPresentation T}
    {decoder : AxiomDecoder axioms} (codec : AxiomCodec decoder) {source target : SetContext}
    (subst : VariableSubstitution signature source [] target) {formula : SetOpenFormula source}
    (proof : ProofCertificate axioms source formula) :
    field (encode codec (.free_substitution subst proof)) 2 = source.length := by
  simp [encode]

def readHeader (free : SetContext) (code : Nat) : Option (SetOpenFormula free) := do
  if field code 0 = free.length then
    SyntaxDecode.formula [] free (← decodeTree (field code 1))
  else none

@[simp] theorem readHeader_encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) : readHeader free (encode codec proof) = some formula := by
  simp [readHeader]

def formulaEqual {free : SetContext} (left right : SetOpenFormula free) : Bool :=
  match SyntaxDecode.formulaEq left right with
  | isTrue _ => true
  | isFalse _ => false

@[simp] theorem formulaEqual_eq_true {free : SetContext} (left right : SetOpenFormula free) :
    formulaEqual left right = true ↔ left = right := by
  unfold formulaEqual
  cases SyntaxDecode.formulaEq left right <;> simp_all

/-- 所有六种核规则的非递归局部检查；子证明只读头部。 -/
def localRun {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) : Option Bool := do
  let free := List.replicate (field code 0) SetSort.set
  let conclusion ← readHeader free code
  match tag code with
  | 0 =>
    let ⟨formula, _⟩ ← LogicalAxiomDecode.decode free (← decodeTree (field code 2))
    return formulaEqual formula conclusion
  | 1 =>
    let certificate ← decoder (← NatPacket.decode (field code 2))
    return formulaEqual (Formula.fromSentence (axioms.sentence certificate)) conclusion
  | 2 =>
    let premise ← readHeader free (field code 2)
    let implication ← readHeader free (field code 3)
    match implication with
    | .imp left right => return formulaEqual premise left && formulaEqual right conclusion
    | _ => none
  | 3 =>
    let premise ← readHeader (.set :: free) (field code 2)
    return formulaEqual (premise.forallFreeTop .set) conclusion
  | 4 =>
    let premise ← readHeader (.set :: free) (field code 2)
    return formulaEqual premise (conclusion.weakenFree SetSort.set)
  | 5 =>
    let source := List.replicate (field code 2) SetSort.set
    let trees ← decodeForest (field code 3)
    let args ← SyntaxDecode.argumentsList [] free source trees
    let premise ← readHeader source (field code 4)
    return formulaEqual (premise.substituteFree (SyntaxDecode.substitution args)) conclusion
  | _ => none

def localCheck {T : SetTheory} {axioms : AxiomPresentation T} (decoder : AxiomDecoder axioms)
    (code : Nat) : Bool := (localRun decoder code).getD false

/-- 编码始终保留原推导的完整局部连接。 -/
theorem localCheck_encode {T : SetTheory} {axioms : AxiomPresentation T} {decoder : AxiomDecoder axioms}
    (codec : AxiomCodec decoder) {free : SetContext} {formula : SetOpenFormula free}
    (proof : ProofCertificate axioms free formula) : localCheck decoder (encode codec proof) = true := by
  unfold localCheck localRun
  rw [encode_free, context_of_length]
  dsimp only
  rw [readHeader_encode]
  cases proof with
  | logical_axiom certificate =>
    simp [encode, LogicalAxiomEncode.roundtrip, formulaEqual, NatEncode.formulaEq_self]
  | theory_axiom certificate =>
    simp [encode, codec.roundtrip, formulaEqual, NatEncode.formulaEq_self]
  | modus_ponens premise implication =>
    simp [encode, readHeader_encode, formulaEqual, NatEncode.formulaEq_self]
  | forall_generalization premise =>
    cases ‹SetSort›
    simp [encode, readHeader_encode, formulaEqual, NatEncode.formulaEq_self]
  | free_strengthening premise =>
    cases ‹SetSort›
    simp [encode, readHeader_encode, formulaEqual, NatEncode.formulaEq_self]
  | free_substitution subst premise =>
    simp only [encode_substitution_source]
    simp [encode, formulaEqual]
    rw [field_node, get_succ, get_succ, get_zero, context_of_length,
      SyntaxEncode.argumentsList_roundtrip]
    simp only [readHeader_encode, Option.bind_some, Option.getD_some]
    rw [SyntaxEncode.substitution_roundtrip, NatEncode.formulaEq_self]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ProofTreeCode
