import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransform
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxCanonical

/-! # 数值语法变换与类型安全内核的交换

替换项在证明规则处没有束缚变量。跨过量词时必须提升变量像；
下面的分层替换保持这一内核约定，并显式证明其数值编码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
open Nonlogical.BasicSetTheory NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation.ObjectHorn
set_option autoImplicit false

mutual
theorem term_substitute {sb sf tb tf : SetContext} (mode depth parameter : Nat) (hMode : mode < 4)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), boundValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (bs entry))))
    (hf : ∀ {sort} (entry : Variable sf sort), freeValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (fs entry)))) :
    {sort : SetSort} → (input : Term signature sb sf sort) →
    term mode depth parameter (SyntaxEncode.term input) = some (treeValue (SyntaxEncode.term (input.substituteMapped bs fs)))
  | _, .bvar entry => hb entry
  | _, .fvar entry => hf entry
  | _, .app symbol args => by
    simp only [SyntaxEncode.term_app, leaf, term, Term.substituteMapped]
    rw [arguments_substitute mode depth parameter hMode bs fs hb hf args]
    simp [nodeValue, listValue]

theorem arguments_substitute {sb sf tb tf : SetContext} (mode depth parameter : Nat) (hMode : mode < 4)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), boundValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (bs entry))))
    (hf : ∀ {sort} (entry : Variable sf sort), freeValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (fs entry)))) :
    {sorts : SetContext} → (input : Arguments signature sb sf sorts) →
    arguments mode depth parameter (SyntaxEncode.argumentsList input) =
      some (listValue ((SyntaxEncode.argumentsList (input.substituteMapped bs fs)).map treeValue))
  | _, .nil => by simp [arguments, SyntaxEncode.argumentsList, Arguments.substituteMapped, hMode]
  | _, .cons first rest => by
    simp only [SyntaxEncode.argumentsList, arguments, Arguments.substituteMapped]
    rw [term_substitute mode depth parameter hMode bs fs hb hf first,
      arguments_substitute mode depth parameter hMode bs fs hb hf rest]
    rfl
end

mutual
private theorem shift_closed {free : SetContext} : {sort : SetSort} → (input : Term signature [] free sort) →
    SyntaxSubstitution.shift (SyntaxEncode.term input) = SyntaxEncode.term input
  | _, .bvar entry => nomatch entry
  | _, .fvar _ => rfl
  | _, .app symbol args => by
    simp only [SyntaxEncode.term_app, SyntaxSubstitution.shift, SyntaxSubstitution.term]
    rw [shifts_closed args]
private theorem shifts_closed {free : SetContext} : {sorts : SetContext} → (input : Arguments signature [] free sorts) →
    SyntaxSubstitution.terms (fun i => SyntaxSubstitution.bvar (i + 1)) SyntaxSubstitution.fvar
      (SyntaxEncode.argumentsList input) = SyntaxEncode.argumentsList input
  | _, .nil => rfl
  | _, .cons first rest => by
    simp only [SyntaxEncode.argumentsList, SyntaxSubstitution.terms]
    rw [show SyntaxSubstitution.term (fun i => SyntaxSubstitution.bvar (i + 1)) SyntaxSubstitution.fvar
      (SyntaxEncode.term first) = SyntaxEncode.term first from shift_closed first, shifts_closed rest]
end

@[simp] theorem encode_embedBoundClosed {free : SetContext} {sort : SetSort}
    (bound : SetContext) (input : Term signature [] free sort) :
    SyntaxEncode.term (input.embedBoundClosed bound) = SyntaxEncode.term input := by
  induction bound with
  | nil => rfl
  | cons sort rest ih =>
    cases sort
    change SyntaxEncode.term ((input.embedBoundClosed rest).weakenBound SetSort.set) = SyntaxEncode.term input
    rw [← SyntaxSubstitution.shift_encode, ih, shift_closed]

/-- 同一操作穿过若干 binder 后的上下文。 -/
abbrev extend (base : SetContext) : Nat → SetContext
  | 0 => base
  | n + 1 => .set :: extend base n

def boundLift {sb tb tf : SetContext} (bs : VariableSubstitution signature sb tb tf) :
    (depth : Nat) → VariableSubstitution signature (extend sb depth) (extend tb depth) tf
  | 0 => bs
  | depth + 1 => by exact VariableSubstitution.liftBound (σ := signature) SetSort.set (boundLift bs depth)

def freeLift {sf tb tf : SetContext} (fs : VariableSubstitution signature sf tb tf) :
    (depth : Nat) → VariableSubstitution signature sf (extend tb depth) tf
  | 0 => fs
  | depth + 1 => VariableSubstitution.weakenBound SetSort.set (freeLift fs depth)

/-- 恒等变量像跨过任意多个量词仍保持恒等。 -/
theorem boundLift_id {bound free : SetContext} (depth : Nat) {sort : SetSort}
    (entry : Variable (extend bound depth) sort) :
    boundLift (VariableSubstitution.boundId : VariableSubstitution signature bound bound free) depth entry = .bvar entry := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases entry with
    | here => rfl
    | there entry =>
      change (boundLift (VariableSubstitution.boundId : VariableSubstitution signature bound bound free)
        depth entry).weakenBound SetSort.set = _
      rw [ih]
      rfl

theorem freeLift_id {bound free : SetContext} (depth : Nat) {sort : SetSort}
    (entry : Variable free sort) :
    freeLift (VariableSubstitution.freeId : VariableSubstitution signature free bound free) depth entry = .fvar entry := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (freeLift (VariableSubstitution.freeId : VariableSubstitution signature free bound free)
      depth entry).weakenBound SetSort.set = _
    rw [ih]
    rfl

/-- 对全部深度给出变量编码交换后，公式交换由完整 AST 的递归直接导出。 -/
theorem formula_substitute {sb sf tb tf : SetContext} (mode parameter : Nat) (hMode : mode < 4)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ depth {sort} (entry : Variable (extend sb depth) sort),
      boundValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (boundLift bs depth entry))))
    (hf : ∀ depth {sort} (entry : Variable sf sort),
      freeValue mode depth parameter entry.index = some (treeValue (SyntaxEncode.term (freeLift fs depth entry))))
    (depth : Nat) (input : SetFormula (extend sb depth) sf) :
    formula mode depth parameter (SyntaxEncode.formula input) =
      some (treeValue (SyntaxEncode.formula (input.substituteMapped (boundLift bs depth) (freeLift fs depth)))) := by
  cases hInput : input with
  | falsum => simp [SyntaxEncode.formula, leaf, formula, Formula.substituteMapped, hMode]
  | truth => simp [SyntaxEncode.formula, leaf, formula, Formula.substituteMapped, hMode]
  | rel symbol args =>
    simp only [SyntaxEncode.formula, leaf, formula, Formula.substituteMapped]
    rw [arguments_substitute mode depth parameter hMode _ _ (hb depth) (hf depth) args]
    simp [nodeValue, listValue]
  | equal left right =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    rw [term_substitute mode depth parameter hMode _ _ (hb depth) (hf depth) left,
      term_substitute mode depth parameter hMode _ _ (hb depth) (hf depth) right]
    simp
  | neg body =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    rw [formula_substitute mode parameter hMode bs fs hb hf depth body]
    simp
  | conj left right | disj left right | imp left right | iff left right =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    rw [formula_substitute mode parameter hMode bs fs hb hf depth left,
      formula_substitute mode parameter hMode bs fs hb hf depth right]
    simp
  | forallE sort body | existsE sort body =>
    cases sort
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    have hBody := formula_substitute mode parameter hMode bs fs hb hf (depth + 1) body
    dsimp only [extend, boundLift, freeLift] at hBody
    rw [hBody]
    simp
termination_by sizeOf (SyntaxEncode.formula input)
decreasing_by all_goals simp_all [SyntaxEncode.formula]; all_goals omega

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
