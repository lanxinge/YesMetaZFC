import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransformKernel

/-! # 四种局部内核操作的具体数值实例 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
open Nonlogical.BasicSetTheory NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation.ObjectHorn
set_option autoImplicit false

@[simp] theorem extend_length (base : SetContext) (depth : Nat) :
    (extend base depth).length = depth + base.length := by
  induction depth <;> simp_all [extend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem boundLift_empty {tb tf : SetContext} (bs : VariableSubstitution signature [] tb tf)
    (depth : Nat) {sort : SetSort} (entry : Variable (extend [] depth) sort) :
    SyntaxEncode.term (boundLift bs depth entry) = SyntaxSubstitution.bvar entry.index := by
  induction depth with
  | zero => cases entry
  | succ depth ih =>
    cases entry with
    | here => rfl
    | there entry =>
      change SyntaxEncode.term ((boundLift bs depth entry).weakenBound SetSort.set) =
        SyntaxSubstitution.bvar (entry.index + 1)
      rw [← SyntaxSubstitution.shift_encode, ih]
      rfl

private theorem freeLift_closed {sf tf : SetContext} (fs : VariableSubstitution signature sf [] tf)
    (depth : Nat) {sort : SetSort} (entry : Variable sf sort) :
    SyntaxEncode.term (freeLift fs depth entry) = SyntaxEncode.term (fs entry) := by
  have h : freeLift fs depth entry = (fs entry).embedBoundClosed (extend [] depth) := by
    induction depth with
    | zero => rfl
    | succ depth ih =>
      change (freeLift fs depth entry).weakenBound SetSort.set =
        ((fs entry).embedBoundClosed (extend [] depth)).weakenBound SetSort.set
      rw [ih]
  rw [h, encode_embedBoundClosed]

theorem freeLift_abstract {free : SetContext} (depth : Nat)
    {sort : SetSort} (entry : Variable (SetSort.set :: free) sort) :
    SyntaxEncode.term (freeLift (VariableSubstitution.abstractFreeTop (bound := [])) depth entry) =
      match entry with
      | .here => SyntaxSubstitution.bvar depth
      | .there previous => SyntaxSubstitution.fvar previous.index := by
  induction depth with
  | zero => cases entry <;> rfl
  | succ depth ih =>
    change SyntaxEncode.term ((freeLift (VariableSubstitution.abstractFreeTop (σ := signature) (bound := [])) depth entry).weakenBound SetSort.set) = _
    rw [← SyntaxSubstitution.shift_encode, ih]
    cases entry <;> rfl

private theorem boundLift_point {free : SetContext} (point : SetOpenTerm free) (depth : Nat)
    {sort : SetSort} (entry : Variable (extend [SetSort.set] depth) sort) :
    SyntaxEncode.term (boundLift (VariableSubstitution.instantiateTop point) depth entry) =
      if entry.index < depth then SyntaxSubstitution.bvar entry.index else SyntaxEncode.term point := by
  induction depth with
  | zero =>
    cases entry with
    | here => rfl
    | there entry => cases entry
  | succ depth ih =>
    cases entry with
    | here => simp [boundLift, VariableSubstitution.liftBound, Variable.index, SyntaxSubstitution.bvar, leaf]
    | there entry =>
      change SyntaxEncode.term ((boundLift (VariableSubstitution.instantiateTop point) depth entry).weakenBound SetSort.set) =
        if entry.index + 1 < depth + 1 then SyntaxSubstitution.bvar (entry.index + 1) else SyntaxEncode.term point
      rw [← SyntaxSubstitution.shift_encode, ih]
      by_cases h : entry.index < depth
      · simp [h, SyntaxSubstitution.shift, SyntaxSubstitution.bvar, SyntaxSubstitution.term, leaf]
      · simp only [h, Nat.add_lt_add_iff_right, if_false]
        exact (SyntaxSubstitution.shift_encode point).trans (encode_embedBoundClosed [SetSort.set] point)

/-- 同时代入表按当前内核的变量编号取出正确替换项。 -/
theorem lookup_substitution {free : SetContext} (source : SetContext)
    (subst : VariableSubstitution signature source [] free)
    {sort : SetSort} (entry : Variable source sort) :
    lookup (listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue)) entry.index =
      some (treeValue (SyntaxEncode.term (subst entry))) := by
  induction source with
  | nil => cases entry
  | cons sort source ih =>
    cases sort
    cases entry with
    | here => simp [SyntaxEncode.substitutionArguments, SyntaxEncode.argumentsList, Variable.index, listValue]
    | there entry =>
      simp only [SyntaxEncode.substitutionArguments, SyntaxEncode.argumentsList, List.map_cons, listValue, Variable.index, lookup_cons_succ]
      exact ih (fun entry => subst (.there entry)) entry

/-- 加强自由上下文的编码与内核重命名一致。 -/
theorem weakenFree_encode {free : SetContext} (input : SetOpenFormula free) :
    formula 0 0 0 (SyntaxEncode.formula input) =
      some (treeValue (SyntaxEncode.formula (input.weakenFree SetSort.set))) := by
  have h := formula_substitute 0 0 (by decide)
    (VariableSubstitution.boundId : VariableSubstitution signature [] [] (SetSort.set :: free))
    (fun entry => Term.fvar (.there entry))
    (by intro depth sort entry; rw [boundLift_empty]; rfl)
    (by intro depth sort entry; rw [freeLift_closed]; rfl) 0 input
  change formula 0 0 0 (SyntaxEncode.formula input) = some (treeValue (SyntaxEncode.formula
    (input.substituteMapped VariableSubstitution.boundId (VariableSubstitution.of_renaming (VariableRenaming.weaken SetSort.set))))) at h
  rw [Formula.substituteMapped_of_renaming] at h
  exact h

/-- 抽象最新自由变量，完整覆盖量词下的深度变化。 -/
theorem abstractTop_encode {free : SetContext} (input : SetOpenFormula (SetSort.set :: free)) :
    formula 1 0 0 (SyntaxEncode.formula input) =
      some (treeValue (SyntaxEncode.formula input.abstractFreeTop)) := by
  have h := formula_substitute 1 0 (by decide)
    (fun {sort} (entry : Variable [] sort) => VariableSubstitution.abstractBound (σ := signature) (free := free) SetSort.set entry)
    (fun {sort} (entry : Variable (SetSort.set :: free) sort) => VariableSubstitution.abstractFreeTop (σ := signature) (bound := []) entry)
    (by
      intro depth sort entry
      rw [boundLift_empty]
      have hLt : entry.index < depth := by
        have h := SyntaxDecode.variable_lt entry
        have hLength : (extend [] depth).length = depth := by rw [extend_length]; rfl
        rw [hLength] at h
        exact h
      simp [boundValue, hLt])
    (by
      intro depth sort entry
      rw [freeLift_abstract]
      cases entry <;> rfl) 0 input
  exact h

/-- 实例化的替换项是 bound-closed 项，故跨过量词不会改变其编码。 -/
theorem instantiateTop_encode {free : SetContext} (input : SetFormula [SetSort.set] free) (point : SetOpenTerm free) :
    formula 2 0 (treeValue (SyntaxEncode.term point)) (SyntaxEncode.formula input) =
      some (treeValue (SyntaxEncode.formula (input.instantiateTop point))) := by
  have h := formula_substitute 2 (treeValue (SyntaxEncode.term point)) (by decide)
    (VariableSubstitution.instantiateTop point) VariableSubstitution.freeId
    (by
      intro depth sort entry
      rw [boundLift_point]
      have hLt : entry.index < depth + 1 := by
        have h := SyntaxDecode.variable_lt entry
        have hLength : (extend [SetSort.set] depth).length = depth + 1 := extend_length _ _
        rw [hLength] at h
        exact h
      by_cases h : entry.index < depth
      · simp [boundValue, h]
      · have hEq : entry.index = depth := by omega
        simp [boundValue, hEq])
    (by intro depth sort entry; rw [freeLift_closed]; rfl) 0 input
  exact h

/-- 有限表同时自由代入，表顺序与实际内核一致。 -/
theorem substituteFree_encode {source free : SetContext} (input : SetOpenFormula source)
    (subst : VariableSubstitution signature source [] free) :
    formula 3 0 (listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue))
      (SyntaxEncode.formula input) = some (treeValue (SyntaxEncode.formula (input.substituteFree subst))) := by
  have h := formula_substitute 3
    (listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue)) (by decide)
    VariableSubstitution.boundId subst
    (by intro depth sort entry; rw [boundLift_empty]; rfl)
    (by intro depth sort entry; rw [freeLift_closed]; exact lookup_substitution source subst entry) 0 input
  exact h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
