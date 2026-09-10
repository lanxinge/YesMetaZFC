import YesMetaZFC.Automation.ObjectCodeInstantiation
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransformKernel

/-! # 参数化项码与类型化代入的交换

一个项／参数列遍历统一处理弱化及复合项的码等式，不展开具体数值编码。
-/
namespace YesMetaZFC.Automation.ObjectCodeInstantiation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
set_option autoImplicit false
universe u
variable {α : Type u}

mutual
theorem term_mapped (node : Nat → List α → α) (source target : Nat → α)
    {sb sf tb tf : SetContext} (b : VariableSubstitution signature sb tb tf) (f : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), term node target (b entry) = node 0 [node entry.index []])
    (hf : ∀ {sort} (entry : Variable sf sort), term node target (f entry) = source entry.index)
    {sort : SetSort} : (input : Term signature sb sf sort) →
      term node target (input.substituteMapped b f) = term node source input
  | .bvar entry => hb entry
  | .fvar entry => hf entry
  | .app symbol args => by
    change node 2 (node symbol.ctorIdx [] :: arguments node target (args.substituteMapped b f)) = _
    rw [arguments_mapped node source target b f hb hf args]; rfl

theorem arguments_mapped (node : Nat → List α → α) (source target : Nat → α)
    {sb sf tb tf sorts : SetContext} (b : VariableSubstitution signature sb tb tf) (f : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), term node target (b entry) = node 0 [node entry.index []])
    (hf : ∀ {sort} (entry : Variable sf sort), term node target (f entry) = source entry.index) :
    (input : Arguments signature sb sf sorts) →
      arguments node target (input.substituteMapped b f) = arguments node source input
  | .nil => rfl
  | .cons head tail => by
    change term node target (head.substituteMapped b f) :: arguments node target (tail.substituteMapped b f) = _
    rw [term_mapped node source target b f hb hf head, arguments_mapped node source target b f hb hf tail]; rfl
end

theorem term_embedBoundClosed (node : Nat → List α → α) (values : Nat → α)
    {free : SetContext} (bound : SetContext) (input : SetOpenTerm free) :
    term node values (input.embedBoundClosed bound) = term node values input := by
  rw [← ProofT.SyntaxSubstitution.closed_term_substitute_id VariableSubstitution.empty input]
  exact term_mapped node values values VariableSubstitution.empty VariableSubstitution.freeId
    (by intro sort entry; cases entry) (fun _ => rfl) input

/-- 变量像的合同覆盖全部 binder 深度，公式仅作一次结构遍历。 -/
theorem formula_mapped_of_depth (node : Nat → List α → α) (source target : Nat → α)
    {sb sf tb tf : SetContext} (b : VariableSubstitution signature sb tb tf) (f : VariableSubstitution signature sf tb tf)
    (hb : ∀ depth {sort} (entry : Variable (ProofT.SyntaxTransform.extend sb depth) sort),
      term node target (ProofT.SyntaxTransform.boundLift b depth entry) = node 0 [node entry.index []])
    (hf : ∀ depth {sort} (entry : Variable sf sort),
      term node target (ProofT.SyntaxTransform.freeLift f depth entry) = source entry.index)
    (depth : Nat) (input : SetFormula (ProofT.SyntaxTransform.extend sb depth) sf) :
    formula node target (input.substituteMapped (ProofT.SyntaxTransform.boundLift b depth)
      (ProofT.SyntaxTransform.freeLift f depth)) = formula node source input := by
  cases hInput : input with
  | falsum => rfl
  | truth => rfl
  | rel symbol args =>
    simp only [Formula.substituteMapped, formula, arguments_mapped node source target _ _ (hb depth) (hf depth)]
  | equal left right =>
    simp only [Formula.substituteMapped, formula, term_mapped node source target _ _ (hb depth) (hf depth)]
  | neg body =>
    simp only [Formula.substituteMapped, formula, formula_mapped_of_depth node source target b f hb hf depth body]
  | conj left right | disj left right | imp left right | iff left right =>
    simp only [Formula.substituteMapped, formula,
      formula_mapped_of_depth node source target b f hb hf depth left,
      formula_mapped_of_depth node source target b f hb hf depth right]
  | forallE sort body | existsE sort body =>
    cases sort
    exact congrArg (fun code => node _ [code]) (formula_mapped_of_depth node source target b f hb hf (depth + 1) body)
termination_by sizeOf (ProofT.SyntaxEncode.formula input)
decreasing_by all_goals simp_all [ProofT.SyntaxEncode.formula]; all_goals omega

/-- 无自由 bound 槽的替换项穿过量词后，参数化码保持不变。 -/
theorem formula_substituteFree (node : Nat → List α → α) (source target : Nat → α)
    {sf tf : SetContext} (f : VariableSubstitution signature sf [] tf)
    (hf : ∀ {sort} (entry : Variable sf sort), term node target (f entry) = source entry.index)
    (input : SetOpenFormula sf) :
    formula node target (input.substituteFree f) = formula node source input := by
  apply formula_mapped_of_depth node source target VariableSubstitution.boundId f
    (fun depth _ entry => by rw [ProofT.SyntaxTransform.boundLift_id]; rfl) ?_ 0 input
  intro depth sort entry
  cases sort
  have he : ProofT.SyntaxTransform.freeLift f depth entry =
      (f entry).embedBoundClosed (ProofT.SyntaxTransform.extend [] depth) := by
    induction depth with
    | zero => rfl
    | succ depth ih =>
      change (ProofT.SyntaxTransform.freeLift f depth entry).weakenBound SetSort.set =
        ((f entry).embedBoundClosed (ProofT.SyntaxTransform.extend [] depth)).weakenBound SetSort.set
      rw [ih]
  rw [he, term_embedBoundClosed]
  exact hf entry

theorem binary_template (node : Nat → List α → α) (values : Nat → α)
    (template : ProofT.FormulaTemplate.Binary) {free : SetContext} (left right : SetOpenTerm free) :
    formula node values (template left right) =
      formula node (prepend (term node values left) (fun _ => term node values right)) template.body := by
  have he : (fun {sort} (entry : Variable [] sort) => (VariableSubstitution.empty entry : Term signature [] free sort)) =
      (fun {sort} entry => VariableSubstitution.boundId entry) := by funext sort entry; cases entry
  change formula node values (template.body.substituteMapped VariableSubstitution.empty _) = _
  let substitution : VariableSubstitution signature [.set,.set] [] free :=
    VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty)
  apply Eq.trans (congrArg (fun b : {sort : SetSort} → Variable [] sort → Term signature [] free sort =>
    formula node values (template.body.substituteMapped b substitution)) he)
  apply formula_substituteFree node (prepend (term node values left) (fun _ => term node values right)) values
    (VariableSubstitution.cons left (VariableSubstitution.cons right VariableSubstitution.empty)) ?_ template.body
  intro sort entry
  cases entry with
  | here => rfl
  | there entry =>
    cases entry with
    | here => rfl
    | there entry => cases entry

theorem term_weakenFree (node : Nat → List α → α) (values : Nat → α) (first : α)
    {bound free : SetContext} (input : SetTerm bound free) :
    term node (prepend first values) (input.weakenFree SetSort.set) = term node values input := by
  have h := term_mapped node values (prepend first values) VariableSubstitution.boundId
    (VariableSubstitution.of_renaming (VariableRenaming.weaken SetSort.set))
    (fun _ => rfl) (fun _ => rfl) input
  simpa only [Term.substituteMapped_of_renaming] using! h

theorem term_weakenBound (node : Nat → List α → α) (values : Nat → α)
    {free : SetContext} (input : SetOpenTerm free) :
    term node values (input.weakenBound SetSort.set) = term node values input := by
  have h := term_mapped node values values
    (VariableSubstitution.of_bound_renaming (VariableRenaming.weaken SetSort.set)) VariableSubstitution.freeId
    (by intro sort entry; cases entry) (fun _ => rfl) input
  simpa only [Term.substituteMapped_of_bound_renaming] using! h

/-- 自由重命名只改变数码环境；bound 编号保持不变。 -/
theorem formula_renamed (node : Nat → List α → α) (source target : Nat → α)
    {bound sf tf : SetContext} (f : VariableRenaming sf tf)
    (hf : ∀ {sort} (entry : Variable sf sort), target (f entry).index = source entry.index)
    (input : SetFormula bound sf) :
    formula node target (input.renameMapped VariableRenaming.id f) = formula node source input := by
  have h := formula_mapped_of_depth node source target VariableSubstitution.boundId
    (VariableSubstitution.of_renaming (bound := bound) f)
    (fun depth _ entry => by rw [ProofT.SyntaxTransform.boundLift_id]; rfl) (by
      intro depth sort entry
      have he : ProofT.SyntaxTransform.freeLift (VariableSubstitution.of_renaming (bound := bound) f) depth entry = .fvar (f entry) := by
        induction depth with
        | zero => rfl
        | succ depth ih =>
          change (ProofT.SyntaxTransform.freeLift (VariableSubstitution.of_renaming (bound := bound) f) depth entry).weakenBound SetSort.set = _
          rw [ih]
          rfl
      rw [he]
      exact hf entry) 0 input
  simpa only [ProofT.SyntaxTransform.boundLift, ProofT.SyntaxTransform.freeLift, Formula.substituteMapped_of_renaming] using! h

theorem formula_weakenFree (node : Nat → List α → α) (values : Nat → α) (first : α)
    {bound free : SetContext} (input : SetFormula bound free) :
    formula node (prepend first values) (input.weakenFree SetSort.set) = formula node values input :=
  formula_renamed node values (prepend first values)
    (VariableRenaming.weaken SetSort.set) (fun _ => rfl) input

end YesMetaZFC.Automation.ObjectCodeInstantiation
