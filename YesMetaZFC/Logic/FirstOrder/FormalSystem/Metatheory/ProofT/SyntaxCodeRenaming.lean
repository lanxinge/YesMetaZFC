import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxSubstitution

/-! # 保持变量编号的重命名与空量词编码

上下文类型可以变化；只要实际出现的变量编号不变，当前 quotation 树就不变。
该事实给出空量词公理及存在消去模式所需的直接模板。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxCodeRenaming
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

mutual
theorem term {sb sf tb tf : SetContext} (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf)
    (hb : ∀ {sort} (entry : Variable sb sort), (br entry).index = entry.index)
    (hf : ∀ {sort} (entry : Variable sf sort), (fr entry).index = entry.index) :
    {sort : SetSort} → (input : Term signature sb sf sort) →
    SyntaxEncode.term (input.renameMapped br fr) = SyntaxEncode.term input
  | _, .bvar entry => by simp [Term.renameMapped, hb entry]
  | _, .fvar entry => by simp [Term.renameMapped, hf entry]
  | _, .app symbol args => by
    simp only [Term.renameMapped, SyntaxEncode.term_app]
    rw [arguments br fr hb hf args]

theorem arguments {sb sf tb tf : SetContext} (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf)
    (hb : ∀ {sort} (entry : Variable sb sort), (br entry).index = entry.index)
    (hf : ∀ {sort} (entry : Variable sf sort), (fr entry).index = entry.index) :
    {sorts : SetContext} → (input : Arguments signature sb sf sorts) →
    SyntaxEncode.argumentsList (input.renameMapped br fr) = SyntaxEncode.argumentsList input
  | _, .nil => rfl
  | _, .cons first rest => by
    simp only [Arguments.renameMapped, SyntaxEncode.argumentsList]
    rw [term br fr hb hf first, arguments br fr hb hf rest]
end

theorem formula {sb sf tb tf : SetContext} (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf)
    (hb : ∀ {sort} (entry : Variable sb sort), (br entry).index = entry.index)
    (hf : ∀ {sort} (entry : Variable sf sort), (fr entry).index = entry.index)
    (input : SetFormula sb sf) :
    SyntaxEncode.formula (input.renameMapped br fr) = SyntaxEncode.formula input := by
  induction input generalizing tb tf with
  | falsum | truth => rfl
  | rel symbol args => simp [Formula.renameMapped, SyntaxEncode.formula, arguments br fr hb hf args]
  | equal left right => simp [Formula.renameMapped, SyntaxEncode.formula, term br fr hb hf left, term br fr hb hf right]
  | neg body ih => simp [Formula.renameMapped, SyntaxEncode.formula, ih br fr hb hf]
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr | iff left right ihl ihr =>
    simp [Formula.renameMapped, SyntaxEncode.formula, ihl br fr hb hf, ihr br fr hb hf]
  | forallE sort body ih | existsE sort body ih =>
    simp only [Formula.renameMapped, SyntaxEncode.formula]
    congr 2
    apply ih _ fr _ hf
    intro other entry
    cases entry with
    | here => rfl
    | there entry => exact congrArg Nat.succ (hb entry)

/-- 公式的自由加强在代入前被消去，只需跳过变量像表的首项。 -/
theorem weakenFree_substitute {sb sf tb tf : SetContext} (introduced : SetSort)
    (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature (introduced :: sf) tb tf)
    (input : SetFormula sb sf) :
    (input.weakenFree introduced).substituteMapped bs fs =
      input.substituteMapped bs (fun entry => fs (.there entry)) := by
  exact Formula.substituteMapped_weakenFree_tail introduced bs fs input

/-- 在空束缚上下文中先加强再抽象，不改变正文 quotation。 -/
theorem vacuous_body {free : SetContext} (input : SetOpenFormula free) :
    SyntaxEncode.formula ((input.weakenFree SetSort.set).abstractFreeTop) = SyntaxEncode.formula input := by
  change SyntaxEncode.formula ((input.weakenFree SetSort.set).substituteMapped
    (fun entry => VariableSubstitution.abstractBound (σ := signature) (bound := []) (free := free) SetSort.set entry)
    (fun entry => VariableSubstitution.abstractFreeTop (σ := signature) (bound := []) entry)) = _
  rw [weakenFree_substitute]
  change SyntaxEncode.formula (input.substituteMapped
    (VariableSubstitution.of_bound_renaming (VariableRenaming.weaken SetSort.set)) VariableSubstitution.freeId) = _
  rw [Formula.substituteMapped_of_bound_renaming]
  exact formula _ _ (by intro sort entry; cases entry) (fun _ => rfl) input

@[simp] theorem fromSentence {free : SetContext} (input : SetSentence) :
    SyntaxEncode.formula (Formula.fromSentence (free := free) input) = SyntaxEncode.formula input := by
  cases free with
  | nil => rfl
  | cons sort free =>
    exact formula VariableRenaming.id VariableRenaming.empty (fun _ => rfl) (by intro sort entry; cases entry) input

@[simp] theorem substitutionArguments_substitution {bound free : SetContext} {sorts : SetContext}
    (args : Arguments signature bound free sorts) :
    SyntaxEncode.substitutionArguments sorts (SyntaxDecode.substitution args) = args := by
  cases args with
  | nil => rfl
  | cons first rest =>
    cases ‹SetSort›
    simpa only [SyntaxEncode.substitutionArguments, SyntaxDecode.substitution, VariableSubstitution.cons] using congrArg (Arguments.cons first) (substitutionArguments_substitution rest)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxCodeRenaming
