import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-! # 当前内核编码上的无捕获代入与全称闭合

原始树操作保留全部内核构造子；量词下同时提升两类变量像。
编码交换定理直接对齐类型安全内核的替换，不经过 Hilbert 化。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxSubstitution
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

/-- 重命名后代入只复合变量像，避免重新展开参数项的语法树。 -/
theorem term_rename_substitute {sb sf mb mf tb tf : SetContext}
    (br : VariableRenaming sb mb) (fr : VariableRenaming sf mf)
    (bs : VariableSubstitution signature mb tb tf) (fs : VariableSubstitution signature mf tb tf) :
    {sort : SetSort} → (input : Term signature sb sf sort) →
    (input.renameMapped br fr).substituteMapped bs fs =
      input.substituteMapped (fun entry => bs (br entry)) (fun entry => fs (fr entry)) := by
  intro sort input
  rw [Term.renameMapped_eq_substituteMapped, Term.substituteMapped_comp]
  rfl

theorem arguments_rename_substitute {sb sf mb mf tb tf : SetContext}
    (br : VariableRenaming sb mb) (fr : VariableRenaming sf mf)
    (bs : VariableSubstitution signature mb tb tf) (fs : VariableSubstitution signature mf tb tf) :
    {sorts : SetContext} → (args : Arguments signature sb sf sorts) →
    (args.renameMapped br fr).substituteMapped bs fs =
      args.substituteMapped (fun entry => bs (br entry)) (fun entry => fs (fr entry)) := by
  intro sort args
  rw [Arguments.renameMapped_eq_substituteMapped, Arguments.substituteMapped_comp]
  rfl


/-- 无论束缚变量如何代入，跨过新增自由槽只需跳过替换表的首项。 -/
theorem term_weakenFree_substitute {sb sf tb tf : SetContext} (introduced : SetSort)
    (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature (introduced :: sf) tb tf) :
    {sort : SetSort} → (input : Term signature sb sf sort) →
    (input.weakenFree introduced).substituteMapped bs fs =
      input.substituteMapped bs (fun entry => fs (.there entry)) := by
  intro sort input
  exact Term.substituteMapped_weakenFree_tail introduced bs fs input

theorem arguments_weakenFree_substitute {sb sf tb tf : SetContext} (introduced : SetSort)
    (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature (introduced :: sf) tb tf) :
    {sorts : SetContext} → (args : Arguments signature sb sf sorts) →
    (args.weakenFree introduced).substituteMapped bs fs =
      args.substituteMapped bs (fun entry => fs (.there entry)) := by
  intro sort args
  exact Arguments.substituteMapped_weakenFree_tail introduced bs fs args


mutual
/-- 原项没有束缚变量时，任意束缚变量替换都不起作用。 -/
theorem closed_term_substitute {sf tb tf : SetContext}
    (bs : VariableSubstitution signature [] tb tf) (ρ : VariableRenaming sf tf) :
    {sort : SetSort} → (input : Term signature [] sf sort) →
    input.substituteMapped bs (fun entry => .fvar (ρ entry)) = (input.renameFree ρ).embedBoundClosed tb
  | _, .bvar entry => nomatch entry
  | _, .fvar _ => by simp [Term.substituteMapped, Term.renameFree, Term.rename, Renaming.free, Term.renameMapped]
  | _, .app symbol args => by
    simp only [Term.substituteMapped, Term.renameFree, Term.rename, Renaming.free, Term.renameMapped,
      Term.embedBoundClosed_app]
    rw [closed_arguments_substitute bs ρ args]
    rfl

theorem closed_arguments_substitute {sf tb tf : SetContext}
    (bs : VariableSubstitution signature [] tb tf) (ρ : VariableRenaming sf tf) :
    {sorts : SetContext} → (args : Arguments signature [] sf sorts) →
    args.substituteMapped bs (fun entry => .fvar (ρ entry)) = (args.renameFree ρ).embedBoundClosed tb
  | _, .nil => by simp [Arguments.substituteMapped, Arguments.renameFree, Arguments.rename, Renaming.free,
      Arguments.renameMapped]
  | _, .cons head tail => by
    simp only [Arguments.substituteMapped, Arguments.renameFree, Arguments.rename, Renaming.free,
      Arguments.renameMapped, Arguments.embedBoundClosed_cons]
    rw [closed_term_substitute bs ρ head, closed_arguments_substitute bs ρ tail]
    rfl
end

theorem term_weakenBound_substitute {sb sf tb tf : SetContext} (introduced : SetSort)
    (bs : VariableSubstitution signature (introduced :: sb) tb tf)
    (fs : VariableSubstitution signature sf tb tf) {sort : SetSort}
    (input : Term signature sb sf sort) :
    (input.weakenBound introduced).substituteMapped bs fs =
      input.substituteMapped (fun entry => bs (.there entry)) fs := by
  exact Term.substituteMapped_weakenBound_tail introduced bs fs input

theorem closed_term_substitute_id {free bound : SetContext}
    (bs : VariableSubstitution signature [] bound free) {sort : SetSort}
    (input : Term signature [] free sort) :
    input.substituteMapped bs (fun entry => .fvar entry) = input.embedBoundClosed bound := by
  have hid : input.renameFree VariableRenaming.id = input :=
    (Term.substituteMapped_of_renaming VariableRenaming.id input).symm.trans
      (Term.substituteMapped_id input)
  simpa only [hid, VariableRenaming.id] using closed_term_substitute bs VariableRenaming.id input


def bvar (index : Nat) : Tree := .node 0 [leaf index]
def fvar (index : Nat) : Tree := .node 1 [leaf index]

mutual
def term (bound free : Nat → Tree) : Tree → Tree
  | .node 0 [.node index []] => bound index
  | .node 1 [.node index []] => free index
  | .node 2 (symbol :: args) => .node 2 (symbol :: terms bound free args)
  | input => input
def terms (bound free : Nat → Tree) : List Tree → List Tree
  | [] => []
  | head :: tail => term bound free head :: terms bound free tail
end

mutual
theorem term_substitute {sb sf tb tf : SetContext} (b f : Nat → Tree)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = SyntaxEncode.term (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = SyntaxEncode.term (fs entry)) :
    {sort : SetSort} → (input : Term signature sb sf sort) →
    term b f (SyntaxEncode.term input) = SyntaxEncode.term (input.substituteMapped bs fs)
  | _, .bvar entry => hb entry
  | _, .fvar entry => hf entry
  | _, .app symbol args => by
      simp only [SyntaxEncode.term_app, term, Term.substituteMapped]
      rw [arguments_substitute b f bs fs hb hf args]

theorem arguments_substitute {sb sf tb tf : SetContext} (b f : Nat → Tree)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = SyntaxEncode.term (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = SyntaxEncode.term (fs entry)) :
    {sorts : SetContext} → (args : Arguments signature sb sf sorts) →
    terms b f (SyntaxEncode.argumentsList args) = SyntaxEncode.argumentsList (args.substituteMapped bs fs)
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [SyntaxEncode.argumentsList, terms, Arguments.substituteMapped]
      rw [term_substitute b f bs fs hb hf head, arguments_substitute b f bs fs hb hf tail]
end

def shift (input : Tree) : Tree := term (fun i => bvar (i + 1)) fvar input

theorem shift_encode {bound free : SetContext} {sort : SetSort} (input : Term signature bound free sort) :
    shift (SyntaxEncode.term input) = SyntaxEncode.term (input.weakenBound SetSort.set) := by
  have h := term_substitute (fun i => bvar (i + 1)) fvar
    (VariableSubstitution.of_bound_renaming (VariableRenaming.weaken SetSort.set))
    (VariableSubstitution.freeId : VariableSubstitution signature free (SetSort.set :: bound) free)
    (fun _ => rfl) (fun _ => rfl) input
  simpa only [shift, Term.substituteMapped_of_bound_renaming, Term.weakenBound, Term.rename,
    Renaming.weakenBound, Renaming.bound] using h

def lift (bound : Nat → Tree) : Nat → Tree
  | 0 => bvar 0
  | i + 1 => shift (bound i)

def formula (bound free : Nat → Tree) : Tree → Tree
  | .node 2 (symbol :: args) => .node 2 (symbol :: terms bound free args)
  | .node 3 [left, right] => .node 3 [term bound free left, term bound free right]
  | .node 4 [body] => .node 4 [formula bound free body]
  | .node 5 [left, right] => .node 5 [formula bound free left, formula bound free right]
  | .node 6 [left, right] => .node 6 [formula bound free left, formula bound free right]
  | .node 7 [left, right] => .node 7 [formula bound free left, formula bound free right]
  | .node 8 [left, right] => .node 8 [formula bound free left, formula bound free right]
  | .node 9 [body] => .node 9 [formula (lift bound) (fun i => shift (free i)) body]
  | .node 10 [body] => .node 10 [formula (lift bound) (fun i => shift (free i)) body]
  | input => input
termination_by input => sizeOf input

theorem formula_substitute {sb sf tb tf : SetContext} (b f : Nat → Tree)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), b entry.index = SyntaxEncode.term (bs entry))
    (hf : ∀ {sort} (entry : Variable sf sort), f entry.index = SyntaxEncode.term (fs entry))
    (input : SetFormula sb sf) :
    formula b f (SyntaxEncode.formula input) = SyntaxEncode.formula (input.substituteMapped bs fs) := by
  induction input generalizing tb tf b f with
  | falsum => simp only [SyntaxEncode.formula, leaf, formula, Formula.substituteMapped]
  | truth => simp only [SyntaxEncode.formula, leaf, formula, Formula.substituteMapped]
  | rel symbol args =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    rw [arguments_substitute b f bs fs hb hf args]
  | equal left right =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    rw [term_substitute b f bs fs hb hf left, term_substitute b f bs fs hb hf right]
  | neg body ih => simp only [SyntaxEncode.formula, formula, Formula.substituteMapped, ih b f bs fs hb hf]
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr | iff left right ihl ihr =>
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped, ihl b f bs fs hb hf, ihr b f bs fs hb hf]
  | forallE sort body ih | existsE sort body ih =>
    cases sort
    simp only [SyntaxEncode.formula, formula, Formula.substituteMapped]
    congr 2
    apply ih
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry => exact (congrArg shift (hb entry)).trans (shift_encode (bs entry))
    · intro sort entry
      exact (congrArg shift (hf entry)).trans (shift_encode (fs entry))

/-- 将最新自由变量变为新束缚变量，其他变量按内核约定移动。 -/
def abstractTop (input : Tree) : Tree :=
  formula (fun i => bvar (i + 1)) (fun i => match i with | 0 => bvar 0 | j + 1 => fvar j) input

theorem abstractTop_encode {bound free : SetContext} (input : SetFormula bound (SetSort.set :: free)) :
    abstractTop (SyntaxEncode.formula input) = SyntaxEncode.formula input.abstractFreeTop := by
  unfold abstractTop Formula.abstractFreeTop Formula.substitute Substitution.abstractFreeTop
  apply formula_substitute
  · intro sort entry
    rfl
  · intro sort entry
    cases entry <;> rfl

/-- 按实际 forall_close 的顺序逐层关闭全部自由参数。 -/
def close : Nat → Tree → Tree
  | 0, input => input
  | n + 1, input => close n (.node 9 [abstractTop input])

theorem close_encode {free : SetContext} (input : SetOpenFormula free) :
    close free.length (SyntaxEncode.formula input) = SyntaxEncode.formula (Metatheory.Formula.forall_close input) := by
  induction free with
  | nil => rfl
  | cons sort free ih =>
    cases sort
    rw [List.length_cons, close, abstractTop_encode]
    exact ih (input.forallFreeTop SetSort.set)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxSubstitution
