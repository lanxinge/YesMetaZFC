import YesMetaZFC.SetTheory.Definitional.DeepRfl

/-!
# YesMetaZFC 项目级定义原子签名

本模块把通用的带定义原子核实例化为集合论主线使用的固定签名。第一层只把最底层、
最高频且定义体纯粹由 `∈` 构成的外延等同和子集关系提升为原子；更高层的有序对、
函数和序数原子在后续模块中按同一接口追加。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

universe v

inductive CoreAtom where
  | extensionalEq
  | subset
  deriving Repr, BEq, DecidableEq, Hashable

@[reducible] def coreSignature : AtomSignature where
  Symbol := CoreAtom
  arity := fun _ => 2
  stage := fun _ => 0
  maxStage := 1
  stage_lt_maxStage := by
    intro symbol
    cases symbol <;> decide

abbrev Term (depth : Nat) :=
  Definitional.Term depth

namespace Term

abbrev bound {depth : Nat} : Fin depth → Term depth :=
  Definitional.Term.bound

abbrev free {depth : Nat} : FreeVarId → Term depth :=
  Definitional.Term.free

abbrev bind {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth) :
    Term sourceDepth → Term targetDepth :=
  Definitional.Term.bind substitution

abbrev rename {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (term : Term sourceDepth) : Term targetDepth :=
  Definitional.Term.rename indexMap term

abbrev weaken {depth : Nat} (term : Term depth) : Term (depth + 1) :=
  Definitional.Term.weaken term

abbrev newest {depth : Nat} : Term (depth + 1) :=
  Definitional.Term.newest

abbrev liftSubstitution {sourceDepth targetDepth : Nat}
    (substitution : Fin sourceDepth → Term targetDepth) :
    Fin (sourceDepth + 1) → Term (targetDepth + 1) :=
  Definitional.Term.liftSubstitution substitution

abbrev freeSupport {depth : Nat} : Term depth → List FreeVarId :=
  Definitional.Term.freeSupport

@[simp] theorem eval_bound {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (entry : Fin depth) :
    Definitional.Term.eval env (.bound entry) = env.bound entry :=
  rfl

@[simp] theorem eval_free {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (id : FreeVarId) :
    Definitional.Term.eval env (.free id : Term depth) = env.free id :=
  rfl

@[simp] theorem eval_bound_zero_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 0) = value :=
  rfl

@[simp] theorem eval_bound_one_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 1)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 1) =
      Definitional.Term.eval env (.bound 0) :=
  rfl

@[simp] theorem eval_bound_two_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 2)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 2) =
      Definitional.Term.eval env (.bound 1) :=
  rfl

@[simp] theorem eval_bound_three_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 3)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 3) =
      Definitional.Term.eval env (.bound 2) :=
  rfl

/-- 一次压栈后，index `4` 指向此前的 index `3`。 -/
@[simp] theorem eval_bound_four_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 4)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 4) =
      Definitional.Term.eval env (.bound 3) :=
  rfl

/-- 一次压栈后，index `5` 指向此前的 index `4`。 -/
@[simp] theorem eval_bound_five_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 5)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 5) =
      Definitional.Term.eval env (.bound 4) :=
  rfl

/-- 一次压栈后，index `6` 指向此前的 index `5`。 -/
@[simp] theorem eval_bound_six_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 6)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 6) =
      Definitional.Term.eval env (.bound 5) :=
  rfl

/-- 一次压栈后，index `7` 指向此前的 index `6`。 -/
@[simp] theorem eval_bound_seven_push {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ (depth + 7)) (value : ℳ.Domain) :
    Definitional.Term.eval (env.push value) (.bound 7) =
      Definitional.Term.eval env (.bound 6) :=
  rfl

end Term

abbrev Formula (availableStage depth : Nat) :=
  Definitional.Formula coreSignature availableStage depth

abbrev RootFormula (depth : Nat) :=
  Definitional.RootFormula coreSignature depth

abbrev OpenFormula :=
  Definitional.OpenFormula coreSignature

namespace Formula

def pairArguments {depth : Nat} (left right : Term depth) :
    TermVector 2 depth where
  terms := #[left, right]
  size_eq := rfl

@[simp] theorem pairArguments_get_zero {depth : Nat}
    (left right : Term depth) :
    pairArguments left right (0 : Fin 2) = left :=
  rfl

@[simp] theorem pairArguments_get_one {depth : Nat}
    (left right : Term depth) :
    pairArguments left right (1 : Fin 2) = right :=
  rfl

theorem pairArguments_freeClosed {depth : Nat}
    (left right : Term depth)
    (hLeft : left.freeSupport = []) (hRight : right.freeSupport = []) :
    (pairArguments left right).FreeClosed := by
  intro entry
  refine Fin.cases ?_ (fun rest => ?_) entry
  · simpa [pairArguments] using hLeft
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest
    simpa [pairArguments] using hRight

@[simp] theorem pairArguments_freeClosed_iff {depth : Nat}
    (left right : Term depth) :
    (pairArguments left right).FreeClosed ↔
      left.freeSupport = [] ∧ right.freeSupport = [] := by
  constructor
  · intro hClosed
    exact ⟨by simpa using hClosed 0, by simpa using hClosed 1⟩
  · rintro ⟨hLeft, hRight⟩
    exact pairArguments_freeClosed left right hLeft hRight

def conjunction {depth : Nat} : List (Formula 1 depth) → Formula 1 depth
  | [] => .truth
  | [formula] => formula
  | formula :: rest => .conj formula (conjunction rest)

def disjunction {depth : Nat} : List (Formula 1 depth) → Formula 1 depth
  | [] => .falsum
  | [formula] => formula
  | formula :: rest => .disj formula (disjunction rest)

def extensionalEq {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .atom CoreAtom.extensionalEq (by decide) (pairArguments left right)

def extensionalNe {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .neg (extensionalEq left right)

def subset {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .atom CoreAtom.subset (by decide) (pairArguments left right)

@[simp] theorem extensionalEq_freeClosed_iff {depth : Nat}
    (left right : Term depth) :
    (extensionalEq left right).FreeClosed ↔
      left.freeSupport = [] ∧ right.freeSupport = [] := by
  simp only [extensionalEq, Definitional.Formula.FreeClosed]
  exact pairArguments_freeClosed_iff left right

@[simp] theorem subset_freeClosed_iff {depth : Nat}
    (left right : Term depth) :
    (subset left right).FreeClosed ↔
      left.freeSupport = [] ∧ right.freeSupport = [] := by
  simp only [subset, Definitional.Formula.FreeClosed]
  exact pairArguments_freeClosed_iff left right

def properSubset {depth : Nat} (left right : Term depth) : Formula 1 depth :=
  .conj (subset left right) (extensionalNe left right)

def forallMem {depth : Nat} (set : Term depth)
    (body : Formula 1 (depth + 1)) : Formula 1 depth :=
  .forallE <| .imp
    (.mem Term.newest set.weaken)
    body

def existsMem {depth : Nat} (set : Term depth)
    (body : Formula 1 (depth + 1)) : Formula 1 depth :=
  .existsE <| .conj
    (.mem Term.newest set.weaken)
    body

abbrev forallClosure (depth : Nat) (formula : Formula 1 depth) : OpenFormula :=
  _root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure depth formula

end Formula

def definitions : Definitions coreSignature where
  body
    | .extensionalEq =>
        .forallE <| .iff
          (.mem (.bound 0) (.bound 1))
          (.mem (.bound 0) (.bound 2))
    | .subset =>
        .forallE <| .imp
          (.mem (.bound 0) (.bound 1))
          (.mem (.bound 0) (.bound 2))
  bodyFreeClosed := by
    intro symbol
    cases symbol <;>
      simp [Formula.FreeClosed]

namespace Semantics

private def argument {ℳ : Structure}
    (arguments : Fin 2 → ℳ.Domain) (index : Nat)
    (hIndex : index < 2) : ℳ.Domain :=
  arguments ⟨index, hIndex⟩

def interpretation : Interpretation.{0, v} coreSignature where
  atom := fun {ℳ} symbol arguments _free =>
    match symbol with
    | .extensionalEq =>
        ∀ value, ℳ.mem value (argument arguments 0 (by decide)) ↔
          ℳ.mem value (argument arguments 1 (by decide))
    | .subset =>
        ∀ value, ℳ.mem value (argument arguments 0 (by decide)) →
          ℳ.mem value (argument arguments 1 (by decide))

end Semantics

def kernel : Kernel.{0, v} coreSignature where
  definitions := definitions
  interpretation := Semantics.interpretation
  atom_iff := by
    intro ℳ symbol hExtensional arguments free
    cases symbol with
    | extensionalEq =>
        change (Fin 2 → ℳ.Domain) at arguments
        simp only [Semantics.interpretation, definitions,
          Semantics.satisfies, Term.eval, Env.push]
        change
          (∀ value, ℳ.mem value (arguments 0) ↔
            ℳ.mem value (arguments 1)) ↔
          ∀ value, ℳ.mem value (arguments 0) ↔
            ℳ.mem value (arguments 1)
        rfl
    | subset =>
        change (Fin 2 → ℳ.Domain) at arguments
        simp only [Semantics.interpretation, definitions,
          Semantics.satisfies, Term.eval, Env.push]
        change
          (∀ value, ℳ.mem value (arguments 0) →
            ℳ.mem value (arguments 1)) ↔
          ∀ value, ℳ.mem value (arguments 0) →
            ℳ.mem value (arguments 1)
        rfl

namespace Formula

def satisfies {ℳ : Structure.{v}} {depth : Nat} (env : Env ℳ depth)
    (formula : Formula 1 depth) : Prop :=
  Definitional.Semantics.satisfies Semantics.interpretation env formula

@[deep_rfl 2000] theorem satisfies_falsum_iff
    {ℳ : Structure.{v}} {depth : Nat} (env : Env ℳ depth) :
    satisfies env (.falsum : Formula 1 depth) ↔ False := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_truth_iff
    {ℳ : Structure.{v}} {depth : Nat} (env : Env ℳ depth) :
    satisfies env (.truth : Formula 1 depth) ↔ True := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_mem_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (.mem left right) ↔
      ℳ.mem (Definitional.Term.eval env left)
        (Definitional.Term.eval env right) := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_neg_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (formula : Formula 1 depth) :
    satisfies env (.neg formula) ↔ ¬ satisfies env formula := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_conj_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Formula 1 depth) :
    satisfies env (.conj left right) ↔
      satisfies env left ∧ satisfies env right := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_disj_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Formula 1 depth) :
    satisfies env (.disj left right) ↔
      satisfies env left ∨ satisfies env right := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_imp_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Formula 1 depth) :
    satisfies env (.imp left right) ↔
      (satisfies env left → satisfies env right) := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_iff_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Formula 1 depth) :
    satisfies env (.iff left right) ↔
      (satisfies env left ↔ satisfies env right) := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_forall_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (body : Formula 1 (depth + 1)) :
    satisfies env (.forallE body) ↔
      ∀ value, satisfies (env.push value) body := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[deep_rfl 2000] theorem satisfies_exists_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (body : Formula 1 (depth + 1)) :
    satisfies env (.existsE body) ↔
      ∃ value, satisfies (env.push value) body := by
  simp only [satisfies, Definitional.Semantics.satisfies]

@[simp, prove_auto_norm semantic]
theorem satisfies_forallMem_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (set : Term depth)
    (body : Formula 1 (depth + 1)) :
    satisfies env (forallMem set body) ↔
      ∀ value, ℳ.mem value (Definitional.Term.eval env set) →
        satisfies (env.push value) body := by
  simp [forallMem, satisfies, Definitional.Semantics.satisfies]

@[simp, prove_auto_norm semantic]
theorem satisfies_existsMem_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (set : Term depth)
    (body : Formula 1 (depth + 1)) :
    satisfies env (existsMem set body) ↔
      ∃ value, ℳ.mem value (Definitional.Term.eval env set) ∧
        satisfies (env.push value) body := by
  simp [existsMem, satisfies, Definitional.Semantics.satisfies]

@[simp, prove_auto_norm semantic]
theorem satisfies_rename
    {ℳ : Structure.{v}} {sourceDepth targetDepth : Nat}
    (env : Env ℳ targetDepth)
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (formula : Formula 1 sourceDepth) :
    satisfies env (formula.rename indexMap) ↔
      satisfies (Env.reindex env indexMap) formula :=
  Definitional.Semantics.satisfies_rename
    Semantics.interpretation env indexMap formula

@[simp]
theorem satisfies_bind
    {ℳ : Structure.{v}} {sourceDepth targetDepth : Nat}
    (env : Env ℳ targetDepth)
    (substitution : Fin sourceDepth → Term targetDepth)
    (formula : Formula 1 sourceDepth) :
    satisfies env (formula.bind substitution) ↔
      satisfies (Definitional.Env.substitute env substitution) formula := by
  simpa [satisfies] using
    (Definitional.Semantics.satisfies_bind
      Semantics.interpretation env substitution formula)

theorem satisfies_forallClosure_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (free : FreeVarId → ℳ.Domain)
    (formula : Formula 1 depth) :
    satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        (Formula.forallClosure depth formula) ↔
    ∀ bound : Fin depth → ℳ.Domain,
        satisfies ({ bound := bound, free := free } : Env ℳ depth) formula :=
  by
    simpa [satisfies, Formula.forallClosure] using
      (Definitional.Semantics.satisfies_forallClosure_iff
        Semantics.interpretation free formula)

/-- 任意参数向量上的外延等同原子语义。 -/
theorem satisfies_atom_extensionalEq_iff
    {ℳ : Structure.{v}} {depth : Nat} (env : Env ℳ depth)
    (hStage : coreSignature.stage CoreAtom.extensionalEq < 1)
    (arguments : TermVector 2 depth) :
    satisfies env (.atom CoreAtom.extensionalEq hStage arguments) ↔
      ∀ value,
        ℳ.mem value (Definitional.Term.eval env (arguments 0)) ↔
          ℳ.mem value (Definitional.Term.eval env (arguments 1)) := by
  simp [satisfies, Definitional.Semantics.satisfies,
    Semantics.interpretation, Semantics.argument, TermVector.eval]

/-- 任意参数向量上的子集原子语义。 -/
theorem satisfies_atom_subset_iff
    {ℳ : Structure.{v}} {depth : Nat} (env : Env ℳ depth)
    (hStage : coreSignature.stage CoreAtom.subset < 1)
    (arguments : TermVector 2 depth) :
    satisfies env (.atom CoreAtom.subset hStage arguments) ↔
      ∀ value,
        ℳ.mem value (Definitional.Term.eval env (arguments 0)) →
          ℳ.mem value (Definitional.Term.eval env (arguments 1)) := by
  simp [satisfies, Definitional.Semantics.satisfies,
    Semantics.interpretation, Semantics.argument, TermVector.eval]

@[deep_rfl 2000] theorem satisfies_extensionalEq_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (extensionalEq left right) ↔
      ∀ value, ℳ.mem value (Definitional.Term.eval env left) ↔
        ℳ.mem value (Definitional.Term.eval env right) := by
  cases left <;> cases right <;>
    simp [satisfies, extensionalEq, pairArguments,
    Definitional.Semantics.satisfies, TermVector.eval, TermVector.get,
    Semantics.interpretation, Semantics.argument, Definitional.Term.eval]

/-- 在外延结构中，项目外延等同原子恰好解释为 Lean 对象相等。 -/
theorem satisfies_extensionalEq_iff_eq
    {ℳ : Structure.{v}} (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (extensionalEq left right) ↔
      Definitional.Term.eval env left =
        Definitional.Term.eval env right := by
  rw [satisfies_extensionalEq_iff]
  constructor
  · exact hExt.eq_of_same_members _ _
  · intro hEq value
    simpa [hEq]

@[deep_rfl 2000] theorem satisfies_subset_iff
    {ℳ : Structure.{v}} {depth : Nat}
    (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (subset left right) ↔
      ∀ value, ℳ.mem value (Definitional.Term.eval env left) →
        ℳ.mem value (Definitional.Term.eval env right) := by
  cases left <;> cases right <;>
    simp [satisfies, subset, pairArguments,
    Definitional.Semantics.satisfies, TermVector.eval, TermVector.get,
    Semantics.interpretation, Semantics.argument, Definitional.Term.eval]

end Formula

abbrev Theory :=
  YesMetaZFC.SetTheory.Definitional.Theory coreSignature

abbrev Sentence :=
  YesMetaZFC.SetTheory.Definitional.Sentence coreSignature

namespace Sentence

def ofFormula (formula : OpenFormula) (freeClosed : formula.FreeClosed) :
    Sentence where
  formula := formula
  freeClosed := freeClosed

def forallClosure {depth : Nat} (formula : Formula 1 depth)
    (freeClosed : formula.FreeClosed) : Sentence where
  formula := Formula.forallClosure depth formula
  freeClosed :=
    (_root_.YesMetaZFC.SetTheory.Definitional.Formula.freeClosed_forallClosure
      formula).mpr freeClosed

end Sentence

end Project
end Definitional
end SetTheory
end YesMetaZFC
