import YesMetaZFC.SetTheory.Definitional.Theory.Basic
import YesMetaZFC.Automation.DeriveFreeClosed

/-!
# 项目定义原子核的纯语法层

本模块只固定核心原子签名、公式构造与分层定义体，不引入集合论结构、解释或满足关系。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

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
    (hLeft : left.freeSupport = [])
    (hRight : right.freeSupport = []) :
    (pairArguments left right).FreeClosed := by
  intro entry
  refine Fin.cases ?_ (fun rest => ?_) entry
  · exact hLeft
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest
    exact hRight

@[simp] theorem pairArguments_freeClosed_iff {depth : Nat}
    (left right : Term depth) :
    (pairArguments left right).FreeClosed ↔
      left.freeSupport = [] ∧ right.freeSupport = [] := by
  constructor
  · intro hClosed
    exact ⟨by simpa using hClosed 0, by simpa using hClosed 1⟩
  · rintro ⟨hLeft, hRight⟩
    exact pairArguments_freeClosed left right hLeft hRight

def conjunction {depth : Nat} :
    List (Formula 1 depth) → Formula 1 depth
  | [] => .truth
  | [formula] => formula
  | formula :: rest => .conj formula (conjunction rest)

def disjunction {depth : Nat} :
    List (Formula 1 depth) → Formula 1 depth
  | [] => .falsum
  | [formula] => formula
  | formula :: rest => .disj formula (disjunction rest)

def extensionalEq {depth : Nat}
    (left right : Term depth) : Formula 1 depth :=
  .atom CoreAtom.extensionalEq (by decide) (pairArguments left right)

def extensionalNe {depth : Nat}
    (left right : Term depth) : Formula 1 depth :=
  .neg (extensionalEq left right)

def subset {depth : Nat}
    (left right : Term depth) : Formula 1 depth :=
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

def properSubset {depth : Nat}
    (left right : Term depth) : Formula 1 depth :=
  .conj (subset left right) (extensionalNe left right)

def forallMem {depth : Nat}
    (set : Term depth)
    (body : Formula 1 (depth + 1)) : Formula 1 depth :=
  .forallE <| .imp (.mem Term.newest set.weaken) body

def existsMem {depth : Nat}
    (set : Term depth)
    (body : Formula 1 (depth + 1)) : Formula 1 depth :=
  .existsE <| .conj (.mem Term.newest set.weaken) body

abbrev forallClosure (depth : Nat)
    (formula : Formula 1 depth) : OpenFormula :=
  _root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure depth formula

/-- 有界量词只要求集合项和正文自由闭合。 -/
@[simp] theorem forallMem_freeClosed {depth : Nat} (set : Term depth)
    (body : Formula 1 (depth + 1)) :
    (forallMem set body).FreeClosed ↔ set.freeSupport = [] ∧ body.FreeClosed := by
  simp [forallMem, Definitional.Formula.FreeClosed]
@[simp] theorem existsMem_freeClosed {depth : Nat} (set : Term depth)
    (body : Formula 1 (depth + 1)) :
    (existsMem set body).FreeClosed ↔ set.freeSupport = [] ∧ body.FreeClosed := by
  simp [existsMem, Definitional.Formula.FreeClosed]
@[simp] theorem extensionalNe_freeClosed {depth : Nat} (left right : Term depth) :
    (extensionalNe left right).FreeClosed ↔ left.freeSupport = [] ∧ right.freeSupport = [] := by
  simp [extensionalNe, Definitional.Formula.FreeClosed]
@[simp] theorem properSubset_freeClosed {depth : Nat} (left right : Term depth) :
    (properSubset left right).FreeClosed ↔ left.freeSupport = [] ∧ right.freeSupport = [] := by
  simp [properSubset, Definitional.Formula.FreeClosed]

end Formula

def definitions : Definitions coreSignature where
  body
    | .extensionalEq =>
        .forallE <|
          .iff (.mem (.bound 0) (.bound 1))
            (.mem (.bound 0) (.bound 2))
    | .subset =>
        .forallE <|
          .imp (.mem (.bound 0) (.bound 1))
            (.mem (.bound 0) (.bound 2))
  bodyFreeClosed := by
    intro symbol
    cases symbol <;>
      simp [Formula.FreeClosed]

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
