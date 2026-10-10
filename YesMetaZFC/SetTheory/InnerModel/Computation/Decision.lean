import YesMetaZFC.SetTheory.InnerModel.Computation.Boolean

/-! # Δ₀ 判定指令及两个可执行后端

判定指令只读取集合寄存器，量词指令只遍历某一寄存器中的集合。
一个后端生成实际集合程序，另一个生成原 Project 公式；指令本身不调用公式真值。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project

inductive Cp_test : Nat → Type where
  | falsum {n} : Cp_test n
  | truth {n} : Cp_test n
  | mem {n} : Fin n → Fin n → Cp_test n
  | eq {n} : Fin n → Fin n → Cp_test n
  | subset {n} : Fin n → Fin n → Cp_test n
  | neg {n} : Cp_test n → Cp_test n
  | conj {n} : Cp_test n → Cp_test n → Cp_test n
  | disj {n} : Cp_test n → Cp_test n → Cp_test n
  | imp {n} : Cp_test n → Cp_test n → Cp_test n
  | iff {n} : Cp_test n → Cp_test n → Cp_test n
  | all {n} : Fin n → Cp_test (n + 1) → Cp_test n
  | any {n} : Fin n → Cp_test (n + 1) → Cp_test n

def cp_test_code_l : {n : Nat} → Cp_test n → Cp_code n
  | _, .falsum => .zero
  | _, .truth => cp_one_l
  | _, .mem i j => cp_member_l (.var i) (.var j)
  | _, .eq i j => cp_equal_l (.var i) (.var j)
  | _, .subset i j => cp_subset_l (.var i) (.var j)
  | _, .neg p => cp_not_l (cp_test_code_l p)
  | _, .conj p q => cp_and_l (cp_test_code_l p) (cp_test_code_l q)
  | _, .disj p q => cp_or_l (cp_test_code_l p) (cp_test_code_l q)
  | _, .imp p q => cp_imp_l (cp_test_code_l p) (cp_test_code_l q)
  | _, .iff p q => cp_iff_l (cp_test_code_l p) (cp_test_code_l q)
  | _, .all i p => cp_not_l (.bunion (.var i) (cp_not_l (cp_test_code_l p)))
  | _, .any i p => .bunion (.var i) (cp_test_code_l p)

def cp_test_formula_l : {n : Nat} → Cp_test n → Formula 1 n
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem i j => .mem (.bound i) (.bound j)
  | _, .eq i j => Formula.extensionalEq (.bound i) (.bound j)
  | _, .subset i j => Formula.subset (.bound i) (.bound j)
  | _, .neg p => .neg (cp_test_formula_l p)
  | _, .conj p q => .conj (cp_test_formula_l p) (cp_test_formula_l q)
  | _, .disj p q => .disj (cp_test_formula_l p) (cp_test_formula_l q)
  | _, .imp p q => .imp (cp_test_formula_l p) (cp_test_formula_l q)
  | _, .iff p q => .iff (cp_test_formula_l p) (cp_test_formula_l q)
  | _, .all i p => Formula.forallMem (.bound i) (cp_test_formula_l p)
  | _, .any i p => Formula.existsMem (.bound i) (cp_test_formula_l p)

theorem cp_test_closed_l {n} (p : Cp_test n) : (cp_test_formula_l p).FreeClosed := by
  induction p <;> simp_all -implicitDefEqProofs [cp_test_formula_l, Definitional.Formula.FreeClosed]

theorem cp_test_delta_l {n} (p : Cp_test n) : (cp_test_formula_l p).IsDelta0 := by
  induction p with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem i j => exact .mem _ _
  | eq i j | subset i j => exact .atom _ _ _
  | neg _ h => exact .neg h
  | conj _ _ h k => exact .conj h k
  | disj _ _ h k => exact .disj h k
  | imp _ _ h k => exact .imp h k
  | iff _ _ h k => exact .iff h k
  | all i _ h => exact .forallMem _ h
  | any i _ h => exact .existsMem _ h

def cp_test_schema_l {n} (p : Cp_test (n + 1)) : Delta0UnarySchema n where
  body := cp_test_formula_l p
  freeClosed := cp_test_closed_l p
  delta0 := cp_test_delta_l p

end YesMetaZFC.SetTheory.InnerModel
