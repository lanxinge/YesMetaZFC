import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 有限结构码的统一数值上界 -/
namespace YesMetaZFC.Automation.ObjectCodeBounds
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofCode
open ObjectHorn
set_option autoImplicit false

theorem pair_succ_bound (base left right : Nat) (hBase : 2 ≤ base) (hLeft : left ≤ base) (hRight : right ≤ base) :
    godel_pair_value left right + 1 ≤ base ^ 4 := by
  have hSquare : base + 1 ≤ base ^ 2 := by
    have h := Nat.mul_le_mul_left base hBase
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    omega
  calc
    godel_pair_value left right + 1 ≤ (max left right + 1) ^ 2 :=
      godel_pair_value_lt_max_succ_square left right
    _ ≤ (base + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ (base ^ 2) ^ 2 := Nat.pow_le_pow_left hSquare 2
    _ = base ^ 4 := (Nat.pow_mul base 2 2).symm

theorem list_bound (base : Nat) (hBase : 2 ≤ base) (values : List Nat)
    (hValues : ∀ value, value ∈ values → value ≤ base) :
    listValue values ≤ base ^ (16 ^ values.length) := by
  induction values with
  | nil =>
    change 1 ≤ base ^ (16 ^ 0)
    exact Nat.one_le_pow _ _ (by omega)
  | cons head tail ih =>
    have hTail := ih (fun value h => hValues value (List.mem_cons_of_mem head h))
    let bound := base ^ (16 ^ tail.length)
    have hBaseBound : base ≤ bound := Nat.le_pow (Nat.pow_pos (by decide))
    have hBound : 2 ≤ bound := Nat.le_trans hBase hBaseBound
    have hPair := pair_succ_bound bound head (listValue tail) hBound
      (Nat.le_trans (hValues head List.mem_cons_self) hBaseBound) hTail
    have hNext := pair_succ_bound (bound ^ 4) 1 (godel_pair_value head (listValue tail))
      (Nat.le_trans hBound (Nat.le_pow (by decide)))
      (Nat.one_le_pow _ _ (by omega)) (by omega)
    change godel_pair_value 1 (godel_pair_value head (listValue tail)) + 1 ≤ base ^ (16 ^ (tail.length + 1))
    calc
      _ ≤ (bound ^ 4) ^ 4 := hNext
      _ = base ^ (16 ^ (tail.length + 1)) := by
        rw [← Nat.pow_mul]
        change (base ^ (16 ^ tail.length)) ^ 16 = base ^ (16 ^ (tail.length + 1))
        rw [← Nat.pow_mul, Nat.pow_succ]

theorem list_field_le (values : List Nat) (value : Nat) (h : value ∈ values) : value ≤ listValue values := by
  induction values with
  | nil => cases h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (left_le_godel_pair_value _ _)
        (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _))
    · exact Nat.le_trans (ih h) (Nat.le_trans (right_le_godel_pair_value _ _)
        (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _)))

theorem node_field_le (tag : Nat) (values : List Nat) (value : Nat) (h : value ∈ values) :
    value ≤ nodeValue tag values :=
  Nat.le_trans (list_field_le values value h) (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _))

end YesMetaZFC.Automation.ObjectCodeBounds
