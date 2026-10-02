import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds

/-! # 结构配对与固定长度列表的单调性 -/
namespace YesMetaZFC.Automation.ObjectCodeBounds
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofCode
open ObjectHorn
set_option autoImplicit false

theorem pair_mono {a b c d : Nat} (ha : a ≤ c) (hb : b ≤ d) :
    godel_pair_value a b ≤ godel_pair_value c d := by
  by_cases hShell : max a b < max c d
  · exact Nat.le_trans (Nat.le_of_lt (godel_pair_value_lt_max_succ_square a b))
      (Nat.le_trans (Nat.pow_le_pow_left hShell 2) (max_square_le_godel_pair_value c d))
  · have hEq : max a b = max c d := by omega
    by_cases hLeft : a < b
    · by_cases hRight : c < d
      · have hSame : b = d := by omega
        subst d
        simp only [godel_pair_value, hLeft, hRight, ite_true]
        omega
      · have hSame : b = c := by omega
        subst c
        simp only [godel_pair_value, hLeft, hRight, ite_true, ite_false]
        omega
    · by_cases hRight : c < d
      · omega
      · have hSame : a = c := by omega
        subst c
        simp only [godel_pair_value, hLeft, hRight, ite_false]
        omega

inductive CoordinateLe : List Nat → List Nat → Prop where
  | nil : CoordinateLe [] []
  | cons {a b : Nat} {as bs : List Nat} (head : a ≤ b) (tail : CoordinateLe as bs) :
      CoordinateLe (a :: as) (b :: bs)

theorem list_mono {left right : List Nat} (h : CoordinateLe left right) :
    listValue left ≤ listValue right := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hHead _ ih => exact Nat.add_le_add_right (pair_mono (Nat.le_refl 1) (pair_mono hHead ih)) 1

theorem node_mono (tag : Nat) {left right : List Nat} (h : CoordinateLe left right) :
    nodeValue tag left ≤ nodeValue tag right :=
  Nat.add_le_add_right (pair_mono (Nat.le_refl tag) (list_mono h)) 1

end YesMetaZFC.Automation.ObjectCodeBounds
