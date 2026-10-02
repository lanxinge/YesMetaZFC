import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotationDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeMonotone

/-! # quotation 转换的输入中间码可由最终输出界定 -/
namespace YesMetaZFC.Automation.ObjectProjectQuotation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation ProofCode
open ObjectHorn ObjectCodeBounds
set_option autoImplicit false

private theorem cons_tail (head tail : Nat) :
    tail < godel_pair_value 1 (godel_pair_value head tail) + 1 := by
  have h1 := right_le_godel_pair_value head tail
  have h2 := right_le_godel_pair_value 1 (godel_pair_value head tail)
  omega

private theorem atom_le (tag : Nat) (children : List Tree) :
    treeValue (.node tag children) ≤ treeValue (atom tag children) := by
  by_cases h2 : tag = 2
  · subst tag
    simp only [atom, ite_true, treeValue_node, List.map_cons]
    exact Nat.add_le_add_right (pair_mono (Nat.le_refl 2)
      (Nat.le_of_lt (cons_tail _ _))) 1
  · by_cases h11 : tag = 11
    · subst tag
      simp only [atom, h2, ite_false, ite_true, treeValue_node, List.map_cons]
      let rest := listValue (children.map treeValue)
      let next := godel_pair_value 1 (godel_pair_value 4 rest) + 1
      have hTail : rest < next := cons_tail 4 rest
      have hFour : 4 ≤ godel_pair_value 4 rest := left_le_godel_pair_value _ _
      have hLarge : 16 ≤ next := by
        have h := max_square_le_godel_pair_value 1 (godel_pair_value 4 rest)
        have hSquare : 4 ^ 2 ≤ max 1 (godel_pair_value 4 rest) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        change 16 ≤ godel_pair_value 1 (godel_pair_value 4 rest) + 1
        omega
      change godel_pair_value 11 rest + 1 ≤ godel_pair_value 2 next + 1
      exact Nat.le_trans (godel_pair_value_lt_max_succ_square 11 rest)
        (Nat.le_trans (Nat.pow_le_pow_left (by omega : max 11 rest + 1 ≤ max 2 next) 2)
          (Nat.le_trans (max_square_le_godel_pair_value 2 next) (Nat.le_succ _)))
    · simp [atom, h2, h11]

theorem run_le (input : Tree) : ∀ output, run input = some output → treeValue input ≤ treeValue output := by
  fun_induction run input
  case case1 | case2 => intro output h; cases h; exact Nat.le_refl _
  case case3 | case4 | case12 => intro output h; cases h; exact atom_le _ _
  case case5 body ih | case10 body ih | case11 body ih =>
    intro output h
    obtain ⟨decoded, hBody, hOut⟩ := Option.bind_eq_some_iff.mp h
    cases hOut
    exact node_mono _ (.cons (ih decoded hBody) .nil)
  case case6 left right ihLeft ihRight | case7 left right ihLeft ihRight
     | case8 left right ihLeft ihRight | case9 left right ihLeft ihRight =>
    intro output h
    obtain ⟨a, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRest
    cases hOut
    exact node_mono _ (.cons (ihLeft a hLeft) (.cons (ihRight b hRight) .nil))
  case case13 => intro output h; cases h

end YesMetaZFC.Automation.ObjectProjectQuotation
