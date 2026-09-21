import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Totality
import YesMetaZFC.Model.Arithmetic.Numeral

/-! # 数码输入的任意模型表示

给定外部程序和自然数，实际求值的数码满足编译图；结合内部唯一性可排除非标准伪输出。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem numeral_m (c : code_m) (n : Nat) :
    relation_l c (Numeral.value_l (ℳ := ℳ) n) (Numeral.value_l (eval_l c n)) := by
  induction c generalizing n with
  | zero => rfl
  | succ => rfl
  | left =>
      refine ⟨Numeral.value_l (NatPairing.unpair_l n).2, ?_⟩
      change Pairing.value_l (Numeral.value_l (ℳ := ℳ) (NatPairing.unpair_l n).1)
        (Numeral.value_l (NatPairing.unpair_l n).2) = Numeral.value_l n
      rw [Numeral.pair_m hPA, NatPairing.pair_unpair_l]
  | right =>
      refine ⟨Numeral.value_l (NatPairing.unpair_l n).1, ?_⟩
      change Pairing.value_l (Numeral.value_l (ℳ := ℳ) (NatPairing.unpair_l n).1)
        (Numeral.value_l (NatPairing.unpair_l n).2) = Numeral.value_l n
      rw [Numeral.pair_m hPA, NatPairing.pair_unpair_l]
  | pair c d hc hd => exact ⟨_, _, hc n, hd n, Numeral.pair_m hPA _ _⟩
  | comp c d hc hd => exact ⟨_, hd n, hc (eval_l d n)⟩
  | prec c d hc hd =>
      let R := relation_l (ℳ := ℳ) c
      let S := fun a i v w => relation_l (ℳ := ℳ) d (Pairing.value_l a (Pairing.value_l i v)) w
      have hrun (a k : Nat) : PA.History.graph_l R S (Numeral.value_l a) (Numeral.value_l k)
          (Numeral.value_l (run_l (eval_l c) (eval_l d) a k)) := by
        induction k with
        | zero => exact PA.History.zero_m R S hPA (hc a)
        | succ k ih =>
            apply PA.History.step_m R S hPA ih
            change relation_l (ℳ := ℳ) d
              (Pairing.value_l (Numeral.value_l a)
                (Pairing.value_l (Numeral.value_l k) (Numeral.value_l (run_l (eval_l c) (eval_l d) a k)))) _
            rw [Numeral.pair_m hPA, Numeral.pair_m hPA]
            exact hd _
      refine ⟨Numeral.value_l (NatPairing.unpair_l n).1, Numeral.value_l (NatPairing.unpair_l n).2, ?_, ?_⟩
      · rw [Numeral.pair_m hPA, NatPairing.pair_unpair_l]
      · exact hrun _ _

theorem numeral_iff_m (c : code_m) (n : Nat) (y : num_l ℳ) :
    relation_l c (Numeral.value_l n) y ↔ Numeral.value_l (eval_l c n) = y := by
  constructor
  · exact fun h => unique_m hPA c (numeral_m hPA c n) h
  · rintro rfl; exact numeral_m hPA c n

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
