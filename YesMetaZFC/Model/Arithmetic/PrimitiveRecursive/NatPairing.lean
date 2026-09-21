import YesMetaZFC.Logic.Arithmetic.NatPairing
import YesMetaZFC.Model.Arithmetic.PA.Unpairing
import YesMetaZFC.Model.Arithmetic.Standard

/-! # 可计算配对与标准算术结构的一致性

任意模型的配对证明不依赖平方根；平方根只用于此处标准自然数的可执行解码。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false

theorem le_standard_m (m n : Nat) : le_l (ℳ := standard_m) m n ↔ m ≤ n := by
  change (∃ k, m + k = n) ↔ m ≤ n
  constructor
  · rintro ⟨k, rfl⟩; omega
  · intro h; exact ⟨n - m, Nat.add_sub_of_le h⟩

theorem lt_standard_m (m n : Nat) : lt_l (ℳ := standard_m) m n ↔ m < n := by
  change le_l (ℳ := standard_m) (m + 1) n ↔ m < n
  rw [le_standard_m]
  omega

theorem pair_standard_m (m n : Nat) : Pairing.value_l (ℳ := standard_m) m n = NatPairing.pair_l m n := by
  classical
  simp only [Pairing.value_l, lt_standard_m, NatPairing.pair_l]
  rfl

theorem unpair_pair_l (m n : Nat) : NatPairing.unpair_l (NatPairing.pair_l m n) = (m, n) := by
  have h : Pairing.value_l (ℳ := standard_m)
      (NatPairing.unpair_l (NatPairing.pair_l m n)).1 (NatPairing.unpair_l (NatPairing.pair_l m n)).2 =
      Pairing.value_l (ℳ := standard_m) m n := by
    rw [pair_standard_m, pair_standard_m, NatPairing.pair_unpair_l]
  have h' := PA.Pairing.injective_m pa_models_m _ _ m n h
  exact Prod.ext h'.1 h'.2

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
