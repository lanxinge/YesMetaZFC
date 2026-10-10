import YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive.Program

/-! # 配对呈现的原始递归闭包与程序对应

闭包由零、后继、投影、配对、复合和原始递归生成，递归方程在 run_l 中显式给出。
这是自有 Lean/Std 呈现；不宣称已经提供 Mathlib Nat.Primrec 的导入桥。
-/
namespace YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false

inductive primitive_l : (Nat → Nat) → Prop where
  | zero : primitive_l (fun _ => 0)
  | succ : primitive_l Nat.succ
  | left : primitive_l (fun n => (NatPairing.unpair_l n).1)
  | right : primitive_l (fun n => (NatPairing.unpair_l n).2)
  | pair {f g} : primitive_l f → primitive_l g → primitive_l (fun n => NatPairing.pair_l (f n) (g n))
  | comp {f g} : primitive_l f → primitive_l g → primitive_l (fun n => f (g n))
  | prec {f g} : primitive_l f → primitive_l g →
      primitive_l (fun n => run_l f g (NatPairing.unpair_l n).1 (NatPairing.unpair_l n).2)

theorem primitive_m (c : code_m) : primitive_l (eval_l c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | pair c d hc hd => exact .pair hc hd
  | comp c d hc hd => exact primitive_l.comp (f := eval_l c) (g := eval_l d) hc hd
  | prec c d hc hd => exact .prec hc hd

theorem complete_m {f : Nat → Nat} (h : primitive_l f) : ∃ c, eval_l c = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair _ _ hf hg =>
      obtain ⟨c, rfl⟩ := hf
      obtain ⟨d, rfl⟩ := hg
      exact ⟨.pair c d, rfl⟩
  | comp _ _ hf hg =>
      obtain ⟨c, rfl⟩ := hf
      obtain ⟨d, rfl⟩ := hg
      exact ⟨.comp c d, rfl⟩
  | prec _ _ hf hg =>
      obtain ⟨c, rfl⟩ := hf
      obtain ⟨d, rfl⟩ := hg
      exact ⟨.prec c d, rfl⟩

end YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
