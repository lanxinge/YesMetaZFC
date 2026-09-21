import YesMetaZFC.Logic.Arithmetic.NatPairing

/-! # 七构造原始递归程序

数据语法和可执行求值独立于公式编译；没有无界搜索。递归步的输入为配对 x,(i,y)。
-/
namespace YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false

inductive code_m where
  | zero | succ | left | right
  | pair (c d : code_m) | comp (c d : code_m) | prec (c d : code_m)
  deriving DecidableEq, Repr

def run_l (f g : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => f x
  | n + 1 => g (NatPairing.pair_l x (NatPairing.pair_l n (run_l f g x n)))

def eval_l : code_m → Nat → Nat
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (NatPairing.unpair_l n).1
  | .right => fun n => (NatPairing.unpair_l n).2
  | .pair c d => fun n => NatPairing.pair_l (eval_l c n) (eval_l d n)
  | .comp c d => fun n => eval_l c (eval_l d n)
  | .prec c d => fun n => run_l (eval_l c) (eval_l d) (NatPairing.unpair_l n).1 (NatPairing.unpair_l n).2

end YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
