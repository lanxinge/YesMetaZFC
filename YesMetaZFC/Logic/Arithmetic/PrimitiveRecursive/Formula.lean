import YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive.Program
import YesMetaZFC.Logic.Arithmetic.History
import YesMetaZFC.Logic.Arithmetic.Pairing

/-! # 程序图公式的结构编译

编译结果仅使用原 PA 签名；配对和有限历史都展开为已定义关系，不添加程序求值符号。
-/
namespace YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
open FirstOrder
set_option autoImplicit false

def comp_m (F G : History.binary_m) {Γ Δ : SortContext signature_m}
    (s t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj (G (s.weakenBound sort_m.num) (.bvar .here))
    (F (.bvar .here) (t.weakenBound sort_m.num)))

def pair_m (F G : History.binary_m) {Γ Δ : SortContext signature_m}
    (s t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (F ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (.conj (G ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here))
      (Pairing.graph_m (.bvar (.there .here)) (.bvar .here)
        ((t.weakenBound sort_m.num).weakenBound sort_m.num)))))

def iteration_m (G : History.binary_m) : History.quaternary_m := fun x i a d =>
  .existsE .num (.existsE .num (.conj
    (Pairing.graph_m ((i.weakenBound sort_m.num).weakenBound sort_m.num)
      ((a.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (.conj (Pairing.graph_m ((x.weakenBound sort_m.num).weakenBound sort_m.num)
      (.bvar (.there .here)) (.bvar .here))
      (G (.bvar .here) ((d.weakenBound sort_m.num).weakenBound sort_m.num)))))

def prec_m (F G : History.binary_m) {Γ Δ : SortContext signature_m}
    (s t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (Pairing.graph_m (.bvar (.there .here)) (.bvar .here)
      ((s.weakenBound sort_m.num).weakenBound sort_m.num))
    (History.graph_m F (iteration_m G) (.bvar (.there .here)) (.bvar .here)
      ((t.weakenBound sort_m.num).weakenBound sort_m.num))))

def graph_m : code_m → History.binary_m
  | .zero => fun _ t => .equal zero_m t
  | .succ => fun s t => .equal (succ_m s) t
  | .left => Pairing.left_m
  | .right => Pairing.right_m
  | .pair c d => pair_m (graph_m c) (graph_m d)
  | .comp c d => comp_m (graph_m c) (graph_m d)
  | .prec c d => prec_m (graph_m c) (graph_m d)

end YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive
