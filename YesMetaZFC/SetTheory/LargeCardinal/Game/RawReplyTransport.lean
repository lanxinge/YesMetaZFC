import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.Model.SetTheory.Relations.Parity

/-! # 完整原回答的同图输运数据

所有字段都是实际代表池证明的结论。目标记录核消费同一份数据，原请求、
回答、数字坐标和档案标签因而不需要再次选择共同图或代表池。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_raw_reply_transport_d (I : kpair_convention_l.Interpretation M)
    (Ω X R j g t l : M.Domain) (nx : ∃ x, M.mem x X)
    (s : Fin 54 → M.Domain) (v : Fin 46 → M.Domain) (a : Fin 22 → M.Domain)
    (ε : Env (smdl_structure_l I (R := R) nx) 22) : Prop where
  values : ∀ i, Rd_entry_d (a i) (ε.bound i).val t
  truth : Formula.satisfies ε tg_reply0_m
  links : Tg_reply_link_d (fun x y => Rd_entry_d x y j) v (fun i => (ε.bound i).val)
  numbers : ∃ z, Rr_layer_d I Ω X R (ε.bound 0).val z
  omega : Rd_entry_d (s 16) (ε.bound 0).val g
  arity : Rd_entry_d (ε.bound 1).val (ε.bound 0).val R
  bound : ∀ x, Rd_entry_d x l R → Rd_entry_d x (ε.bound 3).val R
  label : ∀ y, Rd_entry_d (v 23) y j → Rd_entry_d (s 41) y g
  scalars : ∀ i : Fin 4, ∀ y, Rd_entry_d (v ([0,1,27,28].get i)) y j →
    Rd_entry_d (s ([16,17,23,24].get i)) y t

end YesMetaZFC.SetTheory.LargeCardinal
