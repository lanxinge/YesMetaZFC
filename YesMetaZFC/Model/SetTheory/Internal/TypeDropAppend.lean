import YesMetaZFC.Model.SetTheory.Internal.TypeDrop
import YesMetaZFC.Model.SetTheory.Internal.TypeColumn

/-! # 实际增加末位与 dcp 互逆

由一个完整前缀类型和一个源内对象自动构造更长元组及完整类型。
重新删除末位所得集合字面等于原类型，为弹性前缀提供真实实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_realized_d.append_l {ω c X R n m s δ U D P t x : M.Domain}
    (hω : M.IsOmega ω) (succ : M.SuccessorOf m n) (type : Tt_realized_d I ω c X R n s δ U D t)
    (hx : M.mem x X) (pool : Tt_pool_d I ω m U P) :
    ∃ r u, Tt_realized_d I ω c X R m r δ U P u ∧ Td_dcp_d I n m D u t ∧
      (∀ i y, M.mem i n → (Rd_entry_d i y r ↔ Rd_entry_d i y s)) ∧ Rd_entry_d n x r := by
  have on := hω.members_areOrdinals hZF n type.finite
  obtain ⟨m', hm', hmω⟩ := hω.1.2 n type.finite
  have hm : M.mem m ω := (hm'.eq hZF.1 succ) ▸ hmω
  obtain ⟨r, fn, kept, last⟩ := tt_column_append_l hZF on succ (fn0_function_l (ZF.modelsKP hZF) type.tuple) hx
  obtain ⟨u, truth, _⟩ := tt_truth_exists_l I hZF ω c m r δ P
  have full : Tt_realized_d I ω c X R m r δ U P u :=
    ⟨type.model, hm, fn0_of_function_l (ZF.modelsKP hZF) fn, type.point, type.constants, pool, truth⟩
  obtain ⟨s', t', cut, drop, small⟩ := full.dcp_l hZF hω succ type.pool
  have eqs : s' = s := Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := I) hZF.1 cut.1
    (fn0_function_l (ZF.modelsKP hZF) type.tuple).1.1 (fun i y => (cut.2 i y).trans
      ⟨fun h => (kept i y h.1).mp h.2, fun h =>
        ⟨(type.tuple.bound_l h).1, (kept i y (type.tuple.bound_l h).1).mpr h⟩⟩)
  subst s'
  have eqt := hZF.1.eq_of_same_members t' t (fun p => (small.truth p).trans (type.truth p).symm)
  exact ⟨r, u, full, eqt ▸ drop, kept, last⟩

end YesMetaZFC.SetTheory.Internal
