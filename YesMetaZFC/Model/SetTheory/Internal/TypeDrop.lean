import YesMetaZFC.Model.SetTheory.Internal.TypeDropRead

/-! # 删除末位后仍为原前缀的完整类型

先用分离构造裸查询集合的语法逆像，再证明其由实际限制元组实现。
dcp 保留原秩层、指定点与常量域；它与下降一个秩层的 minus 分开。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_realized_d.project_l {ω c X R n m U D P r δ t : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (sub : M.MemberSubset n m)
    (type : Tt_realized_d I ω c X R m r δ U P t) (pool : Tt_pool_d I ω n U D) :
    ∃ s u, M.IsRestrictionOf I s r n ∧ Td_project_d I n m D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨s, cut⟩ := ZF.exists_restriction hZF I r n
  have fs := fn0_of_function_l (ZF.modelsKP hZF) (cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) type.tuple) sub)
  have kept i x (hx : Rd_entry_d i x s) : Rd_entry_d i x r := ((cut.2 i x).mp hx).2
  obtain ⟨u, project⟩ := td_project_exists_l I hZF n m D t
  refine ⟨s, u, cut, project, ⟨type.model, hn, fs, type.point, type.constants, pool, fun p => ?_⟩⟩
  refine (project p).trans (and_congr_right fun hp => ⟨?_, ?_⟩)
  · rintro ⟨q, code, hq⟩
    exact (code.read_l hZF hω hn type fs kept pool hp).mpr ((type.truth q).mp hq).2
  · intro truth
    obtain ⟨q, hq, code⟩ := td_query_exists_l I hZF sub pool type.pool hp
    exact ⟨q, code, (type.truth q).mpr ⟨hq, (code.read_l hZF hω hn type fs kept pool hp).mp truth⟩⟩

/-- 原 5.8 的 dcp：内部后继元数的末位删除，结果字面唯一。 -/
theorem Tt_realized_d.dcp_l {ω c X R n m U D P r δ t : M.Domain}
    (hω : M.IsOmega ω) (succ : M.SuccessorOf m n)
    (type : Tt_realized_d I ω c X R m r δ U P t) (pool : Tt_pool_d I ω n U D) :
    ∃ s u, M.IsRestrictionOf I s r n ∧ Td_dcp_d I n m D t u ∧ Tt_realized_d I ω c X R n s δ U D u := by
  obtain ⟨s, u, cut, project, small⟩ := type.project_l hZF hω
    (hω.transitive hZF m type.finite n succ.predecessor_mem) (fun i hi => (succ i).mpr (Or.inl hi)) pool
  exact ⟨s, u, cut, ⟨succ, project⟩, small⟩

end YesMetaZFC.SetTheory.Internal
