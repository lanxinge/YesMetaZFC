import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 类型游戏重置位置的实际完整类型

从含空根的实际树构造二元组 (S,ν) 及 V(ν+1) 中的完整类型，
三个实际查询同时为真。此处只构造节点与高度部分，不宣称弹性规则已经装配。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_reset_type_l {ω e l n ν η X δ U D S : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hn : M.mem n ω)
    (hl : M.SuccessorOf l e) (hln : M.SuccessorOf n l)
    (hX : V_d I η X) (hη : M.SuccessorOf η ν)
    (hS : M.mem S X) (root : M.mem e S) (point : M.mem δ X)
    (constants : M.MemberSubset U X) (heU : M.mem e U) (pool : Tt_pool_d I ω n U D) :
    ∃ c R r T q₀ q₁ q₂, Smem_d I c X R ∧ Tt_realized_d I ω c X R n r δ U D T ∧
      Rd_entry_d e S r ∧ Rd_entry_d l ν r ∧
      Tg_node_query_d I ω e n l U D e e e q₀ ∧ M.mem q₀ T ∧
      Tg_root_query_d I ω e n U D q₁ ∧ M.mem q₁ T ∧ Tg_max_query_d I ω l n U D q₂ ∧ M.mem q₂ T := by
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have ol := on.mem hln.predecessor_mem
  have oe := ol.mem hl.predecessor_mem
  have zero := tg_graph_empty_l I he
  have empty : M.IsSetFunctionFromTo I e e X := ⟨zero.1, zero.2, fun i hi => (he i hi).elim⟩
  obtain ⟨r₀, fn₀, _, first⟩ := tt_column_append_l hZF oe hl empty hS
  obtain ⟨r, fn, keep, last⟩ := tt_column_append_l hZF ol hln fn₀ (ZF.v_ordinal_mem_l I hZF hX hη.predecessor_mem)
  have rS := (keep e S hl.predecessor_mem).mpr first
  obtain ⟨c, R, model⟩ := smdl_membership_l I hZF ⟨δ, point⟩
  obtain ⟨T, truth, _⟩ := tt_truth_exists_l I hZF ω c n r δ D
  have type : Tt_realized_d I ω c X R n r δ U D T :=
    ⟨model.1, hn, fn0_of_function_l (ZF.modelsKP hZF) fn, point, constants, pool, truth⟩
  have set : Sg_set_d I e l r e := by
    intro x
    refine iff_of_false (he x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((hl i).mp hi).elim (he i) (fun eq => ne (hZF.1.eq_of_same_members i e eq))
  have trans := v_transitive_l I hX
  obtain ⟨q₀, hq₀, nodeRead⟩ := tt_node_query_l hZF hω hn hln.predecessor_mem hl.predecessor_mem pool heU heU heU
  obtain ⟨q₁, hq₁, rootRead⟩ := tt_root_query_l hZF hω he (on.transitive l hln.predecessor_mem e hl.predecessor_mem) pool
  obtain ⟨q₂, hq₂, maxRead⟩ := tt_max_query_l hZF hω hln.predecessor_mem pool
  refine ⟨c, R, r, T, q₀, q₁, q₂, model, type, rS, last, ⟨hq₀, nodeRead⟩, ?_, ⟨hq₁, rootRead⟩, ?_, ⟨hq₂, maxRead⟩, ?_⟩
  · exact (nodeRead c X R r δ T S model trans type rS).mpr
      ⟨e, constants e heU, set, (tg_node_empty_l I hZF.1 he).mpr root⟩
  · exact (rootRead c X R r δ T S model trans type rS).mpr root
  · exact (maxRead η X c R r δ T ν hX model type last).mpr hη

end YesMetaZFC.SetTheory.Internal
