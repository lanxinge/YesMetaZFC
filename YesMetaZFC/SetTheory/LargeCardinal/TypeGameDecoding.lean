import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeQuery
import YesMetaZFC.Model.SetTheory.Internal.TypeGameRoot
import YesMetaZFC.Model.SetTheory.Internal.TypeGameMax
import YesMetaZFC.Model.SetTheory.Internal.TypeGameGraph
import YesMetaZFC.Model.SetTheory.Internal.SubtypeWitness

/-! # 类型游戏的一张图恢复

读取游戏中已经构造的原节点、最大序数查询及任意子类型见证。原排列完整保留，
从完整节点、空根和最大序数恢复同一棵树、同一末位及恰好一个新标签。
长度均为内部自然数；不增加标签顺序规则，也不预设实现层高。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tg_one_graph_recovery_l {ω e j k l n U D s t q₁ q₂ r δ S α a B ν u : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hn : M.mem n ω) (hek : M.mem e k)
    (hk : M.SuccessorOf k j) (hl : M.SuccessorOf l k) (hln : M.SuccessorOf n l)
    (nodeQuery : Tg_node_query_d I ω e n l U D s t k q₁) (maxQuery : Tg_max_query_d I ω l n U D q₂)
    (hB : V_d I α B) (hS : M.mem S B) (rS : Rd_entry_d e S r) (rα : Rd_entry_d k α r)
    (ga : Tg_graph_d I j a) (sa : Sg_set_d I e k r a) (rootS : M.mem e S)
    (qn : M.mem q₁ u) (qm : M.mem q₂ u) (witness : Ts_at_d hZF ω δ l r n U D u ν) :
        ∃ A c H r' g z π, V_d I ν A ∧ Smem_d I c A H ∧ Tt_realized_d I ω c A H n r' δ U D u ∧
          M.IsSetBijectionFromTo I π n n ∧
          (∀ i v x, Rd_entry_d v i π → M.mem i l → (Rd_entry_d i x r ↔ Rd_entry_d v x r')) ∧
          M.SuccessorOf ν α ∧ Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧
          Sg_set_d I e l r' g ∧ Tg_node_d I k S s t g ∧ Rd_entry_d j z g ∧
          ∀ p, M.mem p g ↔ M.mem p a ∨ KPair_d M p j z := by
  have on := hω.members_areOrdinals hZF n hn
  have ol := on.mem hln.predecessor_mem
  have hel := ol.transitive k hl.predecessor_mem e hek
  obtain ⟨A, c, H, r', f, h, π, hA, newModel, newType, ff, _, graph, orig, bij, perm⟩ := witness
  have moved i v x (vi : Rd_entry_d v i π) (hi : M.mem i l) : Rd_entry_d i x r ↔ Rd_entry_d v x r' := by
    have hv := bij.1.1.input_mem_of_pairMember vi
    have hin := on.transitive l hln.predecessor_mem i hi
    constructor
    · intro hx
      have fx := (orig i x hi).mp hx
      exact (graph v x).mp ((perm v hv x (ff.output_mem_of_pairMember fx)).mpr ⟨i, hin, vi, fx⟩)
    · intro hx
      obtain ⟨i', _, vi', fx⟩ := (perm v hv x (newType.tuple.bound_l hx).2).mp ((graph v x).mpr hx)
      exact (orig i x hi).mpr (bij.1.1.1.2 v i' i vi' vi ▸ fx)
  have seen i x (hi : M.mem i l) (hx : Rd_entry_d i x r) : ∃ v, M.mem v n ∧ Rd_entry_d v x r' := by
    obtain ⟨v, hv, vi⟩ := bij.2 i (on.transitive l hln.predecessor_mem i hi)
    exact ⟨v, hv, (moved i v x vi hi).mp hx⟩
  obtain ⟨T, _, newRoot⟩ := newType.tuple.2.1 e (on.transitive l hln.predecessor_mem e hel)
  obtain ⟨β, _, newLast⟩ := newType.tuple.2.1 l hln.predecessor_mem
  obtain ⟨g, _, set, node⟩ := (nodeQuery.2 c A H r' δ u T newModel (ZF.v_transitive_l I hZF hA) newType newRoot).mp qn
  have hα := v_ordinal_l I hB
  have ne : S ≠ α := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) α
    (ZF.v_ordinal_height_l hZF hB hα (eq ▸ hS))
  obtain ⟨eqT, eqβ, sub⟩ := tg_node_recover_l (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF))
    (KP.mem_irrefl_d (ZF.modelsKP hZF)) he hek hln (fn0_function_l (ZF.modelsKP hZF) newType.tuple)
    newRoot newLast set node hα rootS ne ga.1.1 (seen e S hel rS) (seen k α hl.predecessor_mem rα)
    (fun p hp => by
      obtain ⟨i, hi, _, hx⟩ := (sa p).mp hp
      exact seen i p (ol.transitive k hl.predecessor_mem i hi) hx)
  subst T β
  obtain ⟨z, hz, extension⟩ := tg_graph_extend_l (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF)) hk ga node.2.2.1 sub
  exact ⟨A, c, H, r', g, z, π, hA, newModel, newType, bij, moved,
    (maxQuery.2 ν A c H r' δ u α hA newModel newType newLast).mp qm, newRoot, newLast, set, node, hz, extension⟩

end YesMetaZFC.SetTheory.Internal
