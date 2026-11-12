import YesMetaZFC.Model.SetTheory.Demand.Graph
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.SubtypeWitness

/-! # 原 subtype 的同一次实现恢复两图与指定待回应值

任意排列的满射性把原元组中的树、高度、旧标签及待回应点搬入新元组。
先识别两个端点，再由同一原树的最小字母域读取两组范围，最后得到
两张图的精确单点追加；原实现高度由同一末位最大序数查询确定。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 完整原元组只规定标签的值集合；新实现允许原 subtype 中的任意有限排列。 -/
theorem td_two_graph_recovery_l
    {ω e j k h m l n U D s q₁ q₂ r δ S α a b p z U₁ U₂ B ν u : M.Domain}
    (he : ∀ x, ¬ M.mem x e)
    (hk : M.SuccessorOf k j) (hm : M.SuccessorOf m h) (hn : M.SuccessorOf n l)
    (included : M.MemberSubset m n)
    (nodeQuery : Td_node_query_d I ω e n l U D s k q₁)
    (maxQuery : Tg_max_query_d I ω l n U D q₂)
    (hB : V_d I α B) (hS : M.mem S B) (rootS : M.mem e S)
    (old : Tg_graph_d I m r) (rS : Rd_entry_d e S r) (rα : Rd_entry_d h α r)
    (fa : M.IsSetFunctionFromTo I a j U₁) (fb : M.IsSetFunctionFromTo I b j U₂)
    (alphabet : Td_alphabet_d S U₁ U₂) (disjoint : ∀ x, M.mem x U₁ → ¬ M.mem x U₂)
    (hz : M.mem z U₁) (pending : KPair_d M p j z)
    (values : ∀ q, (M.mem q a ∨ M.mem q b ∨ q = p) ↔
      ∃ i, M.mem i h ∧ i ≠ e ∧ Rd_entry_d i q r)
    (qn : M.mem q₁ u) (qm : M.mem q₂ u)
    (witness : Ts_at_d hZF ω δ m r n U D u ν) :
    ∃ A c H r' a' b' z' π, V_d I ν A ∧ Smem_d I c A H ∧
      Tt_realized_d I ω c A H n r' δ U D u ∧ M.IsSetBijectionFromTo I π n n ∧
      (∀ i v x, Rd_entry_d v i π → M.mem i m → (Rd_entry_d i x r ↔ Rd_entry_d v x r')) ∧
      M.SuccessorOf ν α ∧ Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧
      Td_labels_d I e l r' a' b' ∧ Tg_node_d I k S s a' b' ∧ Td_groups_d I ω e l r' a' b' ∧
      M.IsSetFunctionFromTo I a' k U₁ ∧ M.IsSetFunctionFromTo I b' k U₂ ∧
      M.MemberSubset a a' ∧ M.MemberSubset b b' ∧ Rd_entry_d j z a' ∧
      (∀ q, M.mem q a' ↔ M.mem q a ∨ KPair_d M q j z) ∧
      M.mem z' U₂ ∧ Rd_entry_d j z' b' ∧
      (∀ q, M.mem q b' ↔ M.mem q b ∨ KPair_d M q j z') := by
  obtain ⟨A,c,H,r',f,g,π,hA,newModel,newType,ff,_,graph,orig,bij,perm⟩ := witness
  have moved i v x (vi : Rd_entry_d v i π) (hi : M.mem i m) :
      Rd_entry_d i x r ↔ Rd_entry_d v x r' := by
    have hv := bij.1.1.input_mem_of_pairMember vi
    constructor
    · intro hx
      have fx := (orig i x hi).mp hx
      exact (graph v x).mp ((perm v hv x (ff.output_mem_of_pairMember fx)).mpr
        ⟨i,included i hi,vi,fx⟩)
    · intro hx
      obtain ⟨i',_,vi',fx⟩ := (perm v hv x (newType.tuple.bound_l hx).2).mp ((graph v x).mpr hx)
      exact (orig i x hi).mpr (bij.1.1.1.2 v i' i vi' vi ▸ fx)
  have seen i x (hi : M.mem i m) (hx : Rd_entry_d i x r) :
      ∃ v, M.mem v n ∧ Rd_entry_d v x r' := by
    obtain ⟨v,hv,vi⟩ := bij.2 i (included i hi)
    exact ⟨v,hv,(moved i v x vi hi).mp hx⟩
  have hem := (old.2 e).mpr ⟨S,rS⟩
  obtain ⟨T,_,newRoot⟩ := newType.tuple.2.1 e (included e hem)
  obtain ⟨β,_,newLast⟩ := newType.tuple.2.1 l hn.predecessor_mem
  obtain ⟨a',b',_,_,labels,node,groups⟩ :=
    (nodeQuery.2 c A H r' δ u T newModel (v_transitive_l I hA) newType newRoot).mp qn
  have hα := v_ordinal_l I hB
  have ne : S ≠ α := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) α
    (ZF.v_ordinal_height_l hZF hB hα (eq ▸ hS))
  have firstSeen := seen e S hem rS
  have lastSeen := seen h α hm.predecessor_mem rα
  obtain ⟨eqT,eqβ⟩ := td_node_endpoints_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    (KP.mem_irrefl_d (ZF.modelsKP hZF)) he hk hn (fn0_function_l (ZF.modelsKP hZF) newType.tuple)
    newRoot newLast labels node hα rootS ne firstSeen lastSeen
  subst T β
  have range := alphabet.node_l I hZF.1 node
  have fa' : M.IsSetFunctionFromTo I a' k U₁ := ⟨node.2.1.1,node.2.1.2,
    fun i hi => ((node.2.1.2 i).mp hi).imp fun x hx => ⟨range.1 i x hx,hx⟩⟩
  have fb' : M.IsSetFunctionFromTo I b' k U₂ := ⟨node.2.2.1.1,node.2.2.1.2,
    fun i hi => ((node.2.2.1.2 i).mp hi).imp fun x hx => ⟨range.2 i x hx,hx⟩⟩
  have allSeen q (hq : M.mem q a ∨ M.mem q b ∨ q = p) : ∃ v, M.mem v n ∧ Rd_entry_d v q r' := by
    obtain ⟨i,hi,_,point⟩ := (values q).mp hq
    exact seen i q ((hm i).mpr (Or.inl hi)) point
  obtain ⟨_,_,suba,subb,point,first,z',hz',last,second⟩ :=
    td_node_recover_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (KP.mem_irrefl_d (ZF.modelsKP hZF))
      he hk hn (fn0_function_l (ZF.modelsKP hZF) newType.tuple) newRoot newLast labels node
      fa fb fa' fb' disjoint hz pending hα rootS ne firstSeen lastSeen allSeen
  exact ⟨A,c,H,r',a',b',z',π,hA,newModel,newType,bij,moved,
    (maxQuery.2 ν A c H r' δ u α hA newModel newType newLast).mp qm,newRoot,newLast,labels,node,groups,
    fa',fb',suba,subb,point,first,hz',last,second⟩

end YesMetaZFC.SetTheory.Internal
