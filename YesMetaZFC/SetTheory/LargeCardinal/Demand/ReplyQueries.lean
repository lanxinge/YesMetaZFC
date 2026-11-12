import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 同一完整回答中的三条实际查询

从 w 的实际查询池编译 pending、严格秩界与高度公式。pending 保留
固定第一字母表 A；低点证书给出 δ<ν 和 S∈Vν，三次后继给出高度真值。
三个成员证据都读取同一个完整类型，不构造第二个回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 读取已经取定的三条查询；尤其适用于原 Q 表中的同一组码。 -/
theorem Tg_low_d.demand_reply_members_l
    {ω e δ S ν A k d q n m η Y c R r V D w a b pending z U₁ U₂ pp pb ph : M.Domain}
    (low : Tg_low_d hZF ω e δ S ν) (hδ : M.IsOrdinal δ)
    (rank : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R m r δ V D w)
    (record : Td_record_d I ω e k Y S a b pending ν d q n m r)
    (height : Tg_height_d ν η) (tree : Td_tree_d I ω A S)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) (pair : KPair_d M pending k z)
    (pendingQuery : Td_pending_query_d I ω A e m q V D k pp)
    (boundQuery : Tg_bound_query_d I ω e n m V D pb)
    (heightQuery : Tg_height_query_d I ω n m V D ph) :
    M.mem pp w ∧ M.mem pb w ∧ M.mem ph w := by
  have fullPending : Td_pending_d I ω A k S pending :=
    ⟨tree,z,pair,(alphabet.1 z).mp chosen⟩
  obtain ⟨hδν,Z,hZ,hS⟩ := low.read_l hZF hδ
  have bound : Tg_bound_d I δ S ν := ⟨v_ordinal_l I hZ,hδν,Z,hZ,hS⟩
  exact ⟨(pendingQuery.2 η Y c R r δ w S pending rank model type record.root record.pending).mpr fullPending,
    (boundQuery.2 η Y c R r δ w S ν rank model type record.root record.height).mpr bound,
    (heightQuery.2 η Y c R r δ w ν rank model type record.height).mpr height⟩

/-- 所需常量只有 ω、A、k 的实际成员性；弹性语言和一步证书由调用端保留。 -/
theorem Tg_low_d.demand_reply_queries_l
    {ω e δ S ν A k d q n m η Y c R r V D w a b pending z U₁ U₂ : M.Domain}
    (low : Tg_low_d hZF ω e δ S ν) (hw : M.IsOmega ω) (hδ : M.IsOrdinal δ)
    (rank : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R m r δ V D w)
    (record : Td_record_d I ω e k Y S a b pending ν d q n m r)
    (height : Tg_height_d ν η) (tree : Td_tree_d I ω A S)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) (pair : KPair_d M pending k z)
    (hwV : M.mem ω V) (hAV : M.mem A V) (hkV : M.mem k V) :
    ∃ pp pb ph,
      Td_pending_query_d I ω A e m q V D k pp ∧
      Tg_bound_query_d I ω e n m V D pb ∧ Tg_height_query_d I ω n m V D ph ∧
      M.mem pp w ∧ M.mem pb w ∧ M.mem ph w := by
  have he := (type.tuple.bound_l record.root).1
  have hq := (type.tuple.bound_l record.pending).1
  have hn := (type.tuple.bound_l record.height).1
  obtain ⟨pp,pendingQuery⟩ := tt_demand_pending_query_l hZF hw type.finite he hq type.pool hwV hAV hkV
  obtain ⟨pb,boundQuery⟩ := tt_bound_query_l hZF hw he hn hwV type.pool
  obtain ⟨ph,heightQuery⟩ := tt_height_query_l hZF hw hn type.pool
  exact ⟨pp,pb,ph,pendingQuery,boundQuery,heightQuery,
    low.demand_reply_members_l hZF hδ rank model type record height tree alphabet chosen pair
      pendingQuery boundQuery heightQuery⟩

end YesMetaZFC.SetTheory.LargeCardinal
