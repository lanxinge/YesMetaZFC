import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReplyQueries
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup

/-! # 完整回答直接读取开局已选定的原查询行

同一长度的元数、同一高度的常量域及同一元数的查询池由唯一性对齐。
实际成员性随后读取原表的三个码，保持回答 w 及其实现元组不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_query_catalog_d.reply_l
    {ω e δ X Γ S ν A k d q n m η Y c R r τ C V D w a b pending z U₁ U₂ : M.Domain}
    (table : Td_query_catalog_d hZFC ω e δ X Γ)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X)
    (low : Tg_low_d hZF ω e δ S ν) (hτδ : M.mem τ δ)
    (limit : M.IsLimitOrdinal τ) (base : V_d I τ C)
    (constants : ∀ x, M.mem x V ↔ M.mem x C ∨ x = τ) (hAV : M.mem A V)
    (rank : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R m r δ V D w)
    (record : Td_record_d I ω e k Y S a b pending ν d q n m r)
    (height : Tg_height_d ν η) (tree : Td_tree_d I ω A S)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) (pair : KPair_d M pending k z) :
    Tg_query_request_d hZF ω τ k e A ∧
    ∃ Du pn pm pp pb ph, Td_query_data_d Γ τ k e A C V Du D pn pm pp pb ph ∧
      Td_pending_query_d I ω A e m q V D k pp ∧ Tg_bound_query_d I ω e n m V D pb ∧
      Tg_height_query_d I ω n m V D ph ∧ M.mem pp w ∧ M.mem pb w ∧ M.mem ph w := by
  have hn := hw.transitive (ZF.modelsKP hZF) m record.finite n record.height_end.predecessor_mem
  have hq := hw.transitive (ZF.modelsKP hZF) n hn q record.pending_end.predecessor_mem
  have hd := hw.transitive (ZF.modelsKP hZF) q hq d record.labels_end.predecessor_mem
  have ok : M.IsOrdinal k := record.twice.elim (fun _ h => h.1.1.1)
  have hk := (ZF.ordinalAddition_left_eq_or_mem hZF I ok record.twice).elim
    (fun eq => eq.symm ▸ hd) (hw.transitive (ZF.modelsKP hZF) d hd k)
  have he := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  have request : Tg_query_request_d hZF ω τ k e A :=
    ⟨limit,hk,C,V,base,constants,(tt_constants_finite_l hZF hw he limit base constants).2,hAV⟩
  obtain ⟨key,row,keyCode,entry,packet⟩ := table.get_l hZFC hδ hwδ hX hτδ request
  obtain ⟨d',q',n',m',C',V',Du,D',pn,pm,pp,pb,ph,t,v,arity,rowCode,codes,tail,
    base',constants',_,pool,_,_,pq,bq,hq',_⟩ := packet
  have actual : Td_arity_d I k d q n m :=
    ⟨record.twice,record.labels_end,record.pending_end,record.height_end⟩
  obtain ⟨ed,eq,en,em⟩ := actual.unique_l hZF arity
  subst d' q' n' m'
  have ec := ZF.v_unique_l I hZF base base'
  subst C'
  have ev := hZF.1.eq_of_same_members V V' (fun x => (constants x).trans (constants' x).symm)
  subst V'
  have ep := type.pool.unique_l hZF.1 I pool
  subst D'
  exact ⟨request,Du,pn,pm,pp,pb,ph,⟨key,row,t,v,keyCode,entry,rowCode,codes,tail⟩,pq,bq,hq',
    low.demand_reply_members_l hZF hδ.1 rank model type record height tree alphabet chosen pair pq bq hq'⟩

end YesMetaZFC.SetTheory.LargeCardinal
