import YesMetaZFC.SetTheory.LargeCardinal.Game.Tracked
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Realize
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.Model.SetTheory.Demand.ReplyRestore

/-! # 实际双图记录的无界继续类型

原回答 w 仍由原元组 r 实现，恢复后的记录 s₀ 通过实际排列与 r 对接。
只在记录的旧高度槽插入第二图标签，再将高度移到新末槽。插槽给出的
子类型见证最后沿该排列传回 r，不重选或重排回答类型 w。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem woodin_demand_continue_l
    {ω δ e k d₀ q₀ l n τ U D w η Y c R r s₀ ψ S a b p β s a' b' k' p' χ : M.Domain}
    (hd : Woodin_d I δ) (hw : M.IsOmega ω) (empty : ∀ y, ¬ M.mem y e)
    (hτ : M.IsOrdinal τ) (hτχ : M.MemberSubset τ χ) (hχ : M.mem χ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n r δ U D w)
    (record : Td_record_d I ω e k Y S a b p β d₀ q₀ l n s₀)
    (perm : M.IsSetBijectionFromTo I ψ n n)
    (points : ∀ i j y, Rd_entry_d i j ψ → (Rd_entry_d i y r ↔ Rd_entry_d j y s₀))
    (bound : Tg_bound_d I δ S β) (height : Tg_height_d β η)
    (next : M.SuccessorOf k' k) (node : Tg_node_d I k' S s a' b')
    (appendA : ∀ y, M.mem y a' ↔ M.mem y a ∨ y = p)
    (appendB : ∀ y, M.mem y b' ↔ M.mem y b ∨ y = p') :
    ∃ μ A d H κ B V E P m r' u, ∃ q : Ee_queries_d M,
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.mem χ κ ∧ M.mem κ δ ∧
      Ee_language_d hZF ω κ n B V E q ∧ M.SuccessorOf m n ∧
      M.mem k' ω ∧ M.IsOrdinalAddition I l k' k' ∧
      Tt_realized_d I ω d A H m r' δ V P u ∧ Tg_elastic_d I n m E q u ∧
      Rd_entry_d e S r' ∧ Rd_entry_d q₀ p r' ∧ Rd_entry_d l p' r' ∧ Rd_entry_d n β r' ∧
      Td_groups_d I ω e n r' a' b' ∧ Tg_node_d I k' S s a' b' ∧
      (∀ i y, M.mem i l → (Rd_entry_d i y s₀ ↔ Rd_entry_d i y r')) ∧
      Tx_exceeds_d hZF ω δ τ n U D w κ m V P u := by
  obtain ⟨Z,hZ,hS⟩ := bound.2.2
  obtain ⟨ω',Z',μ,A,d,H,hw',hZ',hμ,hA,lower,all⟩ := woodin_game_type_l hZFC hd bound.1 bound.2.1
  have eqω := hZF.1.eq_of_same_members ω' ω (fun i => ⟨hw'.2 ω hw.1 i,hw.2 ω' hw'.1 i⟩)
  subst ω'
  have eqZ := ZF.v_unique_l I hZF hZ' hZ
  subst Z'
  obtain ⟨left,right⟩ := node.aux_labels_rank_l hZF hZ hS
  have fn := fn0_function_l (ZF.modelsKP hZF) record.tuple
  have on := hw.members_areOrdinals (ZF.modelsKP hZF) n record.finite
  have ol := on.mem record.height_end.predecessor_mem
  have oq := ol.mem record.pending_end.predecessor_mem
  have hl := hw.transitive (ZF.modelsKP hZF) n record.finite l record.height_end.predecessor_mem
  have hq := hw.transitive (ZF.modelsKP hZF) l hl q₀ record.pending_end.predecessor_mem
  have hd₀ := hw.transitive (ZF.modelsKP hZF) q₀ hq d₀ record.labels_end.predecessor_mem
  have ok : M.IsOrdinal k := record.twice.elim (fun _ h => h.1.1.1)
  have hk : M.mem k ω := (ZF.ordinalAddition_left_eq_or_mem hZF I ok record.twice).elim
    (fun eq => eq.symm ▸ hd₀) (hw.transitive (ZF.modelsKP hZF) d₀ hd₀ k)
  obtain ⟨k₀,next₀,hk₀⟩ := hw.1.2 k hk
  have hk' : M.mem k' ω := next₀.eq hZF.1 next ▸ hk₀
  obtain ⟨v,hv,_⟩ := ZF.ordinalAddition_existsUnique hZF I k' ok
  have step := Structure.natural_add_left_successor hZF I hw hk next hk record.twice hv
  have eq := step.eq hZF.1 record.labels_end
  have twice : M.IsOrdinalAddition I l k' k' :=
    (ZF.ordinalAddition_successor_iff hZF I ok next).mpr ⟨q₀,eq ▸ hv,record.pending_end⟩
  -- 旧高度以前的每个值均为原树、两组旧标签或已指定 pending。
  obtain ⟨r₁,cut⟩ := ZF.exists_restriction hZF I s₀ l
  have fr₁ := cut.isSetFunctionFromTo fn (on.transitive l record.height_end.predecessor_mem)
  have small : M.IsSetFunctionFromTo I r₁ l Z := ⟨fr₁.1,fr₁.2.1,fun i hi => by
    obtain ⟨y,_,iy⟩ := fr₁.2.2 i hi
    have ry := ((cut.2 i y).mp iy).2
    refine ⟨y,?_,iy⟩
    by_cases ie : i = e
    · exact (fn.1.2 e y S (ie ▸ ry) record.root).symm ▸ hS
    · rcases (record.values y).mpr ⟨i,hi,ie,ry⟩ with ha | hb | hp
      · exact left y ((appendA y).mpr (Or.inl ha))
      · exact right y ((appendB y).mpr (Or.inl hb))
      · exact left y ((appendA y).mpr (Or.inr hp))⟩
  have fq₁ := fn0_of_function_l (ZF.modelsKP hZF) small
  have pending : Rd_entry_d q₀ p r₁ := (cut.2 q₀ p).mpr ⟨record.pending_end.predecessor_mem,record.pending⟩
  obtain ⟨r₀,cut₀⟩ := ZF.exists_restriction hZF I r₁ q₀
  have fq₀ := fn0_of_function_l (ZF.modelsKP hZF)
    (cut₀.isSetFunctionFromTo small (ol.transitive q₀ record.pending_end.predecessor_mem))
  have same₀ i y (hi : M.mem i q₀) : Rd_entry_d i y s₀ ↔ Rd_entry_d i y r₀ := by
    have hil := ol.transitive q₀ record.pending_end.predecessor_mem i hi
    exact ⟨fun iy => (cut₀.2 i y).mpr ⟨hi,(cut.2 i y).mpr ⟨hil,iy⟩⟩,
      fun iy => ((cut.2 i y).mp ((cut₀.2 i y).mp iy).2).2⟩
  have groups₀ : Td_groups_d I ω e q₀ r₀ a b := by
    constructor
    · intro y
      exact (record.groups.1 y).trans
        ⟨fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(same₀ i y hi).mp iy⟩,
          fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(same₀ i y hi).mpr iy⟩⟩
    · intro y
      exact (record.groups.2 y).trans
        ⟨fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(same₀ i y hi).mp iy⟩,
          fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(same₀ i y hi).mpr iy⟩⟩
  have added₁ i y : Rd_entry_d i y r₁ ↔ Rd_entry_d i y r₀ ∨ i = q₀ ∧ y = p := by
    constructor
    · intro iy
      rcases (record.pending_end i).mp (small.input_mem_of_pairMember iy) with hi | eq
      · exact Or.inl ((cut₀.2 i y).mpr ⟨hi,iy⟩)
      · have eq := hZF.1.eq_of_same_members i q₀ eq
        exact Or.inr ⟨eq,small.1.2 q₀ y p (eq ▸ iy) pending⟩
    · rintro (iy | ⟨rfl,rfl⟩)
      · exact ((cut₀.2 i y).mp iy).2
      · exact pending
  -- 唯一新增的是第二图的末标签；旧 pending 继续占据原槽。
  obtain ⟨v₀,fv,added₂⟩ := td_tuple_append_l (ZF.modelsKP hZF) ol record.height_end fq₁
    (right p' ((appendB p').mpr (Or.inr rfl)))
  have odd : ¬ Gm_even_d I ω q₀ := fun even =>
    ((gm_even_successor_l I hZF hw hd₀ record.labels_end).mp even) ⟨k,hk,record.twice⟩
  have groups := groups₀.append_pair_l hZF hw empty hq record.pending_end record.height_end
    fq₀ fq₁ odd added₁ added₂ appendA appendB
  obtain ⟨m,κ,B,V,E,P,r',u,_,_,q,hm,above,hκ,language,full,_,_,elastic,keep,moved,_,_⟩ :=
    all n v₀ record.finite fv χ hχ
  have agree i y (hi : M.mem i l) : Rd_entry_d i y s₀ ↔ Rd_entry_d i y r' := by
    have hin := on.transitive l record.height_end.predecessor_mem i hi
    constructor
    · intro iy
      exact (keep i y hin).mpr ((added₂ i y).mpr (Or.inl ((cut.2 i y).mpr ⟨hi,iy⟩)))
    · intro iy
      rcases (added₂ i y).mp ((keep i y hin).mp iy) with iy | ⟨eq,_⟩
      · exact ((cut.2 i y).mp iy).2
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (eq ▸ hi)).elim
  have inserted : Rd_entry_d l p' r' := (keep l p' record.height_end.predecessor_mem).mpr
    ((added₂ l p').mpr (Or.inr ⟨rfl,rfl⟩))
  have groups' : Td_groups_d I ω e n r' a' b' := by
    constructor
    · intro y
      exact (groups.1 y).trans
        ⟨fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(keep i y hi).mpr iy⟩,
          fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(keep i y hi).mp iy⟩⟩
    · intro y
      exact (groups.2 y).trans
        ⟨fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(keep i y hi).mpr iy⟩,
          fun ⟨i,hi,ne,par,iy⟩ => ⟨i,hi,ne,par,(keep i y hi).mp iy⟩⟩
  obtain ⟨μ',γ,succ,mid,top⟩ := height
  have eqμ := succ.eq hZF.1 hμ
  subst μ'
  refine ⟨μ,A,d,H,κ,B,V,E,P,m,r',u,q,hμ,hA,lower,above,hκ,language,hm,hk',twice,
    full,elastic,(agree e S (ol.transitive q₀ record.pending_end.predecessor_mem e record.root_before)).mp record.root,
    (agree q₀ p record.pending_end.predecessor_mem).mp record.pending,inserted,moved,groups',node,agree,?_⟩
  exact ⟨ordinal_down_l (ZF.modelsKP hZF) hτ language.limit.1 hτχ above,
    fun i hi => (hm i).mpr (Or.inl hi),η,Y,c,R,r,hY,model,type,μ,γ,mid,top.predecessor_mem,
    (ts_at_insert_l hZF hw record.height_end hm hA lower full ⟨fn.1,fn.2.1⟩
      agree record.height inserted moved).input_permute_l hZF hw
        (fun i hi => (hm i).mpr (Or.inl hi)) perm points⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一反策略的实际回复驱动双图继续类型

挑战从当前记录的 pending 查询读取；第二字母只能取同一 τ 的实际回复。
两张图的精确追加与新节点均由原游戏控制导出，再交给武丁类型工厂。
恢复记录与原回答元组通过同一实际排列相连；继续工厂最后仍超过原 w。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_counter_continue_l
    {ω δ A e k d₀ q₀ l n θ U D w η Y c R r s₀ ψ S a b p β χ
      U₁ U₂ x V F L G J B W O τ C h : M.Domain}
    (hd : Woodin_d I δ) (hw : M.IsOmega ω) (empty : ∀ y, ¬ M.mem y e)
    (hθ : M.IsOrdinal θ) (hθχ : M.MemberSubset θ χ) (hχ : M.mem χ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n r δ U D w)
    (record : Td_record_d I ω e k Y S a b p β d₀ q₀ l n s₀)
    (perm : M.IsSetBijectionFromTo I ψ n n)
    (points : ∀ i j y, Rd_entry_d i j ψ → (Rd_entry_d i y r ↔ Rd_entry_d j y s₀))
    (bound : Tg_bound_d I δ S β) (height : Tg_height_d β η)
    (alphabet : Td_alphabet_d S U₁ U₂) (pending : Td_pending_d I ω A k S p)
    (game : Dg_counter_d hZF ω U₁ U₂ x S V F L G J B W O)
    (control : Cg_control_d I true ω e V F L G J τ C)
    (hk : M.mem k ω) (fh : Fn0_d d₀ V h) (hh : M.mem h C)
    (fa : Fn0_d k U₁ a) (fb : Fn0_d k U₂ b) (weave : Dg_weave_d I ω h a b) :
    ∃ z k' n' h₁ h₂ z' s' a' b' p', KPair_d M p k z ∧ M.mem z U₁ ∧
      M.SuccessorOf k' k ∧ M.mem k' ω ∧ M.mem n' ω ∧
      M.IsOrdinalAddition I n' k' k' ∧ Fn0_d n' V h₂ ∧ M.mem h₂ C ∧
      Fseq_end_d I ω h₁ h z ∧ Fseq_end_d I ω h₂ h₁ z' ∧ Rd_entry_d h₁ z' τ ∧ M.mem z' U₂ ∧
      M.IsRestrictionOf I s' x k' ∧ Tg_node_d I k' S s' a' b' ∧
      Fn0_d k' U₁ a' ∧ Fn0_d k' U₂ b' ∧ Dg_weave_d I ω h₂ a' b' ∧
      KPair_d M p' k z' ∧
      (∀ y, M.mem y a' ↔ M.mem y a ∨ y = p) ∧
      (∀ y, M.mem y b' ↔ M.mem y b ∨ y = p') ∧
      ∃ μ Z d H κ K V' E P m r' u, ∃ q : Ee_queries_d M,
        M.SuccessorOf μ β ∧ V_d I μ Z ∧ Smem_d I d Z H ∧ M.mem χ κ ∧ M.mem κ δ ∧
        Ee_language_d hZF ω κ n K V' E q ∧ M.SuccessorOf m n ∧
        M.mem k' ω ∧ M.IsOrdinalAddition I l k' k' ∧
        Tt_realized_d I ω d Z H m r' δ V' P u ∧ Tg_elastic_d I n m E q u ∧
        Rd_entry_d e S r' ∧ Rd_entry_d q₀ p r' ∧ Rd_entry_d l p' r' ∧ Rd_entry_d n β r' ∧
        Td_groups_d I ω e n r' a' b' ∧ Tg_node_d I k' S s' a' b' ∧
        (∀ i y, M.mem i l → (Rd_entry_d i y s₀ ↔ Rd_entry_d i y r')) ∧
        Tx_exceeds_d hZF ω δ θ n U D w κ m V' P u := by
  obtain ⟨_,z,cp,letter⟩ := pending
  have hz := (alphabet.1 z).mpr letter
  have hl := hw.transitive (ZF.modelsKP hZF) n record.finite l record.height_end.predecessor_mem
  have hq := hw.transitive (ZF.modelsKP hZF) l hl q₀ record.pending_end.predecessor_mem
  have hd₀ := hw.transitive (ZF.modelsKP hZF) q₀ hq d₀ record.labels_end.predecessor_mem
  obtain ⟨k',n',h₁,h₂,z',s',a',b',next,hk',hn',twice,f₂,h₂C,end₁,end₂,reply,hz',rest,node,
    fa',fb',weave',first,second⟩ :=
      game.reply_extend_l hZF hw control hk hd₀ record.twice fh hh fa fb weave hz
  obtain ⟨p',cp'⟩ := (I).total k z'
  have appendA y : M.mem y a' ↔ M.mem y a ∨ y = p :=
    (first y).trans (or_congr Iff.rfl ⟨fun cy => (I).unique cy cp,fun eq => eq.symm ▸ cp⟩)
  have appendB y : M.mem y b' ↔ M.mem y b ∨ y = p' :=
    (second y).trans (or_congr Iff.rfl ⟨fun cy => (I).unique cy cp',fun eq => eq.symm ▸ cp'⟩)
  exact ⟨z,k',n',h₁,h₂,z',s',a',b',p',cp,hz,next,hk',hn',twice,f₂,h₂C,end₁,end₂,reply,hz',
    rest,node,fa',fb',weave',cp',appendA,appendB,
    woodin_demand_continue_l hZFC hd hw empty hθ hθχ hχ hY model type record perm points bound height
      next node appendA appendB⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原回答的实际下降与同一反策略继续

原 subtype 的排列首先给出同一回答 w 的较低实现，再恢复两图记录及
实际排列。原反策略只在该记录读出的挑战上回复；新弹性类型仍超过 w。
树根和树非序数性由原树中真实出现的第一字母产生，零轮不另加根假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_generic_reply_l
    {ω δ A e k d₀ q l m κ τ U D V W B C v w b₀ a₀ z₀ η Y c R r α
      q₁ q₂ q₃ S a b ζ χ U₁ U₂ x V₀ F₀ L₀ G₀ J₀ B₀ W₀ O₀ σ₀ C₀ h : M.Domain}
    {σ : Fin 7 → M.Domain}
    (hd : Woodin_d I δ) (hw : M.IsOmega ω) (empty : ∀ y, ¬ M.mem y e)
    (prog : Ts_program_d hZF ω q b₀ σ a₀ z₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R q r δ U D v) (oldHeight : M.SuccessorOf η α)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hm : M.mem m ω)
    (hB : V_d I κ B) (oldConstants : ∀ y, M.mem y U ↔ M.mem y B ∨ y = κ)
    (hC : V_d I τ C) (constants : ∀ y, M.mem y V ↔ M.mem y C ∨ y = τ)
    (pool : Tt_pool_d I ω m V W) (sub : M.MemberSubset w W)
    (subtype : Ts_subtype_d ω q κ τ m U w b₀ σ z₀ v)
    (add : M.IsOrdinalAddition I d₀ k k) (sq : M.SuccessorOf q d₀)
    (sl : M.SuccessorOf l q) (sm : M.SuccessorOf m l)
    (root : Rd_entry_d e S r) (groups : Td_groups_d I ω e q r a b)
    (tree : Td_tree_d I ω A S) (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem ζ U₁)
    (pendingQuery : Td_pending_query_d I ω A e m q V W k q₁)
    (boundQuery : Tg_bound_query_d I ω e l m V W q₂)
    (heightQuery : Tg_height_query_d I ω l m V W q₃)
    (qp : M.mem q₁ w) (qb : M.mem q₂ w) (qh : M.mem q₃ w)
    (hτχ : M.MemberSubset τ χ) (hχ : M.mem χ δ)
    (game : Dg_counter_d hZF ω U₁ U₂ x S V₀ F₀ L₀ G₀ J₀ B₀ W₀ O₀)
    (control : Cg_control_d I true ω e V₀ F₀ L₀ G₀ J₀ σ₀ C₀)
    (hk : M.mem k ω) (fh : Fn0_d d₀ V₀ h) (hh : M.mem h C₀)
    (fa : Fn0_d k U₁ a) (fb : Fn0_d k U₂ b) (weave : Dg_weave_d I ω h a b) :
    ∃ ν X c' H s p β r₀ ψ, M.mem ν η ∧ V_d I ν X ∧ Smem_d I c' X H ∧
      Tt_realized_d I ω c' X H m s δ V W w ∧
      Rd_entry_d e S s ∧ Rd_entry_d q p s ∧ Rd_entry_d l β s ∧
      Td_pending_d I ω A k S p ∧ Tg_bound_d I δ S β ∧ Tg_height_d β ν ∧ M.mem β α ∧
      Td_record_d I ω e k X S a b p β d₀ q l m r₀ ∧
      M.IsSetBijectionFromTo I ψ m m ∧
      (∀ i j y, Rd_entry_d i j ψ → (Rd_entry_d i y s ↔ Rd_entry_d j y r₀)) ∧
      ∃ z k' n' h₁ h₂ z' s' a' b' p', KPair_d M p k z ∧ M.mem z U₁ ∧
        M.SuccessorOf k' k ∧ M.mem k' ω ∧ M.mem n' ω ∧
        M.IsOrdinalAddition I n' k' k' ∧ Fn0_d n' V₀ h₂ ∧ M.mem h₂ C₀ ∧
        Fseq_end_d I ω h₁ h z ∧ Fseq_end_d I ω h₂ h₁ z' ∧
        Rd_entry_d h₁ z' σ₀ ∧ M.mem z' U₂ ∧
        M.IsRestrictionOf I s' x k' ∧ Tg_node_d I k' S s' a' b' ∧
        Fn0_d k' U₁ a' ∧ Fn0_d k' U₂ b' ∧ Dg_weave_d I ω h₂ a' b' ∧
        KPair_d M p' k z' ∧
        (∀ y, M.mem y a' ↔ M.mem y a ∨ y = p) ∧
        (∀ y, M.mem y b' ↔ M.mem y b ∨ y = p') ∧
        ∃ μ Z c'' H' κ' K V' E P n r' u, ∃ qe : Ee_queries_d M,
          M.SuccessorOf μ β ∧ V_d I μ Z ∧ Smem_d I c'' Z H' ∧ M.mem χ κ' ∧ M.mem κ' δ ∧
          Ee_language_d hZF ω κ' m K V' E qe ∧ M.SuccessorOf n m ∧
          M.mem k' ω ∧ M.IsOrdinalAddition I l k' k' ∧
          Tt_realized_d I ω c'' Z H' n r' δ V' P u ∧ Tg_elastic_d I m n E qe u ∧
          Rd_entry_d e S r' ∧ Rd_entry_d q p r' ∧ Rd_entry_d l p' r' ∧ Rd_entry_d m β r' ∧
          Td_groups_d I ω e m r' a' b' ∧ Tg_node_d I k' S s' a' b' ∧
          (∀ i y, M.mem i l → (Rd_entry_d i y r₀ ↔ Rd_entry_d i y r')) ∧
          Tx_exceeds_d hZF ω δ τ m V W w κ' n V' P u := by
  have letter := (alphabet.1 ζ).mp chosen
  obtain ⟨p₀,cp₀⟩ := (I).total k ζ
  have start : Td_pending_d I ω A k S p₀ := ⟨tree,ζ,cp₀,letter⟩
  have rootS := start.root_l hZF hw empty
  have fna := fn0_function_l (ZF.modelsKP hZF) fa
  have fnb := fn0_function_l (ZF.modelsKP hZF) fb
  obtain ⟨ν,X,c',H,s,p,β,r₀,ψ,hν,hX,lower,actual,rs,rp,rβ,pending,bound,height,lt,record,perm,points⟩ :=
    td_reply_descend_l hZF hw empty prog hY model type oldHeight hκ hτ hm hB oldConstants
      hC constants pool sub subtype add sq sl sm root groups ⟨fna.1,fna.2.1⟩ ⟨fnb.1,fnb.2.1⟩
      rootS letter pendingQuery boundQuery heightQuery qp qb qh
  refine ⟨ν,X,c',H,s,p,β,r₀,ψ,hν,hX,lower,actual,rs,rp,rβ,pending,bound,height,lt,record,perm,points,?_⟩
  exact td_counter_continue_l hZFC hd hw empty hτ.1 hτχ hχ hX lower actual record perm points
    bound height alphabet pending game control hk fh hh fa fb weave

end YesMetaZFC.SetTheory.LargeCardinal
