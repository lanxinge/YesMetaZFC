import YesMetaZFC.Model.SetTheory.Demand.Graph
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax

/-! # 任意回答排列的根与两新增槽

原字母的真实出现给出树非序数。pending 的首坐标等于旧图定义域，
故不能等于任何旧标签；高度也不能等于原树或标签。排列的单射性
随后迫使旧前缀恰与旧前缀对应，两个新增槽允许交换，不要求奇偶保持。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 实际出现过字母的树含非空节点，其真实标签对排除树为序数。 -/
theorem Td_letter_d.not_ordinal_l (hirr : ∀ x, ¬ M.mem x x)
    {side : Bool} {S z : M.Domain} (letter : Td_letter_d side S z) : ¬ M.IsOrdinal S := by
  obtain ⟨q,i,p,x,a,b,t,hq,⟨u,pair,hu⟩,_⟩ := letter
  exact fun ordinal => pair.not_transitive_l M hirr ((ordinal.mem hq).mem hu).transitive

variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hirr : ∀ x, ¬ M.mem x x)
local notation "I" => kpair_interpretation_l M hE hP
include hirr

/-- π 从新位置指向原位置；只约束两新增槽的集合，不预设其各自固定。 -/
theorem td_reply_endpoints_l
    {e k q l m r s a b S T p z β π : M.Domain}
    (empty : ∀ x, ¬ M.mem x e) (heq : M.mem e q)
    (sl : M.SuccessorOf l q) (sm : M.SuccessorOf m l)
    (old : M.IsSetFunction I r) (oldRoot : Rd_entry_d e S r)
    (labels : Td_labels_d I e q r a b) (fa : Tg_graph_d I k a) (fb : Tg_graph_d I k b)
    (rootS : M.mem e S) (rootT : M.mem e T) (notOrdinal : ¬ M.IsOrdinal S)
    (newRoot : Rd_entry_d e T s) (newPending : Rd_entry_d q p s) (newHeight : Rd_entry_d l β s)
    (pending : KPair_d M p k z) (ordinal : M.IsOrdinal β)
    (bij : M.IsSetBijectionFromTo I π m m)
    (moved : ∀ i v x, Rd_entry_d v i π → M.mem i q → (Rd_entry_d i x r ↔ Rd_entry_d v x s)) :
    ∃ i j, Rd_entry_d q i π ∧ Rd_entry_d l j π ∧
      ((i = q ∧ j = l) ∨ (i = l ∧ j = q)) ∧ Rd_entry_d e e π ∧ T = S ∧
      ∀ v t, Rd_entry_d v t π → (M.mem v q ↔ M.mem t q) := by
  classical
  have split v (hv : M.mem v m) : M.mem v q ∨ v = q ∨ v = l := by
    rcases (sm v).mp hv with hv | eq
    · exact ((sl v).mp hv).elim Or.inl (fun eq => Or.inr (Or.inl (hE.eq_of_same_members v q eq)))
    · exact Or.inr (Or.inr (hE.eq_of_same_members v l eq))
  have outside v (hv : v = q ∨ v = l) : ¬ M.mem v q := by
    rcases hv with eq | eq
    · exact fun h => hirr q (Eq.mp (congrArg (fun w => M.mem w q) eq) h)
    · exact fun h => hirr l ((sl l).mpr (Or.inl
        (Eq.mp (congrArg (fun w => M.mem w q) eq) h)))
  have ql : q ≠ l := fun eq => hirr l (eq ▸ sl.predecessor_mem)
  have pendingOut i (point : Rd_entry_d q i π) : ¬ M.mem i q := by
    intro hi
    have value := (moved i q p point hi).mpr newPending
    by_cases ie : i = e
    · have eq := old.2 e p S (ie ▸ value) oldRoot
      exact KPair_d.empty_not_mem_l empty pending (eq.symm ▸ rootS)
    · rcases (labels p).mpr ⟨i,hi,ie,value⟩ with ha | hb
      · exact hirr k ((fa.2 k).mpr ⟨z,p,pending,ha⟩)
      · exact hirr k ((fb.2 k).mpr ⟨z,p,pending,hb⟩)
  have heightOut i (point : Rd_entry_d l i π) : ¬ M.mem i q := by
    intro hi
    have value := (moved i l β point hi).mpr newHeight
    by_cases ie : i = e
    · exact notOrdinal (old.2 e β S (ie ▸ value) oldRoot ▸ ordinal)
    · rcases (labels β).mpr ⟨i,hi,ie,value⟩ with ha | hb
      · obtain ⟨u,v,pair⟩ := fa.1.1 β ha
        exact pair.not_transitive_l M hirr ordinal.transitive
      · obtain ⟨u,v,pair⟩ := fb.1.1 β hb
        exact pair.not_transitive_l M hirr ordinal.transitive
  have qm : M.mem q m := (sm q).mpr (Or.inl sl.predecessor_mem)
  obtain ⟨i,hi,qi⟩ := bij.1.1.2.2 q qm
  obtain ⟨j,hj,lj⟩ := bij.1.1.2.2 l sm.predecessor_mem
  have si : i = q ∨ i = l := (split i hi).elim (fun hi => (pendingOut i qi hi).elim) id
  have sj : j = q ∨ j = l := (split j hj).elim (fun hj => (heightOut j lj hj).elim) id
  have order : (i = q ∧ j = l) ∨ (i = l ∧ j = q) := by
    rcases si with ei | ei <;> rcases sj with ej | ej
    · exact (ql (bij.1.2 q l q (ei ▸ qi) (ej ▸ lj))).elim
    · exact Or.inl ⟨ei,ej⟩
    · exact Or.inr ⟨ei,ej⟩
    · exact (ql (bij.1.2 q l l (ei ▸ qi) (ej ▸ lj))).elim
  have cover t (ht : t = q ∨ t = l) : ∃ v, (v = q ∨ v = l) ∧ Rd_entry_d v t π := by
    rcases order with ⟨ei,ej⟩ | ⟨ei,ej⟩ <;> rcases ht with et | et
    · exact ⟨q,Or.inl rfl,Eq.mpr (congrArg (fun y => Rd_entry_d q y π) et) (ei ▸ qi)⟩
    · exact ⟨l,Or.inr rfl,Eq.mpr (congrArg (fun y => Rd_entry_d l y π) et) (ej ▸ lj)⟩
    · exact ⟨l,Or.inr rfl,Eq.mpr (congrArg (fun y => Rd_entry_d l y π) et) (ej ▸ lj)⟩
    · exact ⟨q,Or.inl rfl,Eq.mpr (congrArg (fun y => Rd_entry_d q y π) et) (ei ▸ qi)⟩
  have keep v t (point : Rd_entry_d v t π) : M.mem v q ↔ M.mem t q := by
    constructor
    · intro hv
      rcases split t (bij.1.1.output_mem_of_pairMember point) with ht | ht
      · exact ht
      · obtain ⟨w,hw,wt⟩ := cover t ht
        exact (outside w hw (bij.1.2 v w t point wt ▸ hv)).elim
    · intro ht
      rcases split v (bij.1.1.input_mem_of_pairMember point) with hv | eq | eq
      · exact hv
      · exact (pendingOut t (eq ▸ point) ht).elim
      · exact (heightOut t (eq ▸ point) ht).elim
  have em : M.mem e m := (sm e).mpr (Or.inl ((sl e).mpr (Or.inl heq)))
  obtain ⟨v,_,ev⟩ := bij.1.1.2.2 e em
  have hv := (keep e v ev).mp heq
  have value := (moved v e T ev hv).mpr newRoot
  have ve : v = e := by
    apply Classical.byContradiction
    intro ne
    rcases (labels T).mpr ⟨v,hv,ne,value⟩ with ha | hb
    · obtain ⟨x,y,pair⟩ := fa.1.1 T ha
      exact KPair_d.empty_not_mem_l empty pair rootT
    · obtain ⟨x,y,pair⟩ := fb.1.1 T hb
      exact KPair_d.empty_not_mem_l empty pair rootT
  have eqT : T = S := old.2 e T S (ve ▸ value) oldRoot
  exact ⟨i,j,qi,lj,order,ve ▸ ev,eqT,keep⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意回答与原两图记录之间的实际排列

旧前缀仍按原两组顺序保存，回答本身不作任何改写。限制原排列到旧前缀，
再在两个新增槽上取恒等，得到回答与恢复记录之间的完整双射。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 恢复记录可有不同坐标次序；输出双射明确连接同一个原回答元组。 -/
theorem td_reply_record_l
    {ω e k d q l m X S a b r s p β π : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hm : M.mem m ω)
    (add : M.IsOrdinalAddition I d k k) (sq : M.SuccessorOf q d)
    (sl : M.SuccessorOf l q) (sm : M.SuccessorOf m l)
    (old : Tg_graph_d I q r) (root : Rd_entry_d e S r)
    (groups : Td_groups_d I ω e q r a b)
    (actual : Fn0_d m X s) (pending : Rd_entry_d q p s) (height : Rd_entry_d l β s)
    (perm : M.IsSetBijectionFromTo I π m m)
    (moved : ∀ i j x, Rd_entry_d j i π → M.mem i q →
      (Rd_entry_d i x r ↔ Rd_entry_d j x s))
    (preserved : ∀ i j, Rd_entry_d i j π → (M.mem i q ↔ M.mem j q)) :
    ∃ r₀ ψ, Td_record_d I ω e k X S a b p β d q l m r₀ ∧
      M.IsSetBijectionFromTo I ψ m m ∧
      (∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x s ↔ Rd_entry_d j x r₀)) := by
  have qm : M.MemberSubset q m := fun i hi => (sm i).mpr (Or.inl ((sl i).mpr (Or.inl hi)))
  have hl := hw.transitive (ZF.modelsKP hZF) m hm l sm.predecessor_mem
  have hq := hw.transitive (ZF.modelsKP hZF) l hl q sl.predecessor_mem
  have oldFn : M.IsSetFunctionFromTo I r q X := ⟨old.1,old.2,fun i hi => by
    obtain ⟨x,ix⟩ := (old.2 i).mp hi
    obtain ⟨j,_,ji⟩ := perm.2 i (qm i hi)
    exact ⟨x,(actual.bound_l ((moved i j x ji hi).mp ix)).2,ix⟩⟩
  obtain ⟨l',m',r₀,record,kept⟩ := td_record_append_l (ZF.modelsKP hZF) hw empty hq add sq
    (fn0_of_function_l (ZF.modelsKP hZF) oldFn) root groups
    (actual.bound_l pending).2 (actual.bound_l height).2
  have el := record.pending_end.eq hZF.1 sl
  subst l'
  have em := record.height_end.eq hZF.1 sm
  subst m'
  obtain ⟨ρ,cut⟩ := ZF.exists_restriction hZF I π q
  have base := cut.isSetFunctionFromTo perm.1.1 qm
  have small : M.IsSetFunctionFromTo I ρ q q := ⟨base.1,base.2.1,fun i hi => by
    obtain ⟨j,_,ij⟩ := base.2.2 i hi
    exact ⟨j,(preserved i j ((cut.2 i j).mp ij).2).mp hi,ij⟩⟩
  have bij : M.IsSetBijectionFromTo I ρ q q := ⟨⟨small,fun i j x ix jx =>
    perm.1.2 i j x ((cut.2 i x).mp ix).2 ((cut.2 j x).mp jx).2⟩,fun j hj => by
      obtain ⟨i,_,ij⟩ := perm.2 j (qm j hj)
      have hi := (preserved i j ij).mpr hj
      exact ⟨i,hi,(cut.2 i j).mpr ⟨hi,ij⟩⟩⟩
  obtain ⟨ψ,bψ,entries⟩ := tp_extend_l hZF qm bij
  have sf := (fn0_function_l (ZF.modelsKP hZF) actual).1
  have rf := (fn0_function_l (ZF.modelsKP hZF) record.tuple).1
  refine ⟨r₀,ψ,record,bψ,fun i j x ij => ?_⟩
  rcases (entries i j).mp ij with ij | ⟨hi,out,eq⟩
  · have hj := small.output_mem_of_pairMember ij
    exact (moved j i x ((cut.2 i j).mp ij).2 hj).symm.trans (kept j x hj).symm
  · subst j
    rcases (sm i).mp hi with hi | eq
    · rcases (sl i).mp hi with hi | eq
      · exact (out hi).elim
      · have eq := hZF.1.eq_of_same_members i q eq
        subst i
        exact ⟨fun hx => (sf.2 q x p hx pending).symm ▸ record.pending,
          fun hx => (rf.2 q x p hx record.pending).symm ▸ pending⟩
    · have eq := hZF.1.eq_of_same_members i l eq
      subst i
      exact ⟨fun hx => (sf.2 l x β hx height).symm ▸ record.height,
        fun hx => (rf.2 l x β hx record.height).symm ▸ height⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原回答类型的两图恢复与严格下降

先识别原树和两个新增槽，再恢复原两图记录及其与实际回答的排列。
回答 w 的实现元组和完整类型保持不变，恢复记录只通过已构造双射相连。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原字母真实出现即可处理零轮，无需假定旧节点具有正长度。 -/
theorem td_reply_restore_l
    {ω A e k d q l m X S T a b r s p β π ζ : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hm : M.mem m ω)
    (add : M.IsOrdinalAddition I d k k) (sq : M.SuccessorOf q d)
    (sl : M.SuccessorOf l q) (sm : M.SuccessorOf m l)
    (old : Tg_graph_d I q r) (root : Rd_entry_d e S r)
    (groups : Td_groups_d I ω e q r a b) (fa : Tg_graph_d I k a) (fb : Tg_graph_d I k b)
    (rootS : M.mem e S) (letter : Td_letter_d false S ζ)
    (actual : Fn0_d m X s) (newRoot : Rd_entry_d e T s)
    (newPending : Rd_entry_d q p s) (newHeight : Rd_entry_d l β s)
    (pending : Td_pending_d I ω A k T p) (ordinal : M.IsOrdinal β)
    (perm : M.IsSetBijectionFromTo I π m m)
    (moved : ∀ i j x, Rd_entry_d j i π → M.mem i q →
      (Rd_entry_d i x r ↔ Rd_entry_d j x s)) :
    T = S ∧ ∃ r₀ ψ, Td_record_d I ω e k X S a b p β d q l m r₀ ∧
      M.IsSetBijectionFromTo I ψ m m ∧
      (∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x s ↔ Rd_entry_d j x r₀)) := by
  have hirr := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have rootT := pending.root_l hZF hw empty
  obtain ⟨_,z,cp,_⟩ := pending
  obtain ⟨_,_,_,_,_,_,eq,keep⟩ := td_reply_endpoints_l hZF.1
    (KP.exists_pair (ZF.modelsKP hZF)) hirr empty ((old.2 e).mpr ⟨S,root⟩)
    sl sm old.1 root groups.cover_l fa fb rootS rootT (letter.not_ordinal_l hirr)
    newRoot newPending newHeight cp ordinal perm moved
  exact ⟨eq,td_reply_record_l hZF hw empty hm add sq sl sm old root groups actual
    newPending newHeight perm moved keep⟩

/-- 原 dcp、任意原回答和原三查询直接给出同一 w 的可继续记录。 -/
theorem td_reply_descend_l
    {ω A k e d₀ q l m κ τ U D V W B C v w b₀ a₀ z₀ η Y c R r δ α
      q₁ q₂ q₃ S a b ζ : M.Domain} {σ : Fin 7 → M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (prog : Ts_program_d hZF ω q b₀ σ a₀ z₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R q r δ U D v) (oldHeight : M.SuccessorOf η α)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hm : M.mem m ω)
    (hB : V_d I κ B) (oldConstants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hC : V_d I τ C) (constants : ∀ x, M.mem x V ↔ M.mem x C ∨ x = τ)
    (pool : Tt_pool_d I ω m V W) (sub : M.MemberSubset w W)
    (subtype : Ts_subtype_d ω q κ τ m U w b₀ σ z₀ v)
    (add : M.IsOrdinalAddition I d₀ k k) (sq : M.SuccessorOf q d₀)
    (sl : M.SuccessorOf l q) (sm : M.SuccessorOf m l)
    (root : Rd_entry_d e S r) (groups : Td_groups_d I ω e q r a b)
    (fa : Tg_graph_d I k a) (fb : Tg_graph_d I k b)
    (rootS : M.mem e S) (letter : Td_letter_d false S ζ)
    (pendingQuery : Td_pending_query_d I ω A e m q V W k q₁)
    (boundQuery : Tg_bound_query_d I ω e l m V W q₂)
    (heightQuery : Tg_height_query_d I ω l m V W q₃)
    (qp : M.mem q₁ w) (qb : M.mem q₂ w) (qh : M.mem q₃ w) :
    ∃ ν X c' H s p β r₀ ψ, M.mem ν η ∧ V_d I ν X ∧ Smem_d I c' X H ∧
      Tt_realized_d I ω c' X H m s δ V W w ∧
      Rd_entry_d e S s ∧ Rd_entry_d q p s ∧ Rd_entry_d l β s ∧
      Td_pending_d I ω A k S p ∧ Tg_bound_d I δ S β ∧ Tg_height_d β ν ∧ M.mem β α ∧
      Td_record_d I ω e k X S a b p β d₀ q l m r₀ ∧
      M.IsSetBijectionFromTo I ψ m m ∧
      (∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x s ↔ Rd_entry_d j x r₀)) := by
  have qm : M.MemberSubset q m := fun i hi => (sm i).mpr (Or.inl ((sl i).mpr (Or.inl hi)))
  obtain ⟨ν,X,c',H,s,T,p,β,π,hν,hX,lower,actual,rT,rp,rβ,pending,bound,height,lt,bij,moved⟩ :=
    td_reply_read_l hZF hw prog hY model type oldHeight hκ hτ hm hB oldConstants hC
      constants pool sub subtype (qm e (type.tuple.bound_l root).1)
      ((sm q).mpr (Or.inl sl.predecessor_mem)) sm.predecessor_mem pendingQuery boundQuery heightQuery qp qb qh
  have fn := fn0_function_l (ZF.modelsKP hZF) type.tuple
  obtain ⟨eq,r₀,ψ,record,perm,points⟩ := td_reply_restore_l hZF hw empty hm add sq sl sm
    ⟨fn.1,fn.2.1⟩ root groups fa fb rootS letter actual.tuple rT rp rβ pending bound.1 bij moved
  subst T
  exact ⟨ν,X,c',H,s,p,β,r₀,ψ,hν,hX,lower,actual,rT,rp,rβ,pending,bound,height,lt,record,perm,points⟩

end YesMetaZFC.SetTheory.Internal
