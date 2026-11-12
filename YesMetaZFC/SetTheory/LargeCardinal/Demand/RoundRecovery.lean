import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity
import YesMetaZFC.Model.SetTheory.Demand.Recovery
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Types.Embedding

/-! # 非重置回合的原类型与同高度双图恢复

两个阶段严格分开：原当前模型用真实 exceeds 推出最大序数查询；第一
原后继则从 u subtype j(oldw) 读出同一 u 的实现。前一 exceeds 不被当成
后一模型中的真值，两阶段只传递实际查询码在同一类型中的成员证据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已搬入第一后继的旧轮和同次 subtype 实际产生原候选的实现。 -/
theorem td_round_realize_l (ρ : Env M 62) (old : Formula.satisfies ρ td_round0_m)
    (η : Env M 17) (subtype : Formula.satisfies η tg_subtype0_m)
    (same : ∀ i : Fin 5, η.bound ([0,1,2,5,9].get i) = ρ.bound ([19,9,0,2,4].get i))
    (program : Formula.satisfies (η.reindex
      (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m)
    (limit : M.IsLimitOrdinal (η.bound 3)) (finite : M.mem (η.bound 4) (η.bound 0)) :
    ∃ B V D, V_d I (η.bound 3) B ∧
      (∀ x, M.mem x V ↔ M.mem x B ∨ x = η.bound 3) ∧
      Tt_pool_d I (η.bound 0) (η.bound 4) V D ∧
      Ts_real_d hZF (η.bound 0) (ρ.bound 21) (η.bound 1) (ρ.bound 10)
        (η.bound 4) V D (η.bound 6) (ρ.bound 5) := by
  have hKP := ZF.modelsKP hZF
  obtain ⟨seed,round⟩ := (Formula.satisfies_conj_iff ..).mp old
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  have omega : M.IsOmega (η.bound 0) := (same 0).symm ▸
    (Formula.satisfies_isOmega_iff ..).mp seed.1
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at round
  obtain ⟨_,_,_,_,rank,model,language,type,_⟩ := round
  have rank := (v_sigma_sat_l hKP ..).mp rank
  have model := (smem_sat_l I ..).mp model
  have type := (tt_realized_sat_l I hKP ..).mp type
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have oldLimit : M.IsLimitOrdinal (ρ.bound 0) :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1
  have oldRank : V_d I (ρ.bound 0) (ρ.bound 1) := (v_sigma_sat_l hKP ..).mp language.2.2.1
  have actual : Tt_realized_d I (η.bound 0) (ρ.bound 7) (ρ.bound 6) (ρ.bound 8)
      (η.bound 1) (ρ.bound 10) (ρ.bound 21) (η.bound 5) (ρ.bound 3) (η.bound 9) := by
    rw [show η.bound 0 = ρ.bound 19 from same 0,
      show η.bound 1 = ρ.bound 9 from same 1,
      show η.bound 5 = ρ.bound 2 from same 3,
      show η.bound 9 = ρ.bound 4 from same 4]
    exact type
  let σ : Fin 7 → Term 17 := fun i =>
    [.bound 10,.bound 11,.bound 12,.bound 13,.bound 14,.bound 15,.bound 16].get i
  obtain ⟨below,_,q,query,member⟩ :=
    (ts_subtype_sat_l hKP η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) σ).mp subtype
  obtain ⟨a,compiled⟩ := (ts_numeric0_sat_l hZF _).mp program
  have slots : (fun i => (σ i).eval η) =
      (fun i => [η.bound 10,η.bound 11,η.bound 12,η.bound 13,η.bound 14,η.bound 15,η.bound 16].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have compiled : Ts_program_d hZF (η.bound 0) (η.bound 1) (η.bound 7)
      (fun i => (σ i).eval η) a (η.bound 8) := by
    rw [slots]
    exact compiled
  have below' : M.mem (η.bound 3) (ρ.bound 0) := same 2 ▸ below
  obtain ⟨B,V,base,_,constants⟩ := tt_constants_exists_l hZF oldRank oldLimit below'
  obtain ⟨D,pool⟩ := tt_pool_exists_l I hZF omega (η.bound 4) V
  have oldLimit' : M.IsLimitOrdinal (η.bound 2) := (same 2).symm ▸ oldLimit
  exact ⟨B,V,D,base,constants,pool,
    ((query.read_l hZF omega compiled rank model actual oldLimit'
      limit below finite base constants pool).mp member).2⟩

/-- 原继续规则中的历史事件、旧元数和两个常量域自动对齐，再读出当前 max。 -/
theorem Td_continue_d.max_l
    {ω e a c δ stage history ℓ κ k n U D u v₀ v₁ ℓ₀ j κ₀ u₀ τ w
      d₀ q₀ h m B₀ U₀ D₀ ph q B V E Bq pm g₀ g₁ : M.Domain}
    (rule : Td_continue_d hZF ω e a c δ stage history ℓ κ k n U D u)
    (hw : M.IsOmega ω) (oc : M.IsOrdinal c) (fh : M.IsSetFunction I history)
    (request : Tg_event_d I c ℓ e history v₀) (move : Td_move_d v₀ ℓ₀ j κ₀ u₀)
    (answer : Tg_event_d I c ℓ a history v₁) (pair : KPair_d M v₁ τ w)
    (arity : Td_arity_d I j d₀ q₀ h m)
    (rankOld : V_d I τ B₀) (constantsOld : ∀ x, M.mem x U₀ ↔ M.mem x B₀ ∨ x = τ)
    (poolOld : Tt_pool_d I ω m U₀ D₀)
    (heightQuery : Tg_height_query_d I ω h m U₀ D₀ ph) (heightMember : M.mem ph w)
    (domain : Ee_domain_d hZF ω κ q V E g₀ g₁)
    (rankLanguage : V_d I κ B) (constantsLanguage : ∀ x, M.mem x V ↔ M.mem x B ∨ x = κ)
    (rankCurrent : V_d I κ Bq) (constantsCurrent : ∀ x, M.mem x U ↔ M.mem x Bq ∨ x = κ)
    (defined : ∃ v, Td_dcp_d I q n E u v ∧ M.mem g₀ v ∧ M.mem g₁ v)
    (maxQuery : Tg_max_query_d I ω q n U D pm) :
    M.mem pm u := by
  obtain ⟨_,v',w',ℓ',j',κ',u',τ',T,d',q',l',m',B',V',W',request',move',answer',pair',
    _,arity',_,rankOld',constantsOld',poolOld',exceeds⟩ := rule
  have ev := request'.unique_l hZF oc fh request
  subst v'
  obtain ⟨el,ej,ek,eu⟩ := move'.unique_l move
  subst ℓ' j' κ' u'
  have ew := answer'.unique_l hZF oc fh answer
  subst w'
  obtain ⟨et,eT⟩ := kpair_injective_l M pair' pair
  subst τ' T
  obtain ⟨ed,eq,eh,em⟩ := arity'.unique_l hZF arity
  subst d' q' l' m'
  have eb := ZF.v_unique_l I hZF rankOld' rankOld
  subst B'
  have ev := hZF.1.eq_of_same_members V' U₀ (fun x => (constantsOld' x).trans (constantsOld x).symm)
  subst V'
  have eb := ZF.v_unique_l I hZF rankLanguage rankCurrent
  subst Bq
  have ev := hZF.1.eq_of_same_members V U (fun x => (constantsLanguage x).trans (constantsCurrent x).symm)
  subst V
  have height := heightQuery.scope_l I (ZF.modelsKP hZF) poolOld poolOld' (fun _ hx => hx)
  obtain ⟨v,drop,largest,parameters⟩ := defined
  exact tg_exceeds_rigid_l hZF hw arity.2.2.2.predecessor_mem drop.1 domain
    height maxQuery heightMember drop ⟨largest,parameters⟩ exceeds

/-- 第一原后继中的实际 subtype 自动实现原 u；最大序数固定回同一旧高度 α。 -/
theorem td_return_recovery_l
    {ω e j k d q h m l n δ η Y c R r S α B₀ a b p z A U₁ U₂ s
      κ τ U D w B V W u pn pm b₀ a₀ z₀ : M.Domain} {σ : Fin 7 → M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (rank : V_d I η Y) (model : Smem_d I c Y R)
    (oldType : Tt_realized_d I ω c Y R m r δ U D w)
    (record : Td_record_d I ω e j Y S a b p α d q h m r)
    (rankHeight : V_d I α B₀) (treeHeight : M.mem S B₀)
    (fa : M.IsSetFunctionFromTo I a j U₁) (fb : M.IsSetFunctionFromTo I b j U₂)
    (pending : Td_pending_d I ω A j S p) (pair : KPair_d M p j z)
    (alphabet : Td_alphabet_d S U₁ U₂) (disjoint : ∀ x, M.mem x U₁ → ¬ M.mem x U₂)
    (next : M.SuccessorOf k j) (last : M.SuccessorOf n l)
    (prog : Ts_program_d hZF ω m b₀ σ a₀ z₀)
    (oldLimit : M.IsLimitOrdinal κ) (currentLimit : M.IsLimitOrdinal τ) (hn : M.mem n ω)
    (currentRank : V_d I τ B) (constants : ∀ x, M.mem x V ↔ M.mem x B ∨ x = τ)
    (pool : Tt_pool_d I ω n V W)
    (subtype : Ts_subtype_d ω m κ τ n U u b₀ σ z₀ w)
    (nodeQuery : Td_node_query_d I ω e n l V W s k pn)
    (maxQuery : Tg_max_query_d I ω l n V W pm) (nodeMember : M.mem pn u) (maxMember : M.mem pm u) :
    ∃ ν Z c' H r' a' b' z' π, M.mem ν η ∧ V_d I ν Z ∧ Smem_d I c' Z H ∧
      Tt_realized_d I ω c' Z H n r' δ V W u ∧ M.IsSetBijectionFromTo I π n n ∧
      (∀ i v x, Rd_entry_d v i π → M.mem i m → (Rd_entry_d i x r ↔ Rd_entry_d v x r')) ∧
      M.SuccessorOf ν α ∧ Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧
      Td_labels_d I e l r' a' b' ∧ Tg_node_d I k S s a' b' ∧ Td_groups_d I ω e l r' a' b' ∧
      M.IsSetFunctionFromTo I a' k U₁ ∧ M.IsSetFunctionFromTo I b' k U₂ ∧
      M.MemberSubset a a' ∧ M.MemberSubset b b' ∧ Rd_entry_d j z a' ∧
      (∀ x, M.mem x a' ↔ M.mem x a ∨ KPair_d M x j z) ∧
      M.mem z' U₂ ∧ Rd_entry_d j z' b' ∧
      (∀ x, M.mem x b' ↔ M.mem x b ∨ KPair_d M x j z') := by
  obtain ⟨below,_,code,query,member⟩ := subtype
  obtain ⟨included,ν,hν,witness⟩ :=
    (query.read_l hZF hw prog rank model oldType oldLimit currentLimit below hn currentRank constants pool).mp member
  have rootS := pending.root_l hZF hw empty
  obtain ⟨_,z₁,pair₁,letter⟩ := pending
  have ez := (kpair_injective_l M pair₁ pair).2
  have chosen : M.mem z U₁ := ez ▸ (alphabet.1 z₁).mpr letter
  have fr := fn0_function_l (ZF.modelsKP hZF) record.tuple
  obtain ⟨Z,c',H,r',a',b',z',π,hZ,model',actual,permutation,moved,succ,root',last',labels,node,
    groups,fa',fb',suba,subb,oldz,appendA,hz',newz,appendB⟩ :=
    td_two_graph_recovery_l hZF empty next record.height_end last included nodeQuery maxQuery
      rankHeight treeHeight rootS ⟨fr.1,fr.2.1⟩ record.root record.height fa fb alphabet disjoint chosen pair record.values
      nodeMember maxMember witness
  exact ⟨ν,Z,c',H,r',a',b',z',π,hν,hZ,model',actual,permutation,moved,succ,root',last',labels,node,
    groups,fa',fb',suba,subb,oldz,appendA,hz',newz,appendB⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已运输旧回合的无额外不交假设恢复

不交性、两张旧图的函数性、待回应字母及树的秩界均从同一六十二槽
回合读取。查询与原 u 的实现由第一施加端点提供。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 旧实数字母域严格落在回答的秩层内，供下一次临界点以下的共同方块使用。 -/
theorem td_round_letters_l (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m) :
    V_d I (ρ.bound 0) (ρ.bound 1) ∧ M.mem (ρ.bound 50) (ρ.bound 1) := by
  obtain ⟨seed,witness⟩ := (Formula.satisfies_conj_iff ..).mp round
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,language,_,_,_,_,_,_,_,letters,_⟩ := seed
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,
    Formula.satisfies_conj_iff] at language
  have base : V_d I (ρ.bound 24) (ρ.bound 34) :=
    (v_sigma_sat_l (ZF.modelsKP hZF) ..).mp language.2.2.1
  have constants : ∀ x, M.mem x (ρ.bound 35) ↔ M.mem x (ρ.bound 34) ∨ x = ρ.bound 24 :=
    (tt_constants0_sat_l hZF.1 ..).mp language.2.2.2.1
  have letters : M.mem (ρ.bound 50) (ρ.bound 35) := (Formula.satisfies_mem_iff ..).mp letters
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at witness
  have below : M.mem (ρ.bound 24) (ρ.bound 0) := (Formula.satisfies_mem_iff ..).mp witness.2.1
  have lang := witness.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,
    Formula.satisfies_conj_iff] at lang
  have limit : M.IsLimitOrdinal (ρ.bound 0) := (Formula.satisfies_isLimitOrdinal_iff ..).mp lang.2.1
  have rank : V_d I (ρ.bound 0) (ρ.bound 1) := (v_sigma_sat_l (ZF.modelsKP hZF) ..).mp lang.2.2.1
  refine ⟨rank,?_⟩
  rcases (constants _).mp letters with ha | eq
  · exact ZF.v_mono_l I hZF base rank
      (fun x hx => limit.1.transitive _ below x hx) _ ha
  · exact eq.symm ▸ ZF.v_ordinal_mem_l I hZF rank below

theorem td_round_recover_l (ρ : Env M 62) (round : Formula.satisfies ρ td_round0_m)
    {n k s U D u pn pm : M.Domain}
    (next : M.SuccessorOf k (ρ.bound 25)) (last : M.SuccessorOf n (ρ.bound 9))
    (real : Ts_real_d hZF (ρ.bound 19) (ρ.bound 21) (ρ.bound 9) (ρ.bound 10) n U D u (ρ.bound 5))
    (nodeQuery : Td_node_query_d I (ρ.bound 19) (ρ.bound 20) n (ρ.bound 9) U D s k pn)
    (maxQuery : Tg_max_query_d I (ρ.bound 19) (ρ.bound 9) n U D pm)
    (nodeMember : M.mem pn u) (maxMember : M.mem pm u) :
    ∃ ν X c R r a b z π, M.mem ν (ρ.bound 5) ∧ V_d I ν X ∧ Smem_d I c X R ∧
      Tt_realized_d I (ρ.bound 19) c X R n r (ρ.bound 21) U D u ∧
      M.IsSetBijectionFromTo I π n n ∧
      (∀ i v x, Rd_entry_d v i π → M.mem i (ρ.bound 9) →
        (Rd_entry_d i x (ρ.bound 10) ↔ Rd_entry_d v x r)) ∧
      M.SuccessorOf ν (ρ.bound 23) ∧ Rd_entry_d (ρ.bound 20) (ρ.bound 22) r ∧
      Rd_entry_d (ρ.bound 9) (ρ.bound 23) r ∧
      Td_labels_d I (ρ.bound 20) (ρ.bound 9) r a b ∧ Tg_node_d I k (ρ.bound 22) s a b ∧
      Td_groups_d I (ρ.bound 19) (ρ.bound 20) (ρ.bound 9) r a b ∧
      M.IsSetFunctionFromTo I a k (ρ.bound 47) ∧ M.IsSetFunctionFromTo I b k (ρ.bound 48) ∧
      M.MemberSubset (ρ.bound 45) a ∧ M.MemberSubset (ρ.bound 46) b ∧
      Rd_entry_d (ρ.bound 25) (ρ.bound 49) a ∧
      (∀ x, M.mem x a ↔ M.mem x (ρ.bound 45) ∨ KPair_d M x (ρ.bound 25) (ρ.bound 49)) ∧
      M.mem z (ρ.bound 48) ∧ Rd_entry_d (ρ.bound 25) z b ∧
      (∀ x, M.mem x b ↔ M.mem x (ρ.bound 46) ∨ KPair_d M x (ρ.bound 25) z) := by
  have hKP := ZF.modelsKP hZF
  obtain ⟨seed,witness⟩ := (Formula.satisfies_conj_iff ..).mp round
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    Formula.satisfies_isEmpty_iff,woodin_sat_l I hZF.1,tg_low_sat_l hZF,
    tg_node_sat_l I hZF.1,td_tree_sat_l I hZF.1,td_alphabet_sat_l hZF.1,
    td_separated_sat_l hZF.1,Formula.satisfies_mem_iff] at seed
  obtain ⟨hw,he,woodin,low,_,_,_,_,_,_,_,_,_,_,_,_,_,_,node,tree,_,alphabet,chosen,_,_,separated⟩ := seed
  obtain ⟨_,_,_,_,regular,_⟩ := woodin
  obtain ⟨_,B,rankB,treeB⟩ := low.read_l hZF regular.isLimitOrdinal.1
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,kpair0_sat_l hZF.1,
    td_record_sat_l I hZF.1] at witness
  obtain ⟨_,_,_,_,_,_,_,_,_,pair,record,_⟩ := witness
  have pending : Td_pending_d I (ρ.bound 19) (ρ.bound 50) (ρ.bound 25) (ρ.bound 22) (ρ.bound 11) :=
    ⟨tree,ρ.bound 49,pair,(alphabet.1 _).mp chosen⟩
  have range := alphabet.node_l I hZF.1 node
  have fa : M.IsSetFunctionFromTo I (ρ.bound 45) (ρ.bound 25) (ρ.bound 47) :=
    ⟨node.2.1.1,node.2.1.2,fun i hi => ((node.2.1.2 i).mp hi).imp fun x hx => ⟨range.1 i x hx,hx⟩⟩
  have fb : M.IsSetFunctionFromTo I (ρ.bound 46) (ρ.bound 25) (ρ.bound 48) :=
    ⟨node.2.2.1.1,node.2.2.1.2,fun i hi => ((node.2.2.1.2 i).mp hi).imp fun x hx => ⟨range.2 i x hx,hx⟩⟩
  obtain ⟨ν,hν,actual⟩ := real
  have fr := fn0_function_l hKP record.tuple
  obtain ⟨X,c,R,r,a,b,z,π,result⟩ := td_two_graph_recovery_l hZF he next record.height_end last
    (fun x hx => (last x).mpr (Or.inl hx)) nodeQuery maxQuery rankB treeB
      (pending.root_l hZF hw he) ⟨fr.1,fr.2.1⟩ record.root record.height fa fb alphabet
        (separated.alphabet_l alphabet) chosen pair record.values nodeMember maxMember actual
  exact ⟨ν,X,c,R,r,a,b,z,π,hν,result⟩

end YesMetaZFC.SetTheory.LargeCardinal
