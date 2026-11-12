import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Parameters
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReplyBase
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope

/-! # demanding 游戏两种元数的实际固定查询包

同一 κ 常量域承载节点型与回答型两个池。五个查询分别检查完整双组
节点、节点高度、原第一字母表上的 pending、严格秩界及回答高度。
所有码先由实际程序构造，再在给定极限秩层内有限配对封装。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_query_packet_d (hZF : M.Models ZF) (ω e κ k s A c : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ d q n m B U Du Dw pn pm pp pb ph t u,
    Td_arity_d I k d q n m ∧
    Rd_quad_d c B U Du t ∧ Rd_quad_d t Dw pn pm u ∧ Rd_triple_d u pp pb ph ∧
    V_d I κ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧
    Tt_pool_d I ω n U Du ∧ Tt_pool_d I ω m U Dw ∧
    Td_node_query_d I ω e n q U Du s k pn ∧ Tg_max_query_d I ω q n U Du pm ∧
    Td_pending_query_d I ω A e m q U Dw k pp ∧ Tg_bound_query_d I ω e n m U Dw pb ∧
    Tg_height_query_d I ω n m U Dw ph ∧ Td_reply_base_d I ω A e k q n m pp pb ph

def td_query_packet_m {l} (ω e κ k s A c : Term l) : Formula 1 l := set[l] ⟪
  ∃ d q n m B U Du Dw pn pm pp pb ph t u,
    ⌜td_arity_m⌝ₚ(⌜k⌝ₛ,d,q,n,m) ∧
    ⌜rd_quad_m⌝ₚ(⌜c⌝ₛ,B,U,Du,t) ∧ ⌜rd_quad_m⌝ₚ(t,Dw,pn,pm,u) ∧ ⌜rd_triple0_m⌝ₚ(u,pp,pb,ph) ∧
    ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ,B) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ,B,U) ∧
    ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,n,U,Du) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,m,U,Dw) ∧
    ⌜td_node_query_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,n,q,U,Du,⌜s⌝ₛ,⌜k⌝ₛ,pn) ∧
    ⌜tg_max_query_m⌝ₚ(⌜ω⌝ₛ,q,n,U,Du,pm) ∧
    ⌜td_pending_query_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜e⌝ₛ,m,q,U,Dw,⌜k⌝ₛ,pp) ∧
    ⌜tg_bound_query_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,n,m,U,Dw,pb) ∧
    ⌜tg_height_query_m⌝ₚ(⌜ω⌝ₛ,n,m,U,Dw,ph) ∧
    ⌜td_reply_base_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜e⌝ₛ,⌜k⌝ₛ,q,n,m,pp,pb,ph)⟫
derive_free_closed td_query_packet_m

theorem td_query_packet_sat_l (hZF : M.Models ZF) {l} (ρ : Env M l) (ω e κ k s A c : Term l) :
    Formula.satisfies ρ (td_query_packet_m ω e κ k s A c) ↔ Td_query_packet_d hZF
      (ω.eval ρ) (e.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (A.eval ρ) (c.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_query_packet_m,Td_query_packet_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    td_arity_sat_l I hZF.1,rd_quad_sat_l hZF.1,rd_triple0_sat_l hZF.1,
    v_sigma_sat_l (ZF.modelsKP hZF),tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF),td_node_query_sat_l I (ZF.modelsKP hZF),
    tg_max_query_sat_l I (ZF.modelsKP hZF),td_pending_query_sat_l I (ZF.modelsKP hZF),
    tg_bound_query_sat_l I (ZF.modelsKP hZF),tg_height_query_sat_l I (ZF.modelsKP hZF),
    td_reply_base_sat_l I (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  rfl

/-- 请求实际生产全部五个查询，包码属于给定 Vδ；封装不使用选择公理。 -/
theorem td_query_packet_exists_l (hZF : M.Models ZF) {ω e δ X κ k s A : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (limit : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hkδ : M.mem κ δ)
    (request : Tg_query_request_d hZF ω κ k s A) :
    ∃ c, M.mem c X ∧ Td_query_packet_d hZF ω e κ k s A c := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hκ,hk,B,U,base,constants,hs,hA⟩ := request
  obtain ⟨d,q,n,m,arity,_,hq,hn,hm⟩ := td_arity_exists_l hZF hw hk
  have heq := (hw.members_areOrdinals (ZF.modelsKP hZF) q hq).empty_mem_of_nonempty
    (ZF.modelsKP hZF) ⟨d,arity.2.1.predecessor_mem⟩ empty
  have hen := (arity.2.2.1 e).mpr (Or.inl heq)
  have hem := (arity.2.2.2 e).mpr (Or.inl hen)
  have hqm := (arity.2.2.2 q).mpr (Or.inl arity.2.2.1.predecessor_mem)
  obtain ⟨Du,poolU⟩ := tt_pool_exists_l I hZF hw n U
  obtain ⟨Dw,poolW⟩ := tt_pool_exists_l I hZF hw m U
  have nat := tt_constants_finite_l hZF hw hk hκ base constants
  obtain ⟨pn,node⟩ := tt_demand_node_query_l hZF hw hn arity.2.2.1.predecessor_mem heq poolU hs nat.2
  obtain ⟨pm,max⟩ := tt_max_query_l hZF hw arity.2.2.1.predecessor_mem poolU
  obtain ⟨pp,pb,ph,replyBase⟩ := td_reply_base_l (A := A) (k := k) hZF hw hm hem hqm
    arity.2.2.2.predecessor_mem
  obtain ⟨pending,bound,height⟩ := replyBase.scope_l I (ZF.modelsKP hZF) poolW nat.1 hA nat.2
  have trans := v_transitive_l I rank
  have hB := ZF.v_mem_l I hZF base rank hkδ
  have hU := tt_constants_rank_l hZF rank limit hkδ base constants
  have hwX := ZF.v_ordinal_mem_l I hZF rank hwδ
  have hDu := poolU.rank_mem_l (ZF.modelsKP hZF) hw rank limit hwX hn hU
  have hDw := poolW.rank_mem_l (ZF.modelsKP hZF) hw rank limit hwX hm hU
  have pair a b (ha : M.mem a X) (hb : M.mem b X) : ∃ p, M.mem p X ∧ KPair_d M p a b := by
    obtain ⟨u,hu,cu⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank a a ha ha
    obtain ⟨v,hv,cv⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank a b ha hb
    obtain ⟨p,hp,cp⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank u v hu hv
    exact ⟨p,hp,u,v,(fun x => (cu x).trans ⟨fun h => h.elim id id,Or.inl⟩),cv,cp⟩
  have quad a b c d (ha : M.mem a X) (hb : M.mem b X) (hc : M.mem c X) (hd : M.mem d X) :
      ∃ r, M.mem r X ∧ Rd_quad_d r a b c d := by
    obtain ⟨p,hp,cp⟩ := pair c d hc hd
    obtain ⟨q,hq,cq⟩ := pair b p hb hp
    obtain ⟨r,hr,cr⟩ := pair a q ha hq
    exact ⟨r,hr,p,cp,q,cq,cr⟩
  obtain ⟨v,hv,cv⟩ := pair pb ph (trans Dw hDw pb bound.1) (trans Dw hDw ph height.1)
  obtain ⟨u,hu,cu⟩ := pair pp v (trans Dw hDw pp pending.1) hv
  obtain ⟨t,ht,ct⟩ := quad Dw pn pm u hDw (trans Du hDu pn node.1) (trans Du hDu pm max.1) hu
  obtain ⟨c,hc,cc⟩ := quad B U Du t hB hU hDu ht
  exact ⟨c,hc,d,q,n,m,B,U,Du,Dw,pn,pm,pp,pb,ph,t,u,arity,cc,ct,⟨v,cv,cu⟩,
    base,constants,poolU,poolW,node,max,pending,bound,height,replyBase⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.1 的固定查询表

模型内统一化一次选定每个合法键 (κ,k,s,A) 的完整查询包。
第四坐标始终是原第一字母表；无关键取空值，读取时保留原请求的全部秩条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_query_key_d (hZF : M.Models ZF) (ω δ x : M.Domain) : Prop :=
  ∃ κ k s A, Rd_quad_d x κ k s A ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s A

def td_query_key_m {d} (ω δ x : Term d) : Formula 1 d := set[d] ⟪∃ κ k s A,
  ⌜rd_quad_m⌝ₚ(⌜x⌝ₛ, κ, k, s, A) ∧ κ ∈ ⌜δ⌝ₛ ∧ ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ, κ, k, s, A)⟫
derive_free_closed td_query_key_m

theorem td_query_key_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω δ x : Term d) :
    Formula.satisfies ρ (td_query_key_m ω δ x) ↔ Td_query_key_d hZF (ω.eval ρ) (δ.eval ρ) (x.eval ρ) := by
  simp only [td_query_key_m, Td_query_key_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_query_catalog_d (ω e δ X Γ : M.Domain) : Prop := Fn0_d X X Γ ∧
  ∀ κ k s A x c, Rd_quad_d x κ k s A → M.mem κ δ → Tg_query_request_d hZF ω κ k s A →
    Rd_entry_d x c Γ → Td_query_packet_d hZF ω e κ k s A c

theorem td_query_catalog_l {ω e δ X : M.Domain} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X) :
    ∃ Γ, Td_query_catalog_d hZFC ω e δ X Γ ∧ M.MemberSubset Γ X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push e).push δ
  let φ : BinarySchema 3 := { body := set[5] ⟪(∃ κ k s A,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, κ, k, s, A) ∧ κ ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧
    ⌜tg_query_request_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, κ, k, s, A) ∧
    ⌜td_query_packet_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, κ, k, s, A, ⌜(.newest : Term 5)⌝ₛ)) ∨
    (¬ ⌜td_query_key_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ) ∧
      ⌜(.newest : Term 5)⌝ₛ = ⌜(.bound 3 : Term 5)⌝ₛ)⟫ }
  have sat x c : φ.denote ρ x c ↔
      (∃ κ k s A, Rd_quad_d x κ k s A ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s A ∧
        Td_query_packet_d hZF ω e κ k s A c) ∨ (¬ Td_query_key_d hZF ω δ x ∧ c = e) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF,
      td_query_packet_sat_l hZF, td_query_key_sat_l hZF, Definitional.Term.eval_weaken]
    rfl
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
  have heX := v_transitive_l I hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) e heω
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := X) (fun x _ => by
    by_cases key : Td_query_key_d hZF ω δ x
    · obtain ⟨κ, k, s, A, code, hk, request⟩ := key
      obtain ⟨c, hc, packet⟩ := td_query_packet_exists_l hZF hω he hδ hwδ hX hk request
      exact ⟨c, hc, (sat x c).mpr (Or.inl ⟨κ, k, s, A, code, hk, request, packet⟩)⟩
    · exact ⟨e, heX, (sat x e).mpr (Or.inr ⟨key, rfl⟩)⟩)
  refine ⟨Γ, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, fun κ k s A x c code hk request entry => ?_⟩, ?_⟩
  · rcases (sat x c).mp (all x c entry) with ⟨κ', k', s', A', code', _, _, packet⟩ | invalid
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := code'.unique_l code
      exact packet
    · exact (invalid.1 ⟨κ, k, s, A, code, hk, request⟩).elim
  · intro p hp
    obtain ⟨x, c, pair⟩ := fn.1.1 p hp
    have entry : Rd_entry_d x c Γ := ⟨p, pair, hp⟩
    obtain ⟨p', hp', pair'⟩ := (sc_v_algebra_l hZFC hδ hX).kpair_l
      (fn.input_mem_of_pairMember entry) (fn.output_mem_of_pairMember entry)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

theorem Td_query_catalog_d.get_l {ω e δ X Γ κ k s A : M.Domain}
    (table : Td_query_catalog_d hZFC ω e δ X Γ)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X)
    (hk : M.mem κ δ) (request : Tg_query_request_d hZF ω κ k s A) :
    ∃ x c, Rd_quad_d x κ k s A ∧ Rd_entry_d x c Γ ∧ Td_query_packet_d hZF ω e κ k s A c := by
  obtain ⟨limit, finite, B, U, rank, constants, hs, hA⟩ := request
  have trans := v_transitive_l I hX
  have hU := tt_constants_rank_l hZF hX hδ hk rank constants
  obtain ⟨x, hx, code⟩ := sc_quad_l (sc_v_algebra_l hZFC hδ hX) (ZF.v_ordinal_mem_l I hZF hX hk)
    (trans ω (ZF.v_ordinal_mem_l I hZF hX hwδ) k finite) (trans U hU s hs) (trans U hU A hA)
  obtain ⟨c, _, entry⟩ := table.1.2.1 x hx
  exact ⟨x, c, code, entry, table.2 κ k s A x c code hk ⟨limit, finite, B, U, rank, constants, hs, hA⟩ entry⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双辅助坐标游戏的固定查询行

键为 (κ,k,s,A)。同一行保存 u、w 的两个不同元数查询池及五条查询；
读取仅拆实际集合编码，语义由开局前已构造的函数表恢复。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_query_data_d (Γ κ k s A B U Du Dw pn pm pp pb ph : M.Domain) : Prop :=
  ∃ x c t v, Rd_quad_d x κ k s A ∧ Rd_entry_d x c Γ ∧
    Rd_quad_d c B U Du t ∧ Rd_quad_d t Dw pn pm v ∧ Rd_triple_d v pp pb ph

def td_query_data_m {d} (Γ κ k s A B U Du Dw pn pm pp pb ph : Term d) : Formula 1 d := set[d] ⟪
  ∃ x c t v, ⌜rd_quad_m⌝ₚ(x,⌜κ⌝ₛ,⌜k⌝ₛ,⌜s⌝ₛ,⌜A⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(x,c,⌜Γ⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(c,⌜B⌝ₛ,⌜U⌝ₛ,⌜Du⌝ₛ,t) ∧
    ⌜rd_quad_m⌝ₚ(t,⌜Dw⌝ₛ,⌜pn⌝ₛ,⌜pm⌝ₛ,v) ∧ ⌜rd_triple0_m⌝ₚ(v,⌜pp⌝ₛ,⌜pb⌝ₛ,⌜ph⌝ₛ)⟫
derive_free_closed td_query_data_m

theorem td_query_data_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (Γ κ k s A B U Du Dw pn pm pp pb ph : Term d) :
    Formula.satisfies ρ (td_query_data_m Γ κ k s A B U Du Dw pn pm pp pb ph) ↔
      Td_query_data_d (Γ.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (A.eval ρ) (B.eval ρ)
        (U.eval ρ) (Du.eval ρ) (Dw.eval ρ) (pn.eval ρ) (pm.eval ρ) (pp.eval ρ) (pb.eval ρ) (ph.eval ρ) := by
  simp only [td_query_data_m,Td_query_data_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_quad_sat_l hE,rd_entry0_sat_l hE,rd_triple0_sat_l hE,Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一表项一次恢复两个查询池的完整语义，未重新选择任何查询码。 -/
theorem Td_query_catalog_d.read_l
    {ω e δ X Γ κ k s A B U Du Dw pn pm pp pb ph : M.Domain}
    (table : Td_query_catalog_d hZFC ω e δ X Γ) (hk : M.mem κ δ)
    (request : Tg_query_request_d hZF ω κ k s A)
    (data : Td_query_data_d Γ κ k s A B U Du Dw pn pm pp pb ph) :
    ∃ d q n m, Td_arity_d I k d q n m ∧ V_d I κ B ∧
      (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧
      Tt_pool_d I ω n U Du ∧ Tt_pool_d I ω m U Dw ∧
      Td_node_query_d I ω e n q U Du s k pn ∧ Tg_max_query_d I ω q n U Du pm ∧
      Td_pending_query_d I ω A e m q U Dw k pp ∧
      Tg_bound_query_d I ω e n m U Dw pb ∧ Tg_height_query_d I ω n m U Dw ph ∧
      Td_reply_base_d I ω A e k q n m pp pb ph := by
  obtain ⟨x,c,t,v,key,entry,row,codes,tail⟩ := data
  obtain ⟨d,q,n,m,B',U',Du',Dw',pn',pm',pp',pb',ph',t',v',arity,row',codes',tail',rest⟩ :=
    table.2 κ k s A x c key hk request entry
  obtain ⟨rfl,rfl,rfl,rfl⟩ := row'.unique_l row
  obtain ⟨rfl,rfl,rfl,rfl⟩ := codes'.unique_l codes
  obtain ⟨rfl,rfl,rfl⟩ := tail'.unique_l tail
  exact ⟨d,q,n,m,arity,rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏的实际固定参数

内部自然数、重置高度、弹性表和程序表沿用已有实际构造。
查询表则一次构造为 demanding 查询包的统一表，保留原 ω、δ、A、S。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_setup_d (p : Tg_params_d M.Domain) (X : M.Domain) : Prop where
  omega : M.IsOmega p.ω
  empty : ∀ x, ¬ M.mem x p.e
  one : M.SuccessorOf p.a p.e
  two : M.SuccessorOf p.b p.a
  three : M.SuccessorOf p.c p.b
  limit : M.IsLimitOrdinal p.δ
  above : M.mem p.ω p.δ
  rank : V_d I p.δ X
  letters : M.mem p.A X
  elastic : ∃ D, Ee_catalog_d hZFC p.ω p.δ X D p.E
  programs : ∃ H, V_d I p.ω H ∧ Tg_program_catalog_d hZFC p.ω H p.P ∧ M.MemberSubset p.P H
  queries : Td_query_catalog_d hZFC p.ω p.e p.δ X p.Q
  elastic_bound : M.MemberSubset p.E X
  query_bound : M.MemberSubset p.Q X
  low : Tg_low_d hZF p.ω p.e p.δ p.S p.ν

/-- 所有表在开局前实际取定，查询表由本游戏的完整查询包生产。 -/
theorem td_setup_l {ω δ A S X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (rank : V_d I δ X) (hA : M.mem A X) :
    ∃ p : Tg_params_d M.Domain, p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = S ∧ Td_setup_d hZFC p X := by
  obtain ⟨e, ν, he, heω, low⟩ := tg_low_l hZF hω hδ.1 S
  obtain ⟨a, ha, haω⟩ := hω.1.2 e heω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 a haω
  obtain ⟨c, hc, _⟩ := hω.1.2 b hbω
  obtain ⟨D, E, elastic, eBound⟩ := ee_catalog_l hZFC hω hδ hwδ rank
  obtain ⟨H, P, hH, programs, pBound⟩ := tg_program_catalog_l hZFC hω
  obtain ⟨Q, queries, qBound⟩ := td_query_catalog_l hZFC hω he hδ hwδ rank
  exact ⟨⟨ω, e, a, b, c, δ, A, S, ν, E, P, Q⟩, rfl, rfl, rfl, rfl,
    hω, he, ha, hb, hc, hδ, hwδ, rank, hA, ⟨D, elastic⟩,
    ⟨H, hH, programs, pBound⟩, queries, eBound, qBound, low⟩

end YesMetaZFC.SetTheory.LargeCardinal
