import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.Model.SetTheory.Demand.NodeScope

/-! # 指定待回应标签的实际后继秩界

字母值从同一原树中的真实出现位置回收，自然数指标由 ω 的既有上界回收。
Kuratowski 对的两次配对分别放入两个后继层，再进入给定的第三后继层；
不要求原高度为极限，也不输入额外的配对闭包证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两次实际幂层已容纳指定标签对；不需要第三个后继。 -/
theorem Td_alphabet_d.pending_rank_two_l
    {ω α β γ Z W S U₁ U₂ k z p : M.Domain}
    (alphabet : Td_alphabet_d S U₁ U₂) (rank : V_d I α Z) (hS : M.mem S Z)
    (above : M.MemberSubset ω α) (hk : M.mem k ω) (hz : M.mem z U₁)
    (first : M.SuccessorOf β α) (second : M.SuccessorOf γ β)
    (target : V_d I γ W) (pair : KPair_d M p k z) : M.mem p W := by
  have hzZ := ((alphabet.1 z).mp hz).mem_l (v_transitive_l I rank) hS
  have hkZ := KP.v_ordinal_subset_l (ZF.modelsKP hZF) rank k (above k hk)
  have oβ := KP.successor_isOrdinal (ZF.modelsKP hZF) (v_ordinal_l I rank) first
  obtain ⟨Z₁,r₁⟩ := ZF.v_exists_l I hZF oβ
  have pow₁ := ZF.v_successor_l I hZF rank r₁ first
  have pow₂ := ZF.v_successor_l I hZF r₁ target second
  obtain ⟨a,b,ha,hb,hp⟩ := pair
  have ha₁ : M.mem a Z₁ := (pow₁ a).mpr (fun y hy => ((ha y).mp hy).symm ▸ hkZ)
  have hb₁ : M.mem b Z₁ := (pow₁ b).mpr (fun y hy =>
    ((hb y).mp hy).elim (fun eq => eq.symm ▸ hkZ) (fun eq => eq.symm ▸ hzZ))
  exact (pow₂ p).mpr (fun y hy =>
    ((hp y).mp hy).elim (fun eq => eq.symm ▸ ha₁) (fun eq => eq.symm ▸ hb₁))

/-- 三后继读取直接使用同一两后继所属证明。 -/
theorem Td_alphabet_d.pending_rank_l
    {ω α β γ η Z W S U₁ U₂ k z p : M.Domain}
    (alphabet : Td_alphabet_d S U₁ U₂) (rank : V_d I α Z) (hS : M.mem S Z)
    (above : M.MemberSubset ω α) (hk : M.mem k ω) (hz : M.mem z U₁)
    (first : M.SuccessorOf β α) (second : M.SuccessorOf γ β) (third : M.SuccessorOf η γ)
    (target : V_d I η W) (pair : KPair_d M p k z) : M.mem p W := by
  have oβ := KP.successor_isOrdinal (ZF.modelsKP hZF) (v_ordinal_l I rank) first
  have oγ := KP.successor_isOrdinal (ZF.modelsKP hZF) oβ second
  obtain ⟨Z₂,r₂⟩ := ZF.v_exists_l I hZF oγ
  have hp₂ := alphabet.pending_rank_two_l hZF rank hS above hk hz first second r₂ pair
  exact ZF.v_mono_l I hZF r₂ target (fun x hx => (third x).mpr (Or.inl hx)) p hp₂

/-- 指定字母实际产生位于第二后继层的同一 pending 对。 -/
theorem Td_alphabet_d.pending_pair_two_l
    {ω α β γ Z W S U₁ U₂ k z : M.Domain}
    (alphabet : Td_alphabet_d S U₁ U₂) (rank : V_d I α Z) (hS : M.mem S Z)
    (above : M.MemberSubset ω α) (hk : M.mem k ω) (hz : M.mem z U₁)
    (first : M.SuccessorOf β α) (second : M.SuccessorOf γ β)
    (target : V_d I γ W) : ∃ p, M.mem p W ∧ KPair_d M p k z := by
  obtain ⟨p,pair⟩ := (I).total k z
  exact ⟨p,alphabet.pending_rank_two_l hZF rank hS above hk hz first second target pair,pair⟩

/-- 原指定字母实际生成 pending 对及其所属证明，供完整旧类型工厂直接使用。 -/
theorem Td_alphabet_d.pending_pair_l
    {ω α β γ η Z W S U₁ U₂ k z : M.Domain}
    (alphabet : Td_alphabet_d S U₁ U₂) (rank : V_d I α Z) (hS : M.mem S Z)
    (above : M.MemberSubset ω α) (hk : M.mem k ω) (hz : M.mem z U₁)
    (first : M.SuccessorOf β α) (second : M.SuccessorOf γ β) (third : M.SuccessorOf η γ)
    (target : V_d I η W) : ∃ p, M.mem p W ∧ KPair_d M p k z := by
  obtain ⟨p,pair⟩ := (I).total k z
  exact ⟨p,alphabet.pending_rank_l hZF rank hS above hk hz first second third target pair,pair⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原两图、指定 pending 与高度的实际典范元组

归纳沿模型内部的 ω 进行，不要求有限长度在外部标准。每轮读取原两图
的同一末项，将其配对码放入两个新槽；最终才追加指定挑战和高度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

private def Td_tuple_d (I : kpair_convention_l.Interpretation M)
    (ω e X S a b k : M.Domain) : Prop :=
  ∃ d q r a' b', M.IsOrdinalAddition I d k k ∧ M.SuccessorOf q d ∧ M.mem q ω ∧
    Fn0_d q X r ∧ Rd_entry_d e S r ∧ M.IsRestrictionOf I a' a k ∧
      M.IsRestrictionOf I b' b k ∧ Td_groups_d I ω e q r a' b'

private def td_tuple_m {d} (ω e X S a b k : Term d) : Formula 1 d := set[d] ⟪
  ∃ d q r a' b', ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(d,⌜k⌝ₛ,⌜k⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(q,d) ∧ q ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(q,⌜X⌝ₛ,r) ∧
    ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ,⌜S⌝ₛ,r) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(a',⌜a⌝ₛ,⌜k⌝ₛ) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(b',⌜b⌝ₛ,⌜k⌝ₛ) ∧
    ⌜td_groups_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,q,r,a',b')⟫

derive_free_closed td_tuple_m

private theorem td_tuple_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω e X S a b k : Term d) :
    Formula.satisfies ρ (td_tuple_m ω e X S a b k) ↔
      Td_tuple_d I (ω.eval ρ) (e.eval ρ) (X.eval ρ) (S.eval ρ)
        (a.eval ρ) (b.eval ρ) (k.eval ρ) := by
  simp only [td_tuple_m,Td_tuple_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff I hE,Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hE,rd_entry0_sat_l hE,
    Formula.satisfies_isRestriction_iff I,td_groups_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部旧标签的实际列：树在首位，之后恰为两张图的奇、偶值集合。 -/
theorem td_tuple_prefix_l {ω e k X S a b A B : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hk : M.mem k ω)
    (fa : M.IsSetFunctionFromTo I a k A) (fb : M.IsSetFunctionFromTo I b k B)
    (hS : M.mem S X) (ha : M.MemberSubset a X) (hb : M.MemberSubset b X) :
    ∃ d q r, M.IsOrdinalAddition I d k k ∧ M.SuccessorOf q d ∧ M.mem q ω ∧
      Fn0_d q X r ∧ Rd_entry_d e S r ∧ Td_groups_d I ω e q r a b := by
  let ρ : Env M 7 := ⟨fun i => [ω,e,X,S,a,b,k].get i,fun _ => ω⟩
  let φ : UnarySchema 7 := { body := .imp (Formula.subset .newest (.bound 7)) (td_tuple_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest) }
  have sat i : φ.denote ρ i ↔ (M.MemberSubset i k → Td_tuple_d I ω e X S a b i) := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_subset_iff,
      td_tuple_sat_l I hZF.1]
    rfl
  have build : ∀ i, M.mem i ω → M.MemberSubset i k → Td_tuple_d I ω e X S a b i := by
    have induction : ∀ i, M.mem i ω → φ.denote ρ i := by
      apply hw.induction (fun i => φ.denote ρ i) (ZF.separation_exists_d hZF φ ρ ω)
      · intro z hz
        have eq := hZF.1.eq_of_same_members z e (fun x => iff_of_false (hz x) (empty x))
        subst z
        apply (sat e).mpr
        intro _
        have he := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
        obtain ⟨q,sq,hq⟩ := hw.1.2 e he
        obtain ⟨r,fr,points⟩ := ZF.exists_constantFunction hZF I (source := q) hS
        have cut f : M.IsRestrictionOf I e f e := ⟨(tg_graph_empty_l I empty).1.1,
          fun i x => iff_of_false (fun ⟨p,_,hp⟩ => empty p hp) (fun h => empty i h.1)⟩
        have groups : Td_groups_d I ω e q r e e := by
          constructor <;> intro p <;> apply iff_of_false (empty p) <;>
            rintro ⟨i,hi,ne,_⟩ <;>
            exact ((sq i).mp hi).elim (empty i) (fun eq => ne (hZF.1.eq_of_same_members i e eq))
        exact ⟨e,q,r,e,e,(ZF.ordinalAddition_zero_iff hZF I empty).mpr rfl,sq,hq,
          fn0_of_function_l (ZF.modelsKP hZF) fr,(points e S).mpr ⟨sq.predecessor_mem,rfl⟩,
          cut a,cut b,groups⟩
      · intro i hi ih j succ
        apply (sat j).mpr
        intro jk
        have ik : M.MemberSubset i k := fun x hx => jk x ((succ x).mpr (Or.inl hx))
        obtain ⟨d,q,r,a₀,b₀,add,sq,hq,fr,root,ra,rb,groups⟩ := (sat i).mp ih ik
        obtain ⟨a₁,ra₁⟩ := ZF.exists_restriction hZF I a j
        obtain ⟨b₁,rb₁⟩ := ZF.exists_restriction hZF I b j
        obtain ⟨x,_,pa,pairA,paA⟩ := fa.2.2 i (jk i succ.predecessor_mem)
        obtain ⟨y,_,pb,pairB,pbB⟩ := fb.2.2 i (jk i succ.predecessor_mem)
        obtain ⟨q₁,sq₁,hq₁⟩ := hw.1.2 q hq
        obtain ⟨q₂,sq₂,hq₂⟩ := hw.1.2 q₁ hq₁
        have oq := hw.members_areOrdinals (ZF.modelsKP hZF) q hq
        obtain ⟨r₁,fr₁,g₁⟩ := td_tuple_append_l (ZF.modelsKP hZF) oq sq₁ fr (ha pa paA)
        obtain ⟨r₂,fr₂,g₂⟩ := td_tuple_append_l (ZF.modelsKP hZF)
          (hw.members_areOrdinals (ZF.modelsKP hZF) q₁ hq₁) sq₂ fr₁ (hb pb pbB)
        have hd := hw.transitive (ZF.modelsKP hZF) q hq d sq.predecessor_mem
        have odd : ¬ Gm_even_d I ω q := fun even =>
          ((gm_even_successor_l I hZF hw hd sq).mp even) ⟨i,hi,add⟩
        have groups₂ := groups.append_pair_l hZF hw empty hq sq₁ sq₂ fr fr₁ odd g₁ g₂
          (td_restrict_next_l (ZF.modelsKP hZF) fa.1 succ ra ra₁ pairA paA)
          (td_restrict_next_l (ZF.modelsKP hZF) fb.1 succ rb rb₁ pairB pbB)
        have oi := hw.members_areOrdinals (ZF.modelsKP hZF) i hi
        obtain ⟨p,hp,_⟩ := ZF.ordinalAddition_existsUnique hZF I j oi
        have next := Structure.natural_add_left_successor hZF I hw hi succ hi add hp
        have ep := next.eq hZF.1 sq
        have twice : M.IsOrdinalAddition I q₁ j j :=
          (ZF.ordinalAddition_successor_iff hZF I oi succ).mpr ⟨q,ep ▸ hp,sq₁⟩
        exact ⟨q₁,q₂,r₂,a₁,b₁,twice,sq₂,hq₂,fr₂,
          (g₂ e S).mpr (Or.inl ((g₁ e S).mpr (Or.inl root))),ra₁,rb₁,groups₂⟩
    exact fun i hi => (sat i).mp (induction i hi)
  obtain ⟨d,q,r,a₀,b₀,add,sq,hq,fr,root,ra,rb,groups⟩ := build k hk (fun _ h => h)
  have self f Y (ff : M.IsSetFunctionFromTo I f k Y) : M.IsRestrictionOf I f f k :=
    ⟨ff.1.1,fun i x => ⟨fun h => ⟨ff.input_mem_of_pairMember h,h⟩,fun h => h.2⟩⟩
  have ea := ra.eq hZF.1 (self a A fa)
  have eb := rb.eq hZF.1 (self b B fb)
  subst a₀ b₀
  exact ⟨d,q,r,add,sq,hq,fr,root,groups⟩

/-- 从同一两图实际造出全部旧标签、指定 pending 与高度，不预设元组。 -/
theorem td_tuple_pending_l {ω e k X S a b A B p α : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hk : M.mem k ω)
    (fa : M.IsSetFunctionFromTo I a k A) (fb : M.IsSetFunctionFromTo I b k B)
    (hS : M.mem S X) (ha : M.MemberSubset a X) (hb : M.MemberSubset b X)
    (hp : M.mem p X) (hα : M.mem α X) :
    ∃ d q h m r, Td_record_d I ω e k X S a b p α d q h m r := by
  obtain ⟨d,q,r₀,add,sq,hq,fr₀,root,groups⟩ := td_tuple_prefix_l hZF hw empty hk fa fb hS ha hb
  obtain ⟨h,m,r,record,_⟩ := td_record_append_l (ZF.modelsKP hZF) hw empty hq add sq fr₀ root groups hp hα
  exact ⟨d,q,h,m,r,record⟩

/-- 同一实际记录立即产生完整类型及完整 pending 查询成员。 -/
theorem tt_demand_tuple_realize_l
    {ω e k U ν X c R δ S s a b p z α U₁ U₂ A P Y F : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hk : M.mem k ω)
    (rank : V_d I ν X) (model : Smem_d I c X R)
    (fa : M.IsSetFunctionFromTo I a k U₁) (fb : M.IsSetFunctionFromTo I b k U₂)
    (hS : M.mem S X) (ha : M.mem a X) (hb : M.mem b X) (hp : M.mem p X) (hα : M.mem α X)
    (point : M.mem δ X) (constants : M.MemberSubset U X)
    (hwU : M.mem ω U) (hAU : M.mem A U) (hkU : M.mem k U) (hsU : M.mem s U)
    (node : Tg_node_d I k S s a b)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P U₁ U₂) (triple : M.IsCartesianProduct I Y A P)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) (pending : KPair_d M p k z) :
    ∃ d q h m r D T query check, Td_record_d I ω e k X S a b p α d q h m r ∧
      Tt_realized_d I ω c X R m r δ U D T ∧
      Td_pending_query_d I ω A e m q U D k query ∧ M.mem query T ∧
      Td_node_query_d I ω e m q U D s k check ∧ M.mem check T := by
  have trans := v_transitive_l I rank
  obtain ⟨d,q,h,m,r,record⟩ := td_tuple_pending_l hZF hw empty hk fa fb hS
    (trans a ha) (trans b hb) hp hα
  obtain ⟨D,T,query,actual,read,member⟩ := tt_demand_pending_realize_l hZF hw record.finite
    (record.tuple.bound_l record.root).1 (record.tuple.bound_l record.pending).1
    rank model record.tuple point constants hwU hAU hkU record.root record.pending
    space tree pair triple alphabet chosen pending
  obtain ⟨check,checkQuery⟩ := tt_demand_node_query_l hZF hw record.finite
    (record.tuple.bound_l record.pending).1 record.root_before actual.pool hsU hkU
  exact ⟨d,q,h,m,r,D,T,query,check,record,actual,read,member,checkQuery,
    (checkQuery.2 c X R r δ T S model trans actual record.root).mpr
      ⟨a,b,ha,hb,record.groups.cover_l,node,record.groups⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 从原树、指定字母和实际秩层生产完整回答查询

两图与 pending 的所属证据由节点及秩界自产。得到的是同一真实类型中的
三条 7.1(6) 查询，且保留原两图的节点查询；子类型关系仍须由原构造证明。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 不额外输入图或 pending 的秩所属证明；它们全部来自同一 S∈Vβ。 -/
theorem td_reply_realize_l
    {ω e k U η Y c R δ S s a b z β U₁ U₂ A P X F : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hk : M.mem k ω)
    (bound : Tg_bound_d I δ S β) (height : Tg_height_d β η)
    (rank : V_d I η Y) (model : Smem_d I c Y R) (above : M.MemberSubset ω β)
    (constants : M.MemberSubset U Y)
    (hwU : M.mem ω U) (hAU : M.mem A U) (hkU : M.mem k U) (hsU : M.mem s U)
    (node : Tg_node_d I k S s a b)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P U₁ U₂) (triple : M.IsCartesianProduct I X A P)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) :
    ∃ p d q h m r D w qp qn qb qh,
      KPair_d M p k z ∧ Td_record_d I ω e k Y S a b p β d q h m r ∧
      Tt_realized_d I ω c Y R m r δ U D w ∧
      Td_pending_query_d I ω A e m q U D k qp ∧ M.mem qp w ∧
      Td_node_query_d I ω e m q U D s k qn ∧ M.mem qn w ∧
      Tg_bound_query_d I ω e h m U D qb ∧ M.mem qb w ∧
      Tg_height_query_d I ω h m U D qh ∧ M.mem qh w := by
  obtain ⟨Z,hZ,hS⟩ := bound.2.2
  obtain ⟨β₁,β₂,s₁,s₂,s₃⟩ := height
  have oη := v_ordinal_l I rank
  have hβ₁ := oη.transitive β₂ s₃.predecessor_mem β₁ s₂.predecessor_mem
  have hβ := oη.transitive β₁ hβ₁ β s₁.predecessor_mem
  have small := ZF.v_mono_l I hZF hZ rank (oη.transitive β hβ)
  obtain ⟨Z₁,hZ₁⟩ := ZF.v_exists_l I hZF (oη.mem hβ₁)
  have next := ZF.v_successor_l I hZF hZ hZ₁ s₁
  have lower := ZF.v_mono_l I hZF hZ₁ rank (oη.transitive β₁ hβ₁)
  have labels := node.aux_labels_rank_l hZF hZ hS
  have ha := lower a ((next a).mpr labels.1)
  have hb := lower b ((next b).mpr labels.2)
  obtain ⟨p,hp,cp⟩ := alphabet.pending_pair_l hZF hZ hS above hk chosen s₁ s₂ s₃ rank
  have ranges := alphabet.node_l I hZF.1 node
  have fa : M.IsSetFunctionFromTo I a k U₁ := ⟨node.2.1.1,node.2.1.2,
    fun i hi => ((node.2.1.2 i).mp hi).imp fun x hx => ⟨ranges.1 i x hx,hx⟩⟩
  have fb : M.IsSetFunctionFromTo I b k U₂ := ⟨node.2.2.1.1,node.2.2.1.2,
    fun i hi => ((node.2.2.1.2 i).mp hi).imp fun x hx => ⟨ranges.2 i x hx,hx⟩⟩
  have hδ := ZF.v_ordinal_mem_l I hZF rank (oη.transitive β hβ δ bound.2.1)
  obtain ⟨d,q,h,m,r,D,w,qp,qn,record,actual,pending,hqp,nodeQuery,hqn⟩ :=
    tt_demand_tuple_realize_l hZF hw empty hk rank model fa fb (small S hS) ha hb hp
      (ZF.v_ordinal_mem_l I hZF rank hβ) hδ constants hwU hAU hkU hsU node
      space tree pair triple alphabet chosen cp
  obtain ⟨qb,bq⟩ := tt_bound_query_l hZF hw (record.tuple.bound_l record.root).1
    record.height_end.predecessor_mem hwU actual.pool
  obtain ⟨qh,hq⟩ := tt_height_query_l hZF hw record.height_end.predecessor_mem actual.pool
  exact ⟨p,d,q,h,m,r,D,w,qp,qn,qb,qh,cp,record,actual,pending,hqp,nodeQuery,hqn,bq,
    (bq.2 η Y c R r δ w S β rank model actual record.root record.height).mpr bound,hq,
    (hq.2 η Y c R r δ w β rank model actual record.height).mpr ⟨β₁,β₂,s₁,s₂,s₃⟩⟩

end YesMetaZFC.SetTheory.Internal
