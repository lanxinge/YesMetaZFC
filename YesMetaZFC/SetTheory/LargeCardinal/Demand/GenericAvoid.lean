import YesMetaZFC.SetTheory.LargeCardinal.Demand.LevelTable
import YesMetaZFC.SetTheory.LargeCardinal.Game.Tracked
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Demand.GenericReply
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.CumulativeFinite
import YesMetaZFC.Model.Forcing.Truth.Definability
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReadyStep
import YesMetaZFC.SetTheory.Descriptive.Tree.ScanStrategy
import YesMetaZFC.SetTheory.LargeCardinal.Demand.SeparatedGame
import YesMetaZFC.SetTheory.Ord.FirstCrossing
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.LargeCardinal.Game.DigitsImage
import YesMetaZFC.SetTheory.LargeCardinal.Demand.CounterGround
import YesMetaZFC.Model.SetTheory.Demand.Realize

/-! # 捕获高度与同一实际 counter 控制历史

高度来自原双图 level 表的像；扩张中的有限 counter 历史只保留其真实
控制集合成员性及交错两图。它不必来自地模型，也不预设无限分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

def Td_tracked_d (ω H K enum R Vc Rc α : M.Domain) : Prop := ∃ n h i v k a b q d t,
  M.mem n ω ∧ Rd_entry_d n h H ∧ Rd_entry_d h i K ∧ Rd_entry_d i v enum ∧
  Rd_quad_d q v k a b ∧ Rd_entry_d q α R ∧ M.IsOrdinalAddition I d k k ∧
  Fn0_d d Vc t ∧ M.mem t Rc ∧ Dg_weave_d I ω t a b

def td_tracked_m {l} (ω H K enum R Vc Rc α : Term l) : Formula 1 l := set[l] ⟪
  ∃ n h i v k a b q d t,
    n ∈ ⌜ω⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n,h,⌜H⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(h,i,⌜K⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(i,v,⌜enum⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(q,v,k,a,b) ∧ ⌜rd_entry0_m⌝ₚ(q,⌜α⌝ₛ,⌜R⌝ₛ) ∧
    ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(d,k,k) ∧ ⌜fn0_m⌝ₚ(d,⌜Vc⌝ₛ,t) ∧
    t ∈ ⌜Rc⌝ₛ ∧ ⌜dg_weave_m⌝ₚ(⌜ω⌝ₛ,t,a,b)⟫
derive_free_closed td_tracked_m

theorem td_tracked_sat_l {l} (ρ : Env M l) (ω H K enum R Vc Rc α : Term l) :
    Formula.satisfies ρ (td_tracked_m ω H K enum R Vc Rc α) ↔ Td_tracked_d hM
      (ω.eval ρ) (H.eval ρ) (K.eval ρ) (enum.eval ρ) (R.eval ρ) (Vc.eval ρ) (Rc.eval ρ) (α.eval ρ) := by
  simp only [td_tracked_m,Td_tracked_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,rd_entry0_sat_l hM.1,rd_quad_sat_l hM.1,
    Formula.satisfies_isOrdinalAddition_iff I hM.1,fn0_sat_l hM.1,dg_weave_sat_l I hM.1,
    Definitional.Term.eval_weaken]
  rfl

section Ground
variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include he

/-- 地表项与扩张中的同一控制历史直接组成 tracked 见证。 -/
theorem Td_level_table_d.track_l
    {p : Tg_params_d M.Domain} {X Z U₁ U₂ R n h v k a b α : M.Domain}
    {H K enum Vc Rc i d t : N.Domain} (table : Td_level_table_d hM p X Z U₁ U₂ R)
    (hn : M.mem n p.ω) (nh : Rd_entry_d (e n) (e h) H)
    (ki : Rd_entry_d (e h) i K) (iv : Rd_entry_d i (e v) enum)
    (key : Td_level_key_d hM p X Z U₁ U₂ v k a b α)
    (add : N.IsOrdinalAddition J d (e k) (e k)) (ft : Fn0_d (M := N) d Vc t)
    (control : N.mem t Rc) (weave : Dg_weave_d J (e p.ω) t (e a) (e b)) :
    Td_tracked_d hN (e p.ω) H K enum (e R) Vc Rc (e α) := by
  obtain ⟨q,code⟩ := rd_quad_exists_l (ZF.modelsKP hM) v k a b
  have entry := (table.2 q α).mpr ⟨v,k,a,b,code,key⟩
  exact ⟨e n,e h,i,e v,e k,e a,e b,e q,d,t,(he p.ω (e n)).mpr ⟨n,hn,rfl⟩,
    nh,ki,iv,rd_quad_image_l e he code,
    (image_entries_l e he table.1 (e q) (e α)).mpr ⟨q,α,entry,rfl,rfl⟩,add,ft,control,weave⟩

/-- 仅地表项和辅助运行历史被回读；counter 历史 t 原样留在扩张中。 -/
theorem Td_level_table_d.read_tracked_l
    {p : Tg_params_d M.Domain} {X Z U₁ U₂ R F : M.Domain}
    {H K enum Vc Rc α : N.Domain} (table : Td_level_table_d hM p X Z U₁ U₂ R)
    (hf : Fn0_d (M := N) (e p.ω) (e F) H)
    (tracked : Td_tracked_d hN (e p.ω) H K enum (e R) Vc Rc α) :
    ∃ n h v k a b β, ∃ i d t : N.Domain,
      e β = α ∧ M.mem n p.ω ∧ Rd_entry_d (e n) (e h) H ∧
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e v) enum ∧ Td_level_key_d hM p X Z U₁ U₂ v k a b β ∧
      N.IsOrdinalAddition J d (e k) (e k) ∧ Fn0_d (M := N) d Vc t ∧
      N.mem t Rc ∧ Dg_weave_d J (e p.ω) t (e a) (e b) := by
  obtain ⟨n,h,i,v,k,a,b,q,d,t,hn,nh,ki,iv,code,entry,add,ft,control,weave⟩ := tracked
  obtain ⟨n₀,hn₀,en⟩ := (he p.ω n).mp hn
  subst n
  obtain ⟨h₀,_,eh⟩ := (he F h).mp (hf.bound_l nh).2
  subst h
  obtain ⟨q₀,β,entry₀,eq,eβ⟩ := (image_entries_l e he table.1 q α).mp entry
  subst q α
  obtain ⟨v₀,k₀,a₀,b₀,code₀,key⟩ := (table.2 q₀ β).mp entry₀
  obtain ⟨rfl,rfl,rfl,rfl⟩ := (rd_quad_image_l e he code₀).unique_l code
  exact ⟨n₀,h₀,v₀,k₀,a₀,b₀,β,i,d,t,rfl,hn₀,nh,ki,iv,key,add,ft,control,weave⟩

end Ground

/-- 对真实 tracked 高度在模型内部取最小元，不构造或假设无限下降列。 -/
theorem td_tracked_min_l {ω H K enum R Vc Rc α : M.Domain} (hα : M.IsOrdinal α)
    (initial : Td_tracked_d hM ω H K enum R Vc Rc α) :
    ∃ β, M.IsOrdinal β ∧ Td_tracked_d hM ω H K enum R Vc Rc β ∧
      ∀ γ, M.mem γ β → ¬ Td_tracked_d hM ω H K enum R Vc Rc γ := by
  let ρ : Env M 7 := ⟨fun i => [ω,H,K,enum,R,Vc,Rc].get i,fun _ => ω⟩
  let φ : UnarySchema 7 := { body := td_tracked_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest }
  have sat β : φ.denote ρ β ↔ Td_tracked_d hM ω H K enum R Vc Rc β := td_tracked_sat_l hM ..
  obtain ⟨β,hβ,state,least⟩ := ZF.ordinal_min_l hM φ ρ hα ((sat α).mpr initial)
  exact ⟨β,hβ,(sat β).mp state,fun γ hγ h => least γ hγ ((sat γ).mpr h)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 继续请求的实际合法性

原回答与恢复记录通过实际排列相连，武丁工厂只生产一次新类型。
固定弹性表和查询表随后读取同一类型；两图的秩界与真实分组共同给出节点查询。
所得走法属于原 Vδ，在每个保留旧轮且实数前缀相符的后续局面中合法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.generic_continue_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ κ₀ u₀ b₀ j k d₀ q₀ l N τ B U D w η Y c R r norm ψ
      a b pending β s a' b' p' χ Z : M.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Td_move_d a₀ ℓ₀ j κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (hk : M.SuccessorOf k j) (hτ : M.IsLimitOrdinal τ) (hB : V_d I τ B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (record : Td_record_d I p.ω p.e j Y p.S a b pending β d₀ q₀ l N norm)
    (perm : M.IsSetBijectionFromTo I ψ N N)
    (points : ∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x r ↔ Rd_entry_d j x norm))
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s a' b')
    (appendA : ∀ x, M.mem x a' ↔ M.mem x a ∨ x = pending)
    (appendB : ∀ x, M.mem x b' ↔ M.mem x b ∨ x = p')
    (hχ : M.mem χ p.δ) (hτχ : M.MemberSubset τ χ) (hZ : V_d I χ Z)
    (hs : M.mem s Z) (hAZ : M.mem p.A Z) :
    ∃ κ C v u μ A d H m V P r',
      M.mem χ κ ∧ M.mem κ p.δ ∧ V_d I κ C ∧ M.mem v X ∧ Td_move_d v ℓ k κ u ∧
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧
      (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧
      Td_groups_d I p.ω p.e N r' a' b' ∧ M.IsOrdinalAddition I l k k ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Td_growth_d hZF p.e p.c p.A n h κ C → Td_aux_d hZF p n h v := by
  obtain ⟨μ,A,d,H,κ,C,V,E,P,m,r',u,q,hμ,hA,lower,above,hκ,language,hm,hkω,twice,
    full,elastic,root,_,_,last,groups,_,_,exceeds⟩ :=
    woodin_demand_continue_l hZFC hd setup.omega setup.empty hτ.1 hτχ hχ hY model type
      record perm points bound height hk node appendA appendB
  -- 固定弹性表只改变查询码的读取，原 u 及其实际实现保持不变。
  obtain ⟨C',V',E',q',data,target⟩ := setup.elastic.elim fun _ table =>
    table.get_l hZFC hκ type.finite language.limit
  have eqC := ZF.v_unique_l I hZF target.rank language.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun x => (target.constants x).trans (language.constants x).symm)
  subst V'
  have eqE := target.pool.unique_l hZF.1 I language.pool
  subst E'
  obtain ⟨t,drop,elastic⟩ := elastic
  obtain ⟨r₀,t₀,_,drop₀,prefixType⟩ := full.dcp_l hZF setup.omega hm language.pool
  have eqt := drop₀.unique_l I hZF.1 drop
  subst t₀
  have elastic' : Tg_elastic_d I N m E q' u :=
    ⟨t,drop,language.elastic_transfer_l hZFC target setup.omega hκ hA lower prefixType elastic⟩
  have sub := ZF.v_mono_l I hZF hZ language.rank (language.limit.1.transitive χ above)
  have hsV := (language.constants s).mpr (Or.inl (sub s hs))
  have hAV := (language.constants p.A).mpr (Or.inl (sub p.A hAZ))
  have request : Tg_query_request_d hZF p.ω κ k s p.A :=
    ⟨language.limit,hkω,C,V,language.rank,language.constants,hsV,hAV⟩
  obtain ⟨m₂,hm₂,_⟩ := setup.omega.1.2 m full.finite
  have arity : Td_arity_d I k l N m m₂ := ⟨twice,record.height_end,hm,hm₂⟩
  obtain ⟨key,row,encoded,entry,d',q₁,N',m',C',V',P',Dw,pn,pm,pp,pb,ph,t₁,v₀,
    arity',rowCode,codes,tail,rank,constant,pool,_,nodeQuery,_,_,_,_⟩ :=
    setup.queries.get_l hZFC setup.limit setup.above setup.rank hκ request
  obtain ⟨ed,eq,en,em⟩ := arity'.unique_l hZF arity
  subst d' q₁ N' m'
  have eqC := ZF.v_unique_l I hZF rank language.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun x => (constant x).trans (language.constants x).symm)
  subst V'
  have eqP := pool.unique_l hZF.1 I full.pool
  subst P'
  have queryData : Td_query_data_d p.Q κ k s p.A C V P Dw pn pm pp pb ph :=
    ⟨key,row,t₁,v₀,encoded,entry,rowCode,codes,tail⟩
  -- 两张真实辅助图都由同一个新节点落在 Vβ，故均属于实际实现层 V(β+1)。
  obtain ⟨Zβ,hZβ,hSβ⟩ := bound.2.2
  obtain ⟨left,right⟩ := node.aux_labels_rank_l hZF hZβ hSβ
  have haA := (ZF.v_unfold_l I hZF hA a').mpr ⟨β,Zβ,hμ.predecessor_mem,hZβ,left⟩
  have hbA := (ZF.v_unfold_l I hZF hA b').mpr ⟨β,Zβ,hμ.predecessor_mem,hZβ,right⟩
  have truth := (nodeQuery.2 d A H r' p.δ u p.S lower (v_transitive_l I hA) full root).mpr
    ⟨a',b',haA,hbA,groups.cover_l,node,groups⟩
  -- 有限配对与真实池的秩界保证整个辅助走法位于原 Vδ。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have tr := v_transitive_l I setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have hVX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit hwX full.finite hVX
  have uu : M.MemberSubset u P := fun x hx => ((full.truth x).mp hx).1
  have huX := v_subset_mem_l I setup.rank hPX uu
  obtain ⟨v,hv,move⟩ := sc_quad_l algebra (tr p.ω hwX ℓ hℓ) (tr p.ω hwX k hkω)
    (ZF.v_ordinal_mem_l I hZF setup.rank hκ) huX
  have ne : k ≠ p.e := fun eq => setup.empty j (eq ▸ hk.predecessor_mem)
  have oldArity : Td_arity_d I j d₀ q₀ l N :=
    ⟨record.twice,record.labels_end,record.pending_end,record.height_end⟩
  refine ⟨κ,C,v,u,μ,A,d,H,m,V,P,r',above,hκ,language.rank,hv,move,hμ,hA,lower,hm,
    language.constants,full,root,last,groups,twice,fun n h z digits real hℓn old₀ old₁ growth => ?_⟩
  exact ⟨ℓ,k,κ,u,l,N,m,m₂,z,s,C,V,P,Dw,pn,pm,pp,pb,ph,C,V,E,
    q'.largest,q'.domain,q'.inaccessible,q'.stretch,
    move,hkω,hκ,arity,digits,real,request,queryData,uu,data,elastic',truth,growth,
    Or.inr ⟨ne,hℓn,a₀,b₀,ℓ₀,j,κ₀,u₀,τ,w,d₀,q₀,l,N,B,U,D,
      old₀,oldMove,old₁,oldAnswer,hk,oldArity,hτ,hB,constants,type.pool,exceeds⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限坍缩条件中实际出现 demanding 继续走法

先把旧条件延长到指定编号之后，再统一界住该有限段的所有值、旧域 τ、
短图 s 与固定字母表 A。武丁工厂只生产一次新走法；将其追加后，全部
先前值均位于同一 Vκ，原完整类型和未来合法性一并保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.generic_dense_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ κ₀ u₀ b₀ j k d₀ q₀ l N τ B U D w η Y c R r norm ψ
      a b pending β s a' b' p' F f E : M.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Td_move_d a₀ ℓ₀ j κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (hk : M.SuccessorOf k j) (hτ : M.IsLimitOrdinal τ) (hB : V_d I τ B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (record : Td_record_d I p.ω p.e j Y p.S a b pending β d₀ q₀ l N norm)
    (perm : M.IsSetBijectionFromTo I ψ N N)
    (points : ∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x r ↔ Rd_entry_d j x norm))
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s a' b')
    (appendA : ∀ x, M.mem x a' ↔ M.mem x a ∨ x = pending)
    (appendB : ∀ x, M.mem x b' ↔ M.mem x b ∨ x = p')
    (hτδ : M.mem τ p.δ) (hsX : M.mem s X)
    (space : Fseq_space_d I p.ω X F) (hf : M.mem f F) (hE : M.mem E p.ω) :
    ∃ κ C v u μ A d H m V P r' i q,
      M.mem κ p.δ ∧ V_d I κ C ∧ M.mem v X ∧ Td_move_d v ℓ k κ u ∧
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧
      (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧
      Td_groups_d I p.ω p.e N r' a' b' ∧ M.IsOrdinalAddition I l k k ∧
      M.mem q F ∧ M.MemberSubset f q ∧ M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i v q ∧
      (∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C) ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Td_growth_d hZF p.e p.c p.A n h κ C → Td_aux_d hZF p n h v := by
  obtain ⟨n,hn,fn⟩ := (space f).mp hf
  have on := setup.omega.members_areOrdinals (ZF.modelsKP hZF) n hn
  have oE := setup.omega.members_areOrdinals (ZF.modelsKP hZF) E hE
  obtain ⟨E',succ,hE'⟩ := setup.omega.1.2 E hE
  have fit : ∃ i, M.mem i p.ω ∧ M.mem E i ∧ M.MemberSubset n i := by
    rcases on.trichotomy hZF.1 oE (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) n E) with eq | lt | gt
    · exact ⟨E',hE',succ.predecessor_mem,fun x hx => (succ x).mpr (Or.inl ((eq x).mp hx))⟩
    · exact ⟨E',hE',succ.predecessor_mem,fun x hx => (succ x).mpr (Or.inl (oE.transitive n lt x hx))⟩
    · exact ⟨n,hn,gt,fun _ h => h⟩
  obtain ⟨i,hi,hEi,ni⟩ := fit
  have oi := setup.omega.members_areOrdinals (ZF.modelsKP hZF) i hi
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have trans := v_transitive_l I setup.rank
  have heω := num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨g,fill,fg⟩ := senv_fill_exists_l I hZF fn (trans p.ω hwX p.e heω)
  obtain ⟨f₀,cut⟩ := ZF.exists_restriction hZF I g i
  have ff₀ := cut.isSetFunctionFromTo fg (setup.omega.transitive (ZF.modelsKP hZF) i hi)
  have kept x y (xy : Rd_entry_d x y f) : Rd_entry_d x y f₀ := by
    have hx := fn.input_mem_of_pairMember xy
    exact (cut.2 x y).mpr ⟨ni x hx,(fill.2 x y).mpr
      ⟨setup.omega.transitive (ZF.modelsKP hZF) n hn x hx,Or.inl ⟨hx,xy⟩⟩⟩
  obtain ⟨C₀,hC₀,values,_⟩ := ZF.v_finite_function_l hZF setup.omega setup.limit setup.rank hwX hi ff₀
  -- 同时容纳全部条件值与本游戏的真实参数；固定 A 不被旧辅助图替代。
  obtain ⟨S₀,hS₀,pair₀⟩ := sc_v_pair_l (ZF.modelsKP hZF) setup.limit setup.rank s p.A hsX setup.letters
  obtain ⟨T₀,hT₀,pair₁⟩ := sc_v_pair_l (ZF.modelsKP hZF) setup.limit setup.rank S₀ τ hS₀
    (ZF.v_ordinal_mem_l I hZF setup.rank hτδ)
  obtain ⟨Z₀,hZ₀,cZ,tZ⟩ := v_joint_bound_l I setup.rank hC₀ hT₀
  obtain ⟨χ,Z,hχ,hZ,zz⟩ := (ZF.v_unfold_l I hZF setup.rank Z₀).mp hZ₀
  have transZ := v_transitive_l I hZ
  have hS₀Z := zz S₀ (tZ S₀ ((pair₁ S₀).mpr (Or.inl rfl)))
  have hτZ := zz τ (tZ τ ((pair₁ τ).mpr (Or.inr rfl)))
  have hτχ := ZF.v_ordinal_height_l hZF hZ hτ.1 hτZ
  obtain ⟨κ,C,v,u,μ,A,d,H,m,V,P,r',above,hκ,hC,hv,move,hμ,hA,lower,hm,cv,full,first,last,groups,twice,legal⟩ :=
    setup.generic_continue_l hZFC hd hℓ oldMove oldAnswer hk hτ hB constants hY model type record perm points
      bound height node appendA appendB hχ ((v_ordinal_l I hZ).transitive τ hτχ) hZ
      (transZ S₀ hS₀Z s ((pair₀ s).mpr (Or.inl rfl)))
      (transZ S₀ hS₀Z p.A ((pair₀ p.A).mpr (Or.inr rfl)))
  obtain ⟨i',si,hi'⟩ := setup.omega.1.2 i hi
  obtain ⟨q,fq,old,value⟩ := tt_column_append_l hZF oi si ff₀ hv
  have sub : M.MemberSubset f q := by
    intro z hz
    obtain ⟨j,y,pair⟩ := fn.1.1 z hz
    have jy : Rd_entry_d j y f := ⟨z,pair,hz⟩
    obtain ⟨z',cp,hz'⟩ := (old j y (ni j (fn.input_mem_of_pairMember jy))).mpr (kept j y jy)
    exact (kpair_unique_l M hZF.1 pair cp).symm ▸ hz'
  have before j y (hj : M.mem j i) (jy : Rd_entry_d j y q) : M.mem y C :=
    ZF.v_mono_l I hZF hZ hC ((v_ordinal_l I hC).transitive χ above) y
      (zz y (cZ y (values.output_mem_of_pairMember ((old j y hj).mp jy))))
  exact ⟨κ,C,v,u,μ,A,d,H,m,V,P,r',i,q,hκ,hC,hv,move,hμ,hA,lower,hm,cv,full,first,last,groups,twice,
    (space q).mpr ⟨i',hi',fq⟩,sub,hEi,hi,value,before,legal⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型内的稠密集及实际泛型命中

双图继续要求由同一个有限公式定义；实际条件延长证明稠密性，再直接
调用原泛型滤子的 meets，不把请求公平性作为额外参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem td_dense_hit_defined_l (hZF : M.Models ZF) (p : Tg_params_d M.Domain)
    (ℓ s k N β a b v₀ w₀ E : M.Domain) :
    Defined_d M (Td_dense_hit_d hZF p ℓ s k N β a b v₀ w₀ E) := by
  let ρ : Env M 22 := ⟨fun i => [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,
    ℓ,s,k,N,β,a,b,v₀,w₀,E].get i,fun _ => p.ω⟩
  let a : Tg_params_d (Term 23) := ⟨.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,
    .bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩
  let φ : UnarySchema 22 := {
    body := td_dense_hit_m a (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
      (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest
    freeClosed := by
      simp -implicitDefEqProofs [td_dense_hit_m,Definitional.Formula.FreeClosed,a]
      apply td_generic_target_closed_l <;>
        simp -implicitDefEqProofs [Tg_params_d.closed_l,Tg_params_d.map_l] }
  refine ⟨22,φ,ρ,fun q => ?_⟩
  exact td_dense_hit_sat_l hZF (ρ.push q) a (.bound 13) (.bound 14) (.bound 15) (.bound 16)
    (.bound 17) (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.generic_meet_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ κ₀ u₀ b₀ j k d₀ q₀ l N τ B U D w η Y c R r norm ψ
      a b pending β s a' b' p' F Q E : M.Domain} {G : M.Domain → Prop}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Td_move_d a₀ ℓ₀ j κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (hk : M.SuccessorOf k j) (hτ : M.IsLimitOrdinal τ) (hB : V_d I τ B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (record : Td_record_d I p.ω p.e j Y p.S a b pending β d₀ q₀ l N norm)
    (perm : M.IsSetBijectionFromTo I ψ N N)
    (points : ∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x r ↔ Rd_entry_d j x norm))
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s a' b')
    (appendA : ∀ x, M.mem x a' ↔ M.mem x a ∨ x = pending)
    (appendB : ∀ x, M.mem x b' ↔ M.mem x b ∨ x = p')
    (hτδ : M.mem τ p.δ) (hsX : M.mem s X) (space : Fseq_space_d I p.ω X F)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F G) (hE : M.mem E p.ω) :
    ∃ q, G q ∧ Td_dense_hit_d hZF p ℓ s k N β a' b' a₀ b₀ E q := by
  obtain ⟨f,hf⟩ := generic.inhabited
  apply generic_pick_l hZF generic (td_dense_hit_defined_l hZF p ℓ s k N β a' b' a₀ b₀ E) hf
  intro q hq
  obtain ⟨κ,C,v,u,μ,A,d,H,m,V,P,r',i,q',hκ,hC,hv,move,hμ,hA,lower,hm,cv,full,first,last,
    groups,twice,hq',sub,hEi,hi,iv,before,legal⟩ :=
    setup.generic_dense_l hZFC hd hℓ oldMove oldAnswer hk hτ hB constants hY model type record perm points
      bound height node appendA appendB hτδ hsX space hq.1 hE
  exact ⟨q',subset_below_l hZF order hq.1 hq' sub,
    κ,C,v,u,i,⟨hκ,hC,move,⟨μ,A,d,H,m,V,P,r',hμ,hA,lower,hm,cv,full,first,last,groups,
      l,twice,record.height_end⟩,legal⟩,
    hEi,hi,iv,before⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双图继续请求在首次越界时的实际捕获

此前的原请求属于目标 Vκ，其类型域因而严格小于 κ。目标请求满足全部
原规则，最小合法编号不可能越过它；所有规则判断仍在原模型中进行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Td_move_d.domain_bound_l {a ℓ k τ u κ C : M.Domain}
    (data : Td_move_d a ℓ k τ u) (hC : V_d I κ C) (hτ : M.IsOrdinal τ) (ha : M.mem a C) : M.mem τ κ :=
  ZF.v_ordinal_height_l hM hC hτ ((show Rd_quad_d a ℓ k τ u from data).mem_l (v_transitive_l I hC) ha).2.2.1

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_generic_target_d.capture_l {p : Tg_params_d M.Domain}
    {X F L ℓ s k m β a b v₀ w₀ κ C v u q d i n z h r j v' ℓ' k' τ u' : M.Domain}
    {f index prior : N.Domain}
    (target : Td_generic_target_d hM p ℓ s k m β a b v₀ w₀ κ C v u)
    (hw : M.IsOmega p.ω) (hw' : N.IsOmega (e p.ω)) (histories : Td_histories_d hM p X F L)
    (fq : Fn0_d d X q) (dw : M.mem d p.ω) (iv : Rd_entry_d i v q) (iw : M.mem i p.ω)
    (before : ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C)
    (ff : N.IsSetFunction J f) (kept : ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) f)
    (scan : Cg_scan_d hN (e p.ω) (e L) f (e h) index) (cross : ¬ N.mem index (e i))
    (lastIndex : Rd_entry_d prior (e v') f) (below : N.mem prior (e i))
    (old : Td_move_d v' ℓ' k' τ u') (oτ : M.IsOrdinal τ)
    (succ : M.SuccessorOf n j) (oldEvent : Tg_event_d I p.c j p.e h v')
    (hn : M.mem n p.ω) (hr : M.mem r p.ω) (fn : Fn0_d r X h)
    (div : M.IsOrdinalDivision I r p.c n p.e)
    (digits : Tg_digits_d hM p.c p.b n p.A h z) (real : M.IsRestrictionOf I s z k)
    (hℓ : M.mem ℓ n) (event₀ : Tg_event_d I p.c ℓ p.e h v₀) (event₁ : Tg_event_d I p.c ℓ p.a h w₀) :
    index = e i ∧ Rd_entry_d index (e v) f ∧ Td_aux_d hM p n h v := by
  obtain ⟨j₀,hj₀,eq⟩ := (he i prior).mp below
  have fq' := fn0_function_l (ZF.modelsKP hM) fq
  have hid := fq'.input_mem_of_pairMember iv
  have od := hw.members_areOrdinals (ZF.modelsKP hM) d dw
  obtain ⟨y,_,jy⟩ := fq'.2.2 j₀ (od.transitive i hid j₀ hj₀)
  have same : e v' = e y := ff.2 (e j₀) (e v') (e y) (eq.symm ▸ lastIndex) (kept j₀ y jy)
  have bound := old.domain_bound_l hM target.2.1 oτ ((hi same).symm ▸ before j₀ y hj₀ jy)
  have aux := target.2.2.2.2 n h z digits real hℓ event₀ event₁
    (Or.inr ⟨j,v',ℓ',k',τ,u',succ,oldEvent,old,bound⟩)
  have legal := histories.admit_l hM hw hr hn fn div (fq.bound_l iv).2 aux
  have hh := (histories.1 h).mpr ⟨r,hr,fn0_function_l (ZF.modelsKP hM) fn⟩
  have legal' := (image_admit_l hM hN e hi he hw hw' histories.1
    (fun t ht => ((histories.2 t).mp ht).1) hh).mp legal
  have eq := (scan.le_l hN hw' ((image_member_l e hi he).mpr iw) (kept i v iv) legal').elim
    (fun lt => (cross lt).elim) (fun eq => eq)
  exact ⟨eq,eq.symm ▸ kept i v iv,aux⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏地模型中的实际轮关系集合

把原有限状态公式分离为真实关系 D。扩张中的归纳只读取 D 的规范像，
不在扩张的分离公理中使用任意地模型谓词。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_round_set_l (p : Tg_params_d M.Domain) (X R : M.Domain) :
    ∃ D, M.IsSetRelation I D ∧ ∀ n h, Rd_entry_d n h D ↔ M.mem h R ∧ Td_ready_d hZF p X n h := by
  obtain ⟨C, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) p.ω R
  let ρ : Env M 8 := ⟨fun i => [p.ω, p.e, p.c, p.b, p.δ, p.A, X, R].get i, fun _ => p.ω⟩
  let φ : BinarySchema 8 := {
    body := .conj (.mem .newest (.bound 9))
      (td_ready_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest) }
  have sat n h : φ.denote ρ n h ↔ M.mem h R ∧ Td_ready_d hZF p X n h := by
    have h := td_ready_sat_l hZF ((ρ.push n).push h)
      (⟨.bound 2, .bound 3, .bound 3, .bound 5, .bound 4, .bound 6, .bound 7,
        .bound 3, .bound 3, .bound 3, .bound 3, .bound 3⟩ : Tg_params_d (Term 10)) (.bound 8) (.bound 1) .newest
    exact and_congr Iff.rfl h
  obtain ⟨D, rel, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨D, rel.1, fun n h => (read n h).trans ?_⟩
  exact ⟨fun h => (sat n _).mp h.2.2, fun h =>
    ⟨(union n).mpr (Or.inl h.2.1), (union _).mpr (Or.inr h.1), (sat n _).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏中最小编号响应的真实地状态

枚举满射与地模型重置走法保证最小合法编号存在。三次追加均为旧有限历史，
因而可回拉到原 I 策略的控制集合；原类型规则始终只在地模型中求值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

omit hi in
theorem Td_move_d.image_l {a ℓ k κ u : M.Domain} (data : Td_move_d a ℓ k κ u) :
    Td_move_d (e a) (e ℓ) (e k) (e κ) (e u) := by
  obtain ⟨v, pair₀, w, pair₁, pair₂⟩ := data
  exact ⟨e v, image_kpair_l e he pair₀, e w, image_kpair_l e he pair₁, image_kpair_l e he pair₂⟩

theorem Td_ready_d.generic_step_l {p : Tg_params_d M.Domain} {X F L G O σ R n m h : M.Domain}
    {g K D T x q t : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ready : Td_ready_d hM p X n h)
    (hh : M.mem h R) (succ : M.SuccessorOf m n) (hx : N.mem x (e p.A))
    (pair : (J).Codes q (e h) x) (qt : Rd_entry_d q t T) :
    ∃ t₀ i a, e t₀ = t ∧ M.mem t₀ R ∧ Td_ready_d hM p X m t₀ ∧ Td_aux_d hM p n h a ∧ Tg_event_d I p.c n p.e t₀ a ∧
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) g ∧ Cg_scan_d hN (e p.ω) (e L) g (e h) i ∧
      ∃ z y, Fseq_end_d J (e p.ω) t z y ∧ N.mem y (e p.A) ∧ Tg_event_d J (e p.c) (e n) (e p.b) t y ∧
        (¬ Gm_even_d J (e p.ω) (e n) → y = x) ∧
        ∃ h₁ b, M.IsSetFunction I h₁ ∧ Td_answer_d hM p n h₁ b ∧ Tg_event_d I p.c n p.e h₁ a ∧ Tg_event_d I p.c n p.a t₀ b := by
  have hhF := ((control.legal h).mp ((control.positions h).mp hh).1).1
  have legalImage (a : M.Domain) := image_admit_l hM hN e hi he (a := a) setup.omega hw histories.1
    (fun s hs => ((histories.2 s).mp hs).1) hhF
  obtain ⟨a₀, ha₀, aux₀⟩ := setup.ready_move_l hZFC hd root ready
  have current := ready
  obtain ⟨_, l, z, hl, fh, div, _⟩ := current
  have admissible := histories.admit_l hM setup.omega hl ready.1 fh div ha₀ aux₀
  obtain ⟨j, hj, ja₀⟩ := surj (e a₀) ((image_member_l e hi he).mpr ha₀)
  obtain ⟨i, a, h₁, w, h₂, l₂, y, ki, ga, h₁F, e₁, sw, h₂F, e₂, fh₂, own, tF, e₃⟩ := c.step (e h) x q t pair qt
  have scan := c.least (e h) i ki ⟨j, e a₀, hj, ja₀, (legalImage a₀).mp admissible⟩
  obtain ⟨a', ga', legal⟩ := scan.2.1
  have eq := (fn0_function_l (ZF.modelsKP hN) c.enumeration).1.2 i a' a ga' ga; subst a'
  obtain ⟨a₁, ha₁, eq⟩ := (he X a).mp (c.enumeration.bound_l ga).2; subst a
  obtain ⟨s₁, hs₁, eq⟩ := (he F h₁).mp h₁F; subst h₁
  obtain ⟨s₂, hs₂, eq⟩ := (he F h₂).mp h₂F; subst h₂
  obtain ⟨s₃, hs₃, eq⟩ := (he F t).mp tF; subst t
  obtain ⟨w₀, hw₀, eq⟩ := (he X w).mp (c.strategy.bound_l sw).2; subst w
  obtain ⟨k₂, hk₂, fs₂⟩ := (histories.1 s₂).mp hs₂
  have fs₂' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs₂
  have eq := fh₂.domain_eq_l hN.1 (fn0_of_function_l (ZF.modelsKP hN) fs₂'); subst l₂
  obtain ⟨k₃, hk₃, fs₃⟩ := (histories.1 s₃).mp hs₃
  have fs₃' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs₃
  obtain ⟨d, b, dec⟩ := e₃
  have eq := dec.prefix_sequence.2.2.2.eq hN.1 fs₂'.2.1
  have last : Rd_entry_d (e k₂) y (e s₃) := eq ▸ dec.last_value
  obtain ⟨y₀, hy₀, eqy⟩ := (he X y).mp (fs₃'.output_mem_of_pairMember last); subst y
  have end₁ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₁ hhF).mpr e₁
  have end₂ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₂ hs₁).mpr e₂
  have end₃ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₃ hs₂).mpr ⟨d, b, dec⟩
  have value := (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 s₁ w₀ σ).mpr sw
  have digit : (M.mem k₂ O ∧ Rd_entry_d s₂ y₀ σ) ∨ (¬ M.mem k₂ O ∧ M.mem y₀ p.A) := by
    rcases own with ⟨turn, val⟩ | ⟨turn, val⟩
    · exact Or.inl ⟨(image_member_l e hi he).mp turn,
        (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 s₂ y₀ σ).mpr val⟩
    · exact Or.inr ⟨fun h => turn ((image_member_l e hi he).mpr h),
        (image_member_l e hi he).mp (val.symm ▸ hx)⟩
  obtain ⟨next, state, aux, event, hyA, j, fj, clock, answer, ae, be⟩ := ready.advance_l hZFC setup histories owner control hh succ hs₁ hs₂ hs₃
    end₁ end₂ end₃ ((legalImage a₁).mpr legal) value ⟨k₂, fn0_of_function_l (ZF.modelsKP hM) fs₂, digit⟩
  have eqj := fj.domain_eq_l hM.1 (fn0_of_function_l (ZF.modelsKP hM) fs₂); subst j
  obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three ready.1
  refine ⟨s₃, i, a₁, rfl, next, state, aux, event, ki, ga, scan, e s₂, e y₀, ⟨d, b, dec⟩,
    (image_member_l e hi he).mpr hyA,
    ⟨e k₂, image_nat_div_l hM hN e hi he setup.omega hc ready.1 clock, last⟩, ?_, s₁, w₀, ?_, answer, ae, be⟩
  · intro odd
    have notOwn : ¬ N.mem (e k₂) (e O) := by
      intro yes
      have phase := (owner.read_l hM (setup.omega.isOrdinal (ZF.modelsKP hM)) (setup.omega.members_areOrdinals (ZF.modelsKP hM) p.c hc)
        ⟨p.b, setup.three.predecessor_mem⟩ hk₂ ready.1 clock).mp ((image_member_l e hi he).mp yes)
      rcases phase with eq | even
      · exact KP.mem_irrefl_d (ZF.modelsKP hM) p.a (eq ▸ setup.two.predecessor_mem)
      · exact odd ((image_even_l hM hN e hi he setup.omega).mp even.2)
    exact own.elim (fun h => (notOwn h.1).elim) And.right
  · obtain ⟨_, _, fs₁⟩ := (histories.1 s₁).mp hs₁
    exact fs₁.1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏在扩张内部的最小请求递归

对地状态集合的像作扩张内部 ω 归纳。每个递归状态都对应真实地有限历史，
且仍受原 I 获胜策略控制；没有借用外部标准 ω 或地模型的外部良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_setup_d.generic_states_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∀ n h, Rd_entry_d n h H → ∃ n₀ h₀, e n₀ = n ∧ e h₀ = h ∧ M.mem h₀ R ∧ Td_ready_d hM p X n₀ h₀ := by
  obtain ⟨B, rel, read⟩ := td_round_set_l hM p X R
  let ρ : Env N 2 := ⟨fun i => [H, e B].get i, fun _ => H⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ h,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ, h, ⌜(.bound 1 : Term 3)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ, h, ⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ h, Rd_entry_d n h H → Rd_entry_d n h (e B) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hN.1, Definitional.Term.eval_weaken]; rfl
  have empty : ∀ x, ¬ N.mem x (e p.e) := fun x hx => (he p.e x).mp hx |>.elim fun y hy => setup.empty y hy.1
  have all : ∀ n, N.mem n (e p.ω) → ∀ h, Rd_entry_d n h H → Rd_entry_d n h (e B) := by
    apply hw.induction
    · obtain ⟨C, sep⟩ := ZF.separation_exists_d hN φ ρ (e p.ω)
      exact ⟨C, fun n => (sep n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz h zh
      have eq := hN.1.eq_of_same_members z (e p.e) (fun x => iff_of_false (hz x) (empty x)); subst z
      have eq := (fn0_function_l (ZF.modelsKP hN) run.1).1.2 (e p.e) h (e p.e) zh (run.2.1 (e p.e) empty); subst h
      exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 p.e p.e B).mp
        ((read p.e p.e).mpr ⟨control.root, setup.ready_empty_l hZFC⟩)
    · intro n hn ih m succ h mh
      obtain ⟨s, _, ns⟩ := run.1.2.1 n hn
      obtain ⟨n₀, s₀, state, en, es⟩ := (image_entries_l e he rel n s).mp (ih s ns)
      subst n s
      obtain ⟨hs₀, ready⟩ := (read n₀ s₀).mp state
      obtain ⟨m₀, sm₀, hm₀⟩ := setup.omega.1.2 n₀ ready.1
      have eq := (image_successor_l (hEN := hN.1) e hi he hM.1 sm₀).eq hN.1 succ; subst m
      obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e s₀) h succ ns mh
      have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
        (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
      obtain ⟨t₀, _, _, et, ht, next, _⟩ := ready.generic_step_l hZFC hN e hi he setup hd root histories owner control
        hw c surj hs₀ sm₀ hx pair qt
      exact et ▸ (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 m₀ t₀ B).mp ((read m₀ t₀).mpr ⟨ht, next⟩)
  intro n h nh
  obtain ⟨n₀, h₀, nh₀, en, eh⟩ := (image_entries_l e he rel n h).mp (all n (run.1.bound_l nh).1 h nh)
  exact ⟨n₀, h₀, en, eh, (read n₀ h₀).mp nh₀⟩

theorem Td_setup_d.generic_round_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H n : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) (hn : N.mem n (e p.ω)) :
    ∃ n₀ m₀ h₀ t₀ a₀ i, e n₀ = n ∧ M.SuccessorOf m₀ n₀ ∧ M.mem n₀ p.ω ∧
      Rd_entry_d n (e h₀) H ∧ Rd_entry_d (e m₀) (e t₀) H ∧ M.IsSetFunction I h₀ ∧
      Td_aux_d hM p n₀ h₀ a₀ ∧ Tg_event_d I p.c n₀ p.e t₀ a₀ ∧
      Rd_entry_d (e h₀) i K ∧ Rd_entry_d i (e a₀) g ∧ Cg_scan_d hN (e p.ω) (e L) g (e h₀) i ∧
      ∃ h₁ b, M.IsSetFunction I h₁ ∧ Td_answer_d hM p n₀ h₁ b ∧ Tg_event_d I p.c n₀ p.e h₁ a₀ ∧ Tg_event_d I p.c n₀ p.a t₀ b := by
  obtain ⟨h, _, nh⟩ := run.1.2.1 n hn
  obtain ⟨n₀, h₀, en, eh, hh, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run n h nh
  subst n h
  obtain ⟨m₀, succ, hm₀⟩ := setup.omega.1.2 n₀ ready.1
  obtain ⟨t, _, mt⟩ := run.1.2.1 (e m₀) ((image_member_l e hi he).mpr hm₀)
  obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e h₀) t
    (image_successor_l (hEN := hN.1) e hi he hM.1 succ) nh mt
  have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
    (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
  obtain ⟨t₀, i, a₀, et, _, _, aux, event, ki, ga, scan, _, _, _, _, _, _, reply⟩ := ready.generic_step_l hZFC hN e hi he setup hd root histories owner control hw c surj hh succ hx pair qt
  obtain ⟨_, _, fh⟩ := (histories.1 h₀).mp (((control.legal h₀).mp ((control.positions h₀).mp hh).1).1)
  exact ⟨n₀, m₀, h₀, t₀, a₀, i, rfl, succ, ready.1, nh, et.symm ▸ mt, fh.1, aux, event, ki, ga, scan, reply⟩

/-- 从原 I 获胜策略与实际枚举直接构造原有限历史策略；全部输入递归都保持地状态。 -/
theorem Td_game_d.generic_strategy_l {p : Tg_params_d M.Domain} {X F L G O B W C Z v σ a : M.Domain}
    {g S : N.Domain} (game : Td_game_d hZFC p X F L G O B W C Z v)
    (hd : Woodin_d I p.δ) (root : M.mem p.e p.S) (win : Cg_win_d I true p.ω X F O B W σ)
    (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω)) (fg : Fn0_d (e p.ω) (e X) g)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (space : Fseq_space_d J (e p.ω) (e p.A) S) :
    ∃ R K D T τ, Cg_control_d I true p.ω p.e X F L G O σ R ∧
      Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T ∧ Fn0_d S (e p.A) τ ∧
      (∀ s y, Rd_entry_d s y τ ↔ N.mem s S ∧ Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y) ∧
      ∀ f, Fn0_d (e p.ω) (e p.A) f → ∃ H, Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H ∧
        ∀ n h, Rd_entry_d n h H → ∃ n₀ h₀, e n₀ = n ∧ e h₀ = h ∧ M.mem h₀ R ∧ Td_ready_d hM p X n₀ h₀ := by
  obtain ⟨R, control⟩ := cg_control_l hM game.setup.omega game.setup.empty game.histories.1 game.legal
    (game.empty_l hZFC) game.runs game.payoff win
  have empty : ∀ x, ¬ N.mem x (e p.e) := fun x hx => (he p.e x).mp hx |>.elim fun y hy => game.setup.empty y hy.1
  have imageSpace := image_fseq_l hM hN e hi he game.setup.omega hw game.histories.1
  have fs := fn0_of_function_l (ZF.modelsKP hN)
    (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) win.1))
  have sub : N.MemberSubset (e p.A) (e X) := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (he p.A x).mp hx
    exact (image_member_l e hi he).mpr (v_transitive_l I game.setup.rank p.A game.setup.letters x₀ hx₀)
  obtain ⟨K, D, T, scan⟩ := cg_scan_table_l hN hw empty imageSpace fg fs sub
  have ha' := (image_member_l e hi he).mpr ha
  obtain ⟨τ, fτ, answer⟩ := scan.strategy_l hN hw empty ha' space
  refine ⟨R, K, D, T, τ, control, scan, fτ, answer, fun f ff => ?_⟩
  have heF := (imageSpace (e p.e)).mpr ⟨e p.e, num_mem_l hN.1 hw (show Num_d 0 (e p.e) from empty), ds_empty_fun_l J empty⟩
  obtain ⟨H, run⟩ := gi_exists_l hN (b := false) hw scan.product scan.response heF ha'
    (fn0_function_l (ZF.modelsKP hN) ff).1 (fun _ _ entry => (ff.bound_l entry).2)
  exact ⟨H, run, game.setup.generic_states_l hZFC hN e hi he hd root game.histories game.owner control ha hw scan surj ff run⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际最小请求编号的无界性与首达时刻

所选编号可以回落，但请求的参数域逐轮严格增长，因此编号不能重复。
参数域图在扩张中由真实公式构造；内部 ω 单射不可能有有限上界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_setup_d.generic_indices_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∃ E, N.IsSetInjectionFromTo J E (e p.ω) (e p.ω) ∧
      (∀ n i, Rd_entry_d n i E ↔ N.mem n (e p.ω) ∧ ∃ h, Rd_entry_d n h H ∧ Rd_entry_d h i K) ∧
      ∀ i, N.mem i (e p.ω) → ∃ n v, N.mem n (e p.ω) ∧ Rd_entry_d n v E ∧ ¬ N.mem v i ∧
        ∀ m w, N.mem m n → Rd_entry_d m w E → N.mem w i := by
  have hf := fn0_function_l (ZF.modelsKP hN) run.1
  have gf := fn0_function_l (ZF.modelsKP hN) c.enumeration
  obtain ⟨E, ef, er⟩ := ZF.exists_compositionFunction hN J hf (fn0_function_l (ZF.modelsKP hN) c.indices)
  have stage (n : N.Domain) (hn : N.mem n (e p.ω)) :
      ∃ n₀ m₀ h₀ t₀ a₀ i ℓ k κ u B, e n₀ = n ∧ M.SuccessorOf m₀ n₀ ∧ M.mem n₀ p.ω ∧
        Rd_entry_d n (e h₀) H ∧ Rd_entry_d (e m₀) (e t₀) H ∧ M.IsSetFunction I h₀ ∧
        Td_move_d a₀ ℓ k κ u ∧ M.mem κ p.δ ∧ Td_growth_d hM p.e p.c p.A n₀ h₀ κ B ∧
        Tg_event_d I p.c n₀ p.e t₀ a₀ ∧ Rd_entry_d n i E ∧ Rd_entry_d i (e a₀) g := by
    obtain ⟨n₀, m₀, h₀, t₀, a₀, i, en, succ, hn₀, nh, mt, fh₀, aux, event, ki, ga, _⟩ :=
      setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run hn
    obtain ⟨ℓ, k, κ, u, _, _, _, _, _, _, B, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      data, _, hκ, _, _, _, _, _, _, _, _, _, growth, _⟩ := aux
    exact ⟨n₀, m₀, h₀, t₀, a₀, i, ℓ, k, κ, u, B, en, succ, hn₀, nh, mt, fh₀, data, hκ, growth,
      event, (er n i).mpr ⟨hn, e h₀, nh, ki⟩, ga⟩
  let ρ : Env N 2 := ⟨fun i => [E, g].get i, fun _ => g⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ i a ℓ k u,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ, i, ⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(i, a, ⌜(.bound 3 : Term 4)⌝ₛ) ∧ ⌜td_move_m⌝ₚ(a, ℓ, k, ⌜(.newest : Term 4)⌝ₛ, u)⟫ }
  have sat n κ : φ.denote ρ n κ ↔ ∃ i a ℓ k u, Rd_entry_d n i E ∧ Rd_entry_d i a g ∧ Td_move_d a ℓ k κ u := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hN.1, td_move_sat_l hN.1, Definitional.Term.eval_weaken]; rfl
  have align {n κ κ' i b ℓ k u : N.Domain} (ni : Rd_entry_d n i E) (ib : Rd_entry_d i b g)
      (data : Td_move_d b ℓ k κ' u) (value : φ.denote ρ n κ) : κ = κ' := by
    obtain ⟨j, b', ℓ', k', u', nj, jb, other⟩ := (sat n κ).mp value
    have eq := ef.1.2 n j i nj ni; subst j
    have eq := gf.1.2 i b' b jb ib; subst b'
    exact (other.unique_l data).2.2.1
  obtain ⟨P, pf, pr⟩ := ZF.exists_setFunctionFromTo_of_denote hN J φ ρ (source := e p.ω) (target := e p.δ) (by
    intro n hn
    obtain ⟨_, _, _, _, b, i, ℓ, k, κ, u, _, _, _, _, _, _, _, data, _, _, _, ni, ib⟩ := stage n hn
    exact ⟨e κ, (sat n (e κ)).mpr ⟨i, e b, e ℓ, e k, e u, ni, ib, data.image_l e he⟩⟩) (by
    intro n _ κ ν hκ hν
    obtain ⟨i, b, ℓ, k, u, ni, ib, data⟩ := (sat n ν).mp hν
    exact align ni ib data hκ) (by
    intro n κ hn val
    obtain ⟨_, _, _, _, b, i, ℓ, k, κ₀, u, _, _, _, _, _, _, _, data, hκ₀, _, _, ni, ib⟩ := stage n hn
    exact (align ni ib (data.image_l e he) val).symm ▸ (image_member_l e hi he).mpr hκ₀)
  have next {n m κ ν : N.Domain} (succ : N.SuccessorOf m n) (nk : Rd_entry_d n κ P) (ml : Rd_entry_d m ν P) : N.mem κ ν := by
    obtain ⟨n₀, m₀, h₀, t₀, b₀, i₀, ℓ₀, k₀, κ₀, u₀, B₀, en, sm, hn₀, nh, mt, _, data₀, _, _, ev₀, ni₀, ib₀⟩ :=
      stage n (pf.input_mem_of_pairMember nk)
    obtain ⟨n₁, m₁, h₁, t₁, b₁, i₁, ℓ₁, k₁, κ₁, u₁, B₁, em, _, _, mh, _, fh₁, data₁, _, growth, _, mi₁, ib₁⟩ :=
      stage m (pf.input_mem_of_pairMember ml)
    have ek := align ni₀ ib₀ (data₀.image_l e he) ((pr n κ).mp nk).2
    have el := align mi₁ ib₁ (data₁.image_l e he) ((pr m ν).mp ml).2
    subst n m
    have eq := hi ((image_successor_l (hEN := hN.1) e hi he hM.1 sm).eq hN.1 succ); subst n₁
    have eq := hi (hf.1.2 (e m₀) (e t₀) (e h₁) mt mh); subst h₁
    have lt : M.mem κ₀ κ₁ := by
      rcases growth with ⟨eq, _⟩ | ⟨j, b, ℓ, k, τ, u, sj, ev, data, below⟩
      · exact (setup.empty n₀ (eq ▸ sm.predecessor_mem)).elim
      · have eq := sm.predecessor_eq hM.1 (setup.omega.members_areOrdinals (ZF.modelsKP hM) n₀ hn₀) sj; subst j
        obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three hn₀
        have eq := ev.unique_l hM (setup.omega.members_areOrdinals (ZF.modelsKP hM) p.c hc) fh₁ ev₀; subst b
        exact (data.unique_l data₀).2.2.1 ▸ below
    exact ek.symm ▸ el.symm ▸ (image_member_l e hi he).mpr lt
  let δenv : Env M 1 := ⟨fun _ => p.δ, fun _ => p.δ⟩
  have oδ : N.IsOrdinal (e p.δ) := (KP.ord0_sat_l (ZF.modelsKP hN) (image_env_l e δenv) .newest).mp
    ((delta0_image_l e hi he (KP.ord0_delta_l .newest) δenv).mp
      ((KP.ord0_sat_l (ZF.modelsKP hM) δenv .newest).mpr setup.limit.1))
  let μ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  have chain := ZF.rel_chain_l J hN μ ⟨Fin.elim0, fun _ => g⟩ hw pf
    (fun x y z _ _ hz xy yz => (oδ.mem hz).transitive y yz x xy) (fun _ _ _ _ succ nk ml => next succ nk ml)
  have inj : N.IsSetInjectionFromTo J E (e p.ω) (e p.ω) := by
    refine ⟨ef, fun n m i ni mi => ?_⟩
    obtain ⟨κ, _, nk⟩ := pf.2.2 n (ef.input_mem_of_pairMember ni)
    obtain ⟨ν, _, ml⟩ := pf.2.2 m (ef.input_mem_of_pairMember mi)
    obtain ⟨j, b, ℓ, k, u, nj, jb, data⟩ := (sat n κ).mp ((pr n κ).mp nk).2
    have eq := ef.1.2 n j i nj ni; subst j
    have eq : ν = κ := align mi jb data ((pr m ν).mp ml).2; subst ν
    rcases (hw.isOrdinal (ZF.modelsKP hN)).wellOrder.linear.compare n (ef.input_mem_of_pairMember ni) m (ef.input_mem_of_pairMember mi) with eq | lt | gt
    · exact hN.1.eq_of_same_members n m eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain n m κ κ lt nk ml)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain m n κ κ gt ml nk)).elim
  exact ⟨E, inj, er, fun i hi => ZF.omega_first_crossing_l hN hw inj hi⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 泛型策略与同运行的原字母坐标一致

在扩张内部对实际纯公式作 ω 归纳：偶数轮由有限前缀因果性读取所构造的
I 策略，奇数轮读取对手输入。这里仅搬运有限图和算术，不重解释旧完整类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Td_setup_d.generic_play_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g B D T f H τ : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d K p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hZ p X F L) (owner : Tg_owner_d hZ p.ω p.c p.a p.b O)
    (control : Cg_control_d K true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g B D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∀ n h z, Rd_entry_d n h H → Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
  classical
  have fn := fn0_function_l (ZF.modelsKP hN) ff
  have heω := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three heω
  have oc := image_ord_l hZ hN e hi he (setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc)
  let ρ : Env N 5 := ⟨fun i => [e p.c, e p.b, e p.A, H, f].get i, fun _ => f⟩
  let φ : UnarySchema 5 := { body := set[6] ⟪∀ h z,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 6)⌝ₛ, h, ⌜(.bound 4 : Term 6)⌝ₛ) →
    ⌜tg_digits_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ, ⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.newest : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ, h, z) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(z, ⌜(.bound 5 : Term 6)⌝ₛ, ⌜(.newest : Term 6)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ h z, Rd_entry_d n h H →
      Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hN.1, tg_digits_sat_l hN, Formula.satisfies_isRestriction_iff J, Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, N.mem n (e p.ω) → ∀ h z, Rd_entry_d n h H →
      Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
    apply hw.induction
    · obtain ⟨C, sep⟩ := ZF.separation_exists_d hN φ ρ (e p.ω)
      exact ⟨C, fun n => (sep n).trans (and_congr_right fun _ => sat n)⟩
    · intro n hn h z _ digits
      exact ⟨(fn0_function_l (ZF.modelsKP hN) digits.1).1.1, fun i y =>
        ⟨fun iy => (hn i (digits.1.bound_l iy).1).elim, fun iy => (hn i iy.1).elim⟩⟩
    · intro n hn ih m succ t z mt dz
      obtain ⟨h, _, nh⟩ := run.1.2.1 n hn
      obtain ⟨n₀, h₀, en, eh, hh, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run n h nh
      subst n h
      obtain ⟨m₀, sm, hm⟩ := setup.omega.1.2 n₀ ready.1
      have eq := (image_successor_l (hEN := hN.1) e hi he hZ.1 sm).eq hN.1 succ; subst m
      have saved := ready
      obtain ⟨hn₀, r, s, hr, fh, _, digits, _⟩ := saved
      have old := digits.image_l hZ hN e hi he setup.omega hc hn₀
        ⟨setup.omega.members_areOrdinals (ZF.modelsKP hZ) r hr, (fn0_function_l (ZF.modelsKP hZ) fh).1, (fn0_function_l (ZF.modelsKP hZ) fh).2.1⟩
      have cut := ih (e h₀) (e s) nh old
      obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e h₀) t succ nh mt
      have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
        (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, z₀, y, endt, hy, event, odd, _⟩ :=
        ready.generic_step_l hZFC hN e hi he setup hd root histories owner control hw c surj hh sm hx pair qt
      obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, _, _, e₂, _, _, _, e₃⟩ := c.step (e h₀) x q t pair qt
      have sub : N.MemberSubset (e h₀) t := fun v hv => e₃.subset_l J v (e₂.subset_l J v (e₁.subset_l J v hv))
      obtain ⟨_, _, ft⟩ := (c.space t).mp (run.1.bound_l mt).2
      obtain ⟨z', endz, dz'⟩ := old.append_l hN hw oc hn succ sub ft.1 hy event
      have eq := dz'.unique_l hN dz; subst z'
      obtain ⟨v, _, nv⟩ := ff.2.1 (e n₀) hn
      have yv : y = v := by
        by_cases even : Gm_even_d J (e p.ω) (e n₀)
        · have xa : x = e a := input.elim (fun h => (h.1 even).elim) And.right
          exact (cg_scan_answer_prefix_l hN hw (fn0_function_l (ZF.modelsKP hN) c.response).1 fn.1 fn.2.1
            run cut nh (xa ▸ pair) qt endt hy (values (e s) v (follows (e n₀) hn even (e s) cut v nv))).symm
        · exact (odd even).trans (input.elim (fun h => fn.1.2 (e n₀) x v h.2 nv)
            (fun h => (h.1 ⟨even, v, nv⟩).elim))
      exact (ds_restrict_iff_l J (fn0_function_l (ZF.modelsKP hN) dz.1) fn.1).mpr
        (ds_append_sub_l J hN.1 (fn0_function_l (ZF.modelsKP hN) old.1) endz
          ((ds_restrict_iff_l J (fn0_function_l (ZF.modelsKP hN) old.1) fn.1).mp cut) (yv.symm ▸ nv))
  exact fun n h z nh dz => all n (run.1.bound_l nh).1 h z nh dz

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双图稠密条件在指定旧轮之后被实际捕获

先自动界定旧轮和所需实数前缀以前的全部编号。任何达到该稠密要求的泛型
有限条件都在首次越界时被选中；旧事件的保持和实数前缀条件由实际递归推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_setup_d.capture_threshold_l {p : Tg_params_d M.Domain}
    {X F L G O σ R a ℓ m h₀ a₀ b₀ s k r β left right : M.Domain} {g K D T f H τ : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H)
    (hℓ : M.mem ℓ p.ω) (hm : M.SuccessorOf m ℓ) (old : Rd_entry_d (e m) (e h₀) H)
    (event₀ : Tg_event_d I p.c ℓ p.e h₀ a₀) (event₁ : Tg_event_d I p.c ℓ p.a h₀ b₀)
    (hk : M.mem k p.ω) (fs : Fn0_d k p.A s) (cut : N.IsRestrictionOf J (e s) f (e k)) :
    ∃ B, M.mem B p.ω ∧ ∀ q, M.mem q F → Td_dense_hit_d hM p ℓ s k r β left right a₀ b₀ B q →
      (∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) →
      ∃ n h a i κ C u, M.mem n p.ω ∧ M.mem ℓ n ∧ Rd_entry_d (e n) (e h) H ∧
        Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) g ∧ Td_generic_target_d hM p ℓ s k r β left right a₀ b₀ κ C a u ∧
        Td_aux_d hM p n h a := by
  have fn := fn0_function_l (ZF.modelsKP hN) c.enumeration
  have hfn := fn0_function_l (ZF.modelsKP hN) run.1
  obtain ⟨E, inj, er, first⟩ := setup.generic_indices_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run
  -- 界住旧轮及所需前缀以前的全部编号，首达该界的轮次必严格晚于二者。
  have max : ∃ d, M.mem d p.ω ∧ (M.mem ℓ d ∨ ℓ = d) ∧ (M.mem k d ∨ k = d) := by
    rcases (setup.omega.isOrdinal (ZF.modelsKP hM)).wellOrder.linear.compare ℓ hℓ k hk with eq | lt | gt
    · exact ⟨k, hk, Or.inr (hM.1.eq_of_same_members ℓ k eq), Or.inr rfl⟩
    · exact ⟨k, hk, Or.inl lt, Or.inr rfl⟩
    · exact ⟨ℓ, hℓ, Or.inr rfl, Or.inl gt⟩
  obtain ⟨d, hdω, ld, kd⟩ := max
  obtain ⟨B, hB, bound⟩ := ZF.omega_prefix_bound_l hN hw inj.1 ((image_member_l e hi he).mpr hdω)
  obtain ⟨B₀, hB₀, eq⟩ := (he p.ω B).mp hB; subst B
  refine ⟨B₀, hB₀, fun q hq hit kept => ?_⟩
  obtain ⟨κ, C, a₁, u, i, target, Bi, hiω, ia, before⟩ := hit
  obtain ⟨n, v, hn, nv, cross, prior⟩ := first (e i) ((image_member_l e hi he).mpr hiω)
  have dn : N.mem (e d) n := by
    rcases (hw.isOrdinal (ZF.modelsKP hN)).wellOrder.linear.compare (e d) ((image_member_l e hi he).mpr hdω) n hn with eq | lt | gt
    · have eq := hN.1.eq_of_same_members (e d) n eq
      exact (cross ((hw.members_areOrdinals (ZF.modelsKP hN) (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inr eq.symm) nv))).elim
    · exact lt
    · exact (cross ((hw.members_areOrdinals (ZF.modelsKP hN) (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inl gt) nv))).elim
  obtain ⟨n₀, m₀, h, t₀, a₂, j, en, _, hn₀, nh, _, _, aux, _, ki, ga, scan, _⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run hn
  subst n
  have dn₀ := (image_member_l e hi he).mp dn
  have on := setup.omega.members_areOrdinals (ZF.modelsKP hM) n₀ hn₀
  have ln : M.mem ℓ n₀ := ld.elim (fun h => on.transitive d dn₀ ℓ h) (fun eq => eq.symm ▸ dn₀)
  have kn : M.mem k n₀ := kd.elim (fun h => on.transitive d dn₀ k h) (fun eq => eq.symm ▸ dn₀)
  have eqv := inj.1.1.2 (e n₀) v j nv ((er (e n₀) j).mpr ⟨hn, e h, nh, ki⟩); subst v
  obtain ⟨j₀, hj₀, sj⟩ := setup.omega.exists_predecessor_of_mem_of_nonempty hM hn₀ ⟨ℓ, ln⟩
  obtain ⟨j₁, m₁, h₁, t₁, a₃, v, ej, sm, _, jh, mt, _, aux₀, ev, kv, gv, _⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr hj₀)
  have eqj := hi ej; subst j₁
  have eqm := sm.eq hM.1 sj; subst m₁
  have eqt := hi (hfn.1.2 (e n₀) (e t₁) (e h) mt nh); subst t₁
  have vi := prior (e j₀) v ((image_member_l e hi he).mpr sj.predecessor_mem)
    ((er (e j₀) v).mpr ⟨(image_member_l e hi he).mpr hj₀, e h₁, jh, kv⟩)
  obtain ⟨ℓ₀,k₀,κ₀,u₀,d₁,q₁,N₁,m₂,x₁,s₁,B₁,U₁,Du₁,Dw₁,pn₁,pm₁,pp₁,pb₁,ph₁,C₁,V₁,E₁,
    g₀,g₁,g₂,g₃,data,_,hκ₀,_⟩ := aux₀
  have hmω := (image_member_l e hi he).mp (run.1.bound_l old).1
  have mn : M.mem m n₀ ∨ m = n₀ := by
    rcases (setup.omega.isOrdinal (ZF.modelsKP hM)).wellOrder.linear.compare m hmω n₀ hn₀ with eq | lt | gt
    · exact Or.inr (hM.1.eq_of_same_members m n₀ eq)
    · exact Or.inl lt
    · rcases (hm n₀).mp gt with lt | eq
      · exact (KP.mem_irrefl_d (ZF.modelsKP hM) ℓ ((setup.omega.members_areOrdinals (ZF.modelsKP hM) ℓ hℓ).transitive n₀ lt ℓ ln)).elim
      · have eq := hM.1.eq_of_same_members n₀ ℓ eq
        exact (KP.mem_irrefl_d (ZF.modelsKP hM) ℓ (eq ▸ ln)).elim
  have sub := (image_subset_iff_l e hi he).mp (c.history_mono_l hN hw run (e m) (e n₀) (e h₀) (e h)
    (mn.elim (fun h => Or.inl ((image_member_l e hi he).mpr h)) (fun eq => Or.inr (congrArg e eq))) old nh)
  have keep {b r : M.Domain} (ev : Tg_event_d I p.c ℓ r h₀ b) : Tg_event_d I p.c ℓ r h b := by
    obtain ⟨j, div, z, code, hz⟩ := ev
    exact ⟨j, div, z, code, sub z hz⟩
  -- 历史包含保留旧请求和回答；真实对局一致性给出捕获所需的实数前缀。
  obtain ⟨n', h', en', eh', _, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run (e n₀) (e h) nh
  have eqn := hi en'; subst n'
  have eqh := hi eh'; subst h'
  obtain ⟨_, z₀, z, hz₀, fh, div, digits, _⟩ := ready
  obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three hn₀
  have imageDigits := digits.image_l hM hN e hi he setup.omega hc hn₀
    ⟨setup.omega.members_areOrdinals (ZF.modelsKP hM) z₀ hz₀, (fn0_function_l (ZF.modelsKP hM) fh).1, (fn0_function_l (ZF.modelsKP hM) fh).2.1⟩
  have real := setup.generic_play_l hN e hi he hZFC hd root histories owner control ha hw c surj ff values follows run (e n₀) (e h) (e z) nh imageDigits
  have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) fs)
  have sz := ds_prefix_mono_l J fs' (fn0_function_l (ZF.modelsKP hN) imageDigits.1).1 cut real
    ((hw.members_areOrdinals (ZF.modelsKP hN) (e n₀) hn).transitive (e k) ((image_member_l e hi he).mpr kn))
  have real₀ := (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fs) (fn0_function_l (ZF.modelsKP hM) digits.1).1).mpr
    ((image_subset_iff_l e hi he).mp sz)
  obtain ⟨d₀, hd₀, fq⟩ := (histories.1 q).mp hq
  have caught := target.capture_l hM hN e hi he setup.omega hw histories (fn0_of_function_l (ZF.modelsKP hM) fq) hd₀ ia hiω before
    fn.1 kept scan cross gv vi data (setup.limit.1.mem hκ₀) sj ev hn₀ hz₀ fh div digits real₀ ln (keep event₀) (keep event₁)
  have eq := hi (fn.1.2 j (e a₂) (e a₁) ga (caught.1.symm ▸ kept i a₁ ia)); subst a₂
  exact ⟨n₀, h, a₁, j, κ, C, u, hn₀, ln, nh, ki, ga, target, caught.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.4：同一反策略下的严格高度矛盾

跟踪原高度表中的实际请求及扩张内同一反策略的有限历史。内部最小高度的
原回答严格下降；同一反策略产生下一节点，原泛型稠密集又实际捕获该节点的
继续类型，得到更小的跟踪高度。不预设无限辅助枝或任何新图的地原像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Td_setup_d.generic_no_counter_l {p : Tg_params_d M.Domain}
    {X F L G O σ R a U₁ U₂ ζ Q : M.Domain} {filter : M.Domain → Prop}
    {g K D T f H τ Vc Fc Lc Gc Jc Bc Wc Oc σc Rc : N.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ)
    (histories : Td_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H)
    (tree : Td_tree_d I p.ω p.A p.S) (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem ζ U₁)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F filter)
    (origin : ∀ q, filter q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g)
    (counter : Dg_counter_d hN (e p.ω) (e U₁) (e U₂) f (e p.S) Vc Fc Lc Gc Jc Bc Wc Oc)
    (counterControl : Cg_control_d J true (e p.ω) (e p.e) Vc Fc Lc Gc Jc σc Rc) : False := by
  obtain ⟨p₀,cp₀⟩ := (I).total p.e ζ
  have start : Td_pending_d I p.ω p.A p.e p.S p₀ := ⟨tree,ζ,cp₀,(alphabet.1 ζ).mp chosen⟩
  have root := start.root_l hM setup.omega setup.empty
  have heω := num_mem_l hM.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨_,Z,rank,treeRank⟩ := setup.low.read_l hM setup.limit.1
  obtain ⟨Vlevel,table⟩ := td_level_table_l hM p X Z U₁ U₂
  have empty : ∀ y, ¬ N.mem y (e p.e) := fun y hy =>
    (he p.e y).mp hy |>.elim fun x hx => setup.empty x hx.1
  have no i y : ¬ Rd_entry_d i y (e p.e) := fun ⟨q,_,hq⟩ => empty q hq
  have emptyWeave : Dg_weave_d J (e p.ω) (e p.e) (e p.e) (e p.e) := by
    constructor
    · intro i _ y
      exact iff_of_false (no i y) (fun ⟨j,_,point⟩ => no j y point)
    · intro i _ y
      exact iff_of_false (no i y) (fun ⟨j,l,_,_,point⟩ => no l y point)
  have emptyFn (A : M.Domain) : Fn0_d p.e A p.e := ⟨fun x hx => (setup.empty x hx).elim,
    fun x hx => (setup.empty x hx).elim,fun x hx => (setup.empty x hx).elim⟩
  have emptyCounter : Fn0_d (e p.e) Vc (e p.e) := ⟨fun x hx => (empty x hx).elim,
    fun x hx => (empty x hx).elim,fun x hx => (empty x hx).elim⟩
  have enumFn := fn0_function_l (ZF.modelsKP hN) c.enumeration
  have histFn := fn0_function_l (ZF.modelsKP hN) run.1
  have indexFn := fn0_function_l (ZF.modelsKP hN) c.indices
  have hwX := ZF.v_ordinal_mem_l I hM setup.rank setup.above
  -- 第一轮必为零节点重置，原两空图及同一 counter 空历史给出真实初始高度。
  have initial : Td_tracked_d hN (e p.ω) H K g (e Vlevel) Vc Rc (e p.ν) := by
    obtain ⟨n,_,h,_,v,i,en,_,_,nh,_,_,aux,_,ki,iv,_⟩ :=
      setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run
        ((image_member_l e hi he).mpr heω)
    have eq := hi en
    subst n
    have saved := aux
    obtain ⟨ℓ,k,κ,u,d,q,N,m,_,s,B,U,Du,Dw,pn,pm,pp,pb,ph,_,_,_,_,_,_,_,
      data,_,hκ,arity,_,_,request,qdata,_,_,_,_,_,branch⟩ := saved
    have eq : k = p.e := branch.elim And.left (fun h => (setup.empty ℓ h.2.1).elim)
    subst k
    have key : Td_level_key_d hM p X Z U₁ U₂ v p.e p.e p.e p.ν :=
      ⟨(image_member_l e hi he).mp (c.enumeration.bound_l iv).2,heω,
        (fun x hx => (setup.empty x hx).elim),(fun x hx => (setup.empty x hx).elim),
        emptyFn U₁,emptyFn U₂,Or.inr rfl,ℓ,κ,u,data,hκ,setup.level_reset_l hZFC aux data⟩
    exact table.track_l hM hN e he heω nh ki iv key
      ((ZF.ordinalAddition_zero_iff hN J empty).mpr rfl) emptyCounter counterControl.root emptyWeave
  obtain ⟨α,_,tracked,least⟩ := td_tracked_min_l hN
    (image_ord_l hM hN e hi he (v_ordinal_l I rank)) initial
  obtain ⟨n,h,v,k,a₀,b₀,α₀,i,dc,tc,eα,hn,nh,ki,iv,key,addc,ftc,tcR,woven⟩ :=
    table.read_tracked_l hM hN e he run.1 tracked
  subst α
  obtain ⟨hvX,hk,haZ,hbZ,fa,fb,hαν,ℓ,κ,u,data,hκ,level⟩ := key
  obtain ⟨η₀,Y₀,c₀,R₀,d₀,q₀,N₀,B₀,U₀,P₀,r₀,hη₀,hY₀,model₀,add,sq,sN,hB₀,constants₀,type₀,
    first₀,last₀,groups₀⟩ := level
  obtain ⟨m₀,sm₀,hm₀⟩ := setup.omega.1.2 N₀ type₀.finite
  have arity : Td_arity_d I k d₀ q₀ N₀ m₀ := ⟨add,sq,sN,sm₀⟩
  -- 按同一辅助历史、最小编号和枚举值识别该轮，随后读取原任意回答。
  obtain ⟨n',m,h',hNext,v',i',en,sm,_,nh',mh,_,aux,ev,ki',iv',_,h₁,w₁,fh₁,answer,ae,be⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run
      ((image_member_l e hi he).mpr hn)
  have eq := hi en
  subst n'
  have eq := hi (histFn.1.2 (e n) (e h') (e h) nh' nh)
  subst h'
  have eq := indexFn.1.2 (e h) i' i ki' ki
  subst i'
  have eq := hi (enumFn.1.2 i (e v') (e v) iv' iv)
  subst v'
  obtain ⟨θ,B₁,U₃,D₃,w,η₁,Y₁,c₁,R₁,r₁,pending,β,norm,ψ,pair,hθδ,hθ,hB₁,constants₁,pool₁,
    hη₁,hY₁,model₁,type₁,first₁,point,heightPoint,pendingTruth,bound,height,below,record,perm,points⟩ :=
    setup.level_reply_l hZFC hn fh₁ ae aux answer data arity hY₀ hη₀ model₀ hB₀ constants₀ type₀
      first₀ groups₀ fa fb tree alphabet chosen
  -- 同一扩张反策略实际回复 pending；只回收有限三图与回复字母。
  obtain ⟨_,z,cp,letter⟩ := pendingTruth
  have hz := (alphabet.1 z).mpr letter
  obtain ⟨_,_,unique⟩ := ZF.ordinalAddition_existsUnique hN J (e k)
    (hw.members_areOrdinals (ZF.modelsKP hN) (e k) ((image_member_l e hi he).mpr hk))
  have eq := (unique dc addc).trans (unique (e d₀) (image_nat_add_l hM hN e hi he setup.omega hk add)).symm
  subst dc
  obtain ⟨k₁,d₁,s₁,a₁,b₁,z₁,tc₁,tc₂,next,hk₁,hd₁,add₁,fs₁,fa₁,fb₁,hz₁,node,appendA,appendB,
    ft₂,tc₂R,end₁,end₂,reply,cut,weave₂⟩ := td_counter_ground_l hM hN e hi he setup.omega hw
      (fn0_function_l (ZF.modelsKP hN) ff) counter counterControl hk add ftc tcR fa fb woven hz
  obtain ⟨p',cp'⟩ := (I).total k z₁
  have extendA y : M.mem y a₁ ↔ M.mem y a₀ ∨ y = pending :=
    (appendA y).trans (or_congr Iff.rfl ⟨fun cy => (I).unique cy cp,fun eq => eq.symm ▸ cp⟩)
  have extendB y : M.mem y b₁ ↔ M.mem y b₀ ∨ y = p' :=
    (appendB y).trans (or_congr Iff.rfl ⟨fun cy => (I).unique cy cp',fun eq => eq.symm ▸ cp'⟩)
  have sourceFn := (fn0_function_l (ZF.modelsKP hM) fs₁).mono_target_l I
    (v_transitive_l I setup.rank p.A setup.letters)
  obtain ⟨_,_,_,hsX⟩ := ZF.v_finite_function_l hM setup.omega setup.limit setup.rank hwX hk₁ sourceFn
  -- 原模型中的实际稠密要求被捕获为同 β 的新请求，counter 状态原样带入下一 key。
  obtain ⟨E,hE,capture⟩ := setup.capture_threshold_l hZFC hN e hi he
    (r := m₀) (β := β) (left := a₁) (right := b₁) hd root histories owner control ha hw c surj ff
      values follows run hn sm mh ev be hk₁ fs₁ cut
  obtain ⟨q,hq,hit⟩ := setup.generic_meet_l hZFC hd hn data pair next hθ hB₁ constants₁
    hY₁ model₁ type₁ record perm points bound height node extendA extendB hθδ hsX histories.1 order generic hE
  obtain ⟨n₁,h',v₁,i₁,κ₁,C₁,u₁,hn₁,_,nh₁,ki₁,iv₁,target,_⟩ :=
    capture q (generic.proper q hq).1 hit (origin q hq)
  have hβν : M.mem β p.ν := hαν.elim (fun h => (v_ordinal_l I rank).transitive α₀ h β below)
    (fun eq => eq ▸ below)
  have labels := node.aux_labels_rank_l hM rank treeRank
  have nextKey : Td_level_key_d hM p X Z U₁ U₂ v₁ k₁ a₁ b₁ β :=
    ⟨(image_member_l e hi he).mp (c.enumeration.bound_l iv₁).2,hk₁,labels.1,labels.2,fa₁,fb₁,
      Or.inl hβν,n,κ₁,u₁,target.2.2.1,target.1,target.level_l hM⟩
  exact least (e β) ((image_member_l e hi he).mpr below)
    (table.track_l hM hN e he hn₁ nh₁ ki₁ iv₁ nextKey
      (image_nat_add_l hM hN e hi he setup.omega hk₁ add₁) ft₂ tc₂R weave₂)

end YesMetaZFC.SetTheory.LargeCardinal
