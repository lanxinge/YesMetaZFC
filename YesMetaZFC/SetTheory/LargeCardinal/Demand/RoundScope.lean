import YesMetaZFC.Model.SetTheory.Demand.Recovery
import YesMetaZFC.Model.SetTheory.Demand.RecordSyntax
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Realize
import YesMetaZFC.SetTheory.LargeCardinal.Types.Renewal
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReplyQueries
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Types.ImageSyntax
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Demand.Separated
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueRealizeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Reflection
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 同一次任意排列实现的双图恢复句子

源只记录原恢复核实际需要的图、端点和值域；它们由真实回合记录直接给出。
输出保留同一类型、实现和排列，指定旧 pending 值进入第一图，两图各精确追加一项。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ω,e,j,k,h,m,l,n,U,D,s,qn,qm,r,δ,S,α,a,b,pending,z,U₁,U₂,B,ν,u。
def td_recover_seed0_m : Formula 1 26 :=
  let v : Fin 26 → Term 26 := Term.bound
  set[26] ⟪⌜Formula.isEmpty⌝ₚ(⌜v 1⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜v 3⌝ₛ,⌜v 2⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜v 5⌝ₛ,⌜v 4⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜v 7⌝ₛ,⌜v 6⌝ₛ) ∧ ⌜v 5⌝ₛ ⊆ ⌜v 7⌝ₛ ∧
    ⌜td_node_query_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 7⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 3⌝ₛ,⌜v 11⌝ₛ) ∧
    ⌜tg_max_query_m⌝ₚ(⌜v 0⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 12⌝ₛ) ∧
    ⌜(v_m kpair_convention_l)⌝ₚ(⌜v 16⌝ₛ,⌜v 23⌝ₛ) ∧ ⌜v 15⌝ₛ ∈ ⌜v 23⌝ₛ ∧ ⌜v 1⌝ₛ ∈ ⌜v 15⌝ₛ ∧
    ⌜tg_graph_m⌝ₚ(⌜v 5⌝ₛ,⌜v 13⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 1⌝ₛ,⌜v 15⌝ₛ,⌜v 13⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 4⌝ₛ,⌜v 16⌝ₛ,⌜v 13⌝ₛ) ∧
    ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜v 17⌝ₛ,⌜v 2⌝ₛ,⌜v 21⌝ₛ) ∧
    ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜v 18⌝ₛ,⌜v 2⌝ₛ,⌜v 22⌝ₛ) ∧
    ⌜td_alphabet_m⌝ₚ(⌜v 15⌝ₛ,⌜v 21⌝ₛ,⌜v 22⌝ₛ) ∧
    (∀ x, x ∈ ⌜v 21⌝ₛ → ¬ x ∈ ⌜v 22⌝ₛ) ∧ ⌜v 20⌝ₛ ∈ ⌜v 21⌝ₛ ∧
    ⌜kpair0_m⌝ₚ(⌜v 19⌝ₛ,⌜v 2⌝ₛ,⌜v 20⌝ₛ) ∧
    (∀ p, (p ∈ ⌜v 17⌝ₛ ∨ p ∈ ⌜v 18⌝ₛ ∨ p = ⌜v 19⌝ₛ) ↔
      ∃ i, i ∈ ⌜v 4⌝ₛ ∧ ¬ (i = ⌜v 1⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i,p,⌜v 13⌝ₛ)) ∧
    ⌜v 11⌝ₛ ∈ ⌜v 25⌝ₛ ∧ ⌜v 12⌝ₛ ∈ ⌜v 25⌝ₛ ∧
    ⌜ts_at_m⌝ₚ(⌜v 0⌝ₛ,⌜v 14⌝ₛ,⌜v 5⌝ₛ,⌜v 13⌝ₛ,⌜v 7⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 25⌝ₛ,⌜v 24⌝ₛ)⟫

def td_recovered_m {d}
    (ω e j k m l n U D s r δ S α a b z U₁ U₂ ν u A c H r' a' b' z' π : Term d) : Formula 1 d := set[d] ⟪
  ⌜(v_m kpair_convention_l)⌝ₚ(⌜ν⌝ₛ,⌜A⌝ₛ) ∧
  ⌜(smem_m (𝒞 := kpair_convention_l))⌝ₚ(⌜c⌝ₛ,⌜A⌝ₛ,⌜H⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ,⌜c⌝ₛ,⌜A⌝ₛ,⌜H⌝ₛ,⌜n⌝ₛ,⌜r'⌝ₛ,⌜δ⌝ₛ,⌜U⌝ₛ,⌜D⌝ₛ,⌜u⌝ₛ) ∧
  ⌜(Formula.isBijectionFromTo kpair_convention_l)⌝ₚ(⌜π⌝ₛ,⌜n⌝ₛ,⌜n⌝ₛ) ∧
  (∀ i v x, ⌜rd_entry0_m⌝ₚ(v,i,⌜π⌝ₛ) → i ∈ ⌜m⌝ₛ →
    (⌜rd_entry0_m⌝ₚ(i,x,⌜r⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(v,x,⌜r'⌝ₛ))) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜ν⌝ₛ,⌜α⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ,⌜S⌝ₛ,⌜r'⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ,⌜α⌝ₛ,⌜r'⌝ₛ) ∧
  (∀ p, (p ∈ ⌜a'⌝ₛ ∨ p ∈ ⌜b'⌝ₛ) ↔ ∃ i, i ∈ ⌜l⌝ₛ ∧ ¬ (i = ⌜e⌝ₛ) ∧
    ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(i,p,⌜r'⌝ₛ)) ∧
  ⌜tg_node_m⌝ₚ(⌜k⌝ₛ,⌜S⌝ₛ,⌜s⌝ₛ,⌜a'⌝ₛ,⌜b'⌝ₛ) ∧
  ⌜td_groups_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,⌜l⌝ₛ,⌜r'⌝ₛ,⌜a'⌝ₛ,⌜b'⌝ₛ) ∧
  ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜a'⌝ₛ,⌜k⌝ₛ,⌜U₁⌝ₛ) ∧
  ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜b'⌝ₛ,⌜k⌝ₛ,⌜U₂⌝ₛ) ∧
  ⌜a⌝ₛ ⊆ ⌜a'⌝ₛ ∧ ⌜b⌝ₛ ⊆ ⌜b'⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ,⌜z⌝ₛ,⌜a'⌝ₛ) ∧
  (∀ p, p ∈ ⌜a'⌝ₛ ↔ p ∈ ⌜a⌝ₛ ∨ ⌜kpair0_m⌝ₚ(p,⌜j⌝ₛ,⌜z⌝ₛ)) ∧
  ⌜z'⌝ₛ ∈ ⌜U₂⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ,⌜z'⌝ₛ,⌜b'⌝ₛ) ∧
  (∀ p, p ∈ ⌜b'⌝ₛ ↔ p ∈ ⌜b⌝ₛ ∨ ⌜kpair0_m⌝ₚ(p,⌜j⌝ₛ,⌜z'⌝ₛ))⟫
derive_free_closed td_recovered_m

-- 八个实际见证依次为 A,c,H,r′,a′,b′,z′,π；原二十六项不变。
def td_recover_result0_m : Formula 1 26 :=
  let v : Fin 26 → Term 26 := Term.bound
  set[26] ⟪∃ A c H r' a' b' z' π,
    ⌜td_recovered_m⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,
      ⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 13⌝ₛ,⌜v 14⌝ₛ,⌜v 15⌝ₛ,⌜v 16⌝ₛ,
      ⌜v 17⌝ₛ,⌜v 18⌝ₛ,⌜v 20⌝ₛ,⌜v 21⌝ₛ,⌜v 22⌝ₛ,⌜v 24⌝ₛ,⌜v 25⌝ₛ,A,c,H,r',a',b',z',π)⟫

theorem td_recover_seed0_closed_l : td_recover_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_recover_seed0_m,Definitional.Formula.FreeClosed]

theorem td_recover_result0_closed_l : td_recover_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_recover_result0_m,Definitional.Formula.FreeClosed]

def td_recover_m : Formula 1 0 := Formula.forallClosure 26 (.imp td_recover_seed0_m td_recover_result0_m)

theorem td_recover_closed_l : td_recover_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨td_recover_seed0_closed_l,td_recover_result0_closed_l⟩

/-- 原恢复核直接证明整条有限句子；没有另加排序、实现或图包含假设。 -/
theorem td_recover_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0,ε⟩ : Env M 0) td_recover_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro v
  simp only [td_recover_seed0_m,td_recover_result0_m,td_recovered_m,Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_isEmpty_iff,Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff,td_node_query_sat_l I (ZF.modelsKP hZF),
    tg_max_query_sat_l I (ZF.modelsKP hZF),v_sat_l I hZF.1,Formula.satisfies_mem_iff,
    tg_graph_sat_l I hZF.1,rd_entry0_sat_l hZF.1,Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    td_alphabet_sat_l hZF.1,Formula.satisfies_forall_iff,Formula.satisfies_neg_iff,kpair0_sat_l hZF.1,
    Formula.satisfies_iff_iff,Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff,ts_at_sat_l hZF,smem_sat_l I,tt_realized_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_isBijectionFromTo_iff I hZF.1,Formula.satisfies_orderedPairMem_iff I,
    tg_node_sat_l I hZF.1,td_groups_sat_l I hZF.1,Definitional.Term.eval_weaken]
  rintro ⟨he,hk,hm,hn,included,node,max,rank,hS,root,old,first,last,fa,fb,alphabet,disjoint,
    hz,pending,values,qn,qm,witness⟩
  exact td_two_graph_recovery_l hZF he hk hm hn included node max rank hS root old first last
    fa fb alphabet disjoint hz pending values qn qm witness

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 回合所用的纯高度刚性句子

只反射原 exceeds、dcp 定义域和两条实际查询的数学定理。
二十个参数不包含节点、分组、排序或查询表，不混淆施加前后的两个模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ω,κ,τ,i,m,l,n,U,D,V,P,W,a,b,δ,w,u,v,g,h。
def td_rigid_seed0_m : Formula 1 20 :=
  let p : Fin 20 → Term 20 := Term.bound
  set[20] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜p 3⌝ₛ ∈ ⌜p 4⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p 6⌝ₛ,⌜p 5⌝ₛ) ∧
    ⌜ee_domain_pack_m⌝ₚ(⌜p 0⌝ₛ,⌜p 2⌝ₛ,⌜p 5⌝ₛ,⌜p 9⌝ₛ,⌜p 8⌝ₛ,⌜p 18⌝ₛ,⌜p 19⌝ₛ) ∧
    ⌜tg_height_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 3⌝ₛ,⌜p 4⌝ₛ,⌜p 7⌝ₛ,⌜p 10⌝ₛ,⌜p 12⌝ₛ) ∧
    ⌜tg_max_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 5⌝ₛ,⌜p 6⌝ₛ,⌜p 9⌝ₛ,⌜p 11⌝ₛ,⌜p 13⌝ₛ) ∧
    ⌜p 12⌝ₛ ∈ ⌜p 15⌝ₛ ∧ ⌜td_dcp_m⌝ₚ(⌜p 5⌝ₛ,⌜p 6⌝ₛ,⌜p 8⌝ₛ,⌜p 16⌝ₛ,⌜p 17⌝ₛ) ∧
    ⌜p 18⌝ₛ ∈ ⌜p 17⌝ₛ ∧ ⌜p 19⌝ₛ ∈ ⌜p 17⌝ₛ ∧
    ⌜tx_exceeds_m⌝ₚ(⌜p 0⌝ₛ,⌜p 14⌝ₛ,⌜p 1⌝ₛ,⌜p 4⌝ₛ,⌜p 7⌝ₛ,⌜p 10⌝ₛ,⌜p 15⌝ₛ,
      ⌜p 2⌝ₛ,⌜p 6⌝ₛ,⌜p 9⌝ₛ,⌜p 11⌝ₛ,⌜p 16⌝ₛ)⟫

theorem td_rigid_seed0_closed_l : td_rigid_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_rigid_seed0_m,Definitional.Formula.FreeClosed]

def td_rigid_m : Formula 1 0 := Formula.forallClosure 20
  (.imp td_rigid_seed0_m (.mem (.bound 13) (.bound 16)))

theorem td_rigid_closed_l : td_rigid_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨td_rigid_seed0_closed_l,rfl,rfl⟩

/-- 原反射句的真值仅使用 ZF，不使用不可达性、武丁性或源层额外理论。 -/
theorem td_rigid_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0,ε⟩ : Env M 0) td_rigid_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [td_rigid_seed0_m,Formula.satisfies_imp_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,
    ee_domain_pack_sat_l hZF,tg_height_query_sat_l I (ZF.modelsKP hZF),
    tg_max_query_sat_l I (ZF.modelsKP hZF),td_dcp_sat_l I hZF.1,
    tx_exceeds_sat_l hZF]
  rintro ⟨hw,hi,hn,domain,height,max,member,drop,hg,hh,exceeds⟩
  exact tg_exceeds_rigid_l hZF hw hi hn domain height max member drop ⟨hg,hh⟩ exceeds

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原排列下的完整弹性 demanding 回答

原 u 的高度以前的全部值由同树节点约束在 Vν 中。指定 pending 对在
V(ν+2) 中实际产生；同一前缀追加 pending 与 ν 后，武丁工厂在
V(ν+3) 产生完整且本身弹性的 w，不把 dcp 的弹性替代为 w 的弹性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原元组的标签位置保持不变；低点与所有载体所属均由实际证书读取。 -/
theorem Tg_low_d.demand_elastic_l
    {ω e δ S ν χ k d q n Y c R r U Du u s a b U₁ U₂ z : M.Domain}
    (low : Tg_low_d hZF ω e δ S ν) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (hd : Woodin_d I δ) (hχ : M.mem χ δ)
    (type : Tt_realized_d I ω c Y R n r δ U Du u)
    (root : Rd_entry_d e S r) (last : Rd_entry_d q ν r)
    (add : M.IsOrdinalAddition I d k k) (sq : M.SuccessorOf q d) (sn : M.SuccessorOf n q)
    (groups : Td_groups_d I ω e q r a b) (node : Tg_node_d I k S s a b)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) :
    ∃ ν₁ ν₂ ν₃ W c' R' τ B V D m r' w pending, ∃ queries : Ee_queries_d M,
      M.SuccessorOf ν₁ ν ∧ M.SuccessorOf ν₂ ν₁ ∧ M.SuccessorOf ν₃ ν₂ ∧
      V_d I ν₃ W ∧ Smem_d I c' W R' ∧ M.mem χ τ ∧ M.mem τ δ ∧
      Ee_language_d hZF ω τ m B V D queries ∧ Tt_realized_d I ω c' W R' m r' δ V D w ∧
      Ee_elastic_d queries w ∧ KPair_d M pending k z ∧
      Td_record_d I ω e k W S a b pending ν d q n m r' ∧
      (∀ i x, M.mem i q → (Rd_entry_d i x r' ↔ Rd_entry_d i x r)) ∧
      (∀ x, Rd_entry_d n x r' ↔ Rd_entry_d q x r) := by
  have woodin := hd
  obtain ⟨ω₀,_,hw₀,hwδ,regular,_⟩ := woodin
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hw₀.2 ω hw.1 x,hw.2 ω₀ hw₀.1 x⟩)
  subst ω₀
  obtain ⟨hδν,Z,rank,hS⟩ := low.read_l hZF regular.isLimitOrdinal.1
  have oν := v_ordinal_l I rank
  have hwν := oν.transitive δ hδν ω hwδ
  have above : M.MemberSubset ω ν := oν.transitive ω hwν
  have hq := hw.transitive (ZF.modelsKP hZF) n type.finite q sn.predecessor_mem
  have hdω := hw.transitive (ZF.modelsKP hZF) q hq d sq.predecessor_mem
  have ok : M.IsOrdinal k := add.elim (fun _ h => h.1.1.1)
  have hk : M.mem k ω := (ZF.ordinalAddition_left_eq_or_mem hZF I ok add).elim
    (fun eq => eq.symm ▸ hdω) (hw.transitive (ZF.modelsKP hZF) d hdω k)
  have heq := (hw.members_areOrdinals (ZF.modelsKP hZF) q hq).empty_mem_of_nonempty
    (ZF.modelsKP hZF) ⟨d,sq.predecessor_mem⟩ empty
  obtain ⟨ν₁,oν₁,first⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) oν
  obtain ⟨ν₂,oν₂,second⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) oν₁
  have hνν₂ := oν₂.transitive ν₁ second.predecessor_mem ν first.predecessor_mem
  obtain ⟨ω',_,Z₂,ν₃,W,_,_,c',R',hw',_,rank₂,third,rank₃,_,model,all⟩ :=
    woodin_elastic_l hZFC hd oν₂ (oν₂.transitive ν hνν₂ δ hδν)
  have eqω := hZF.1.eq_of_same_members ω' ω (fun x => ⟨hw'.2 ω hw.1 x,hw.2 ω' hw'.1 x⟩)
  subst ω'
  have sub := ZF.v_mono_l I hZF rank rank₂ (oν₂.transitive ν hνν₂)
  -- 任意原排列下，每个非根前缀值都是原两图的实际标签。
  have labels := node.aux_labels_rank_l hZF rank hS
  obtain ⟨r₀,cut⟩ := ZF.exists_restriction hZF I r q
  have fn := fn0_function_l (ZF.modelsKP hZF) type.tuple
  have fr₀ := cut.isSetFunctionFromTo fn (fun i hi => (sn i).mpr (Or.inl hi))
  have small : M.IsSetFunctionFromTo I r₀ q Z₂ := ⟨fr₀.1,fr₀.2.1,fun i hi => by
    obtain ⟨x,_,ix⟩ := fr₀.2.2 i hi
    have old := ((cut.2 i x).mp ix).2
    refine ⟨x,sub x ?_,ix⟩
    by_cases ie : i = e
    · exact (fn.1.2 e x S (ie ▸ old) root).symm ▸ hS
    · exact ((groups.cover_l x).mpr ⟨i,hi,ie,old⟩).elim (labels.1 x) (labels.2 x)⟩
  have same i x (hi : M.mem i q) : Rd_entry_d i x r₀ ↔ Rd_entry_d i x r :=
    (cut.2 i x).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
  have groups₀ : Td_groups_d I ω e q r₀ a b := by
    constructor
    · intro x
      exact (groups.1 x).trans
        ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mpr point⟩,
          fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mp point⟩⟩
    · intro x
      exact (groups.2 x).trans
        ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mpr point⟩,
          fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mp point⟩⟩
  obtain ⟨pending,hp,pair⟩ := alphabet.pending_pair_two_l hZF rank hS above hk chosen first second rank₂
  obtain ⟨l,m,r',record,kept⟩ := td_record_append_l (ZF.modelsKP hZF) hw empty hq add sq
    (fn0_of_function_l (ZF.modelsKP hZF) small) ((same e S heq).mpr root) groups₀ hp
    (ZF.v_ordinal_mem_l I hZF rank₂ hνν₂)
  have el := record.pending_end.eq hZF.1 sn
  subst l
  -- 调用的是完整元组的弹性工厂，返回的 upper w 本身满足 Ee_elastic。
  obtain ⟨τ,_,_,B,V,D,queries,_,w,high,hτ,_,_,language,_,full,_,elastic⟩ :=
    all m r' record.finite record.tuple χ hχ
  have record' : Td_record_d I ω e k W S a b pending ν d q n m r' :=
    ⟨record.twice,record.labels_end,record.pending_end,record.height_end,record.finite,full.tuple,
      record.root_before,record.root,record.pending,record.height,record.groups,record.values⟩
  refine ⟨ν₁,ν₂,ν₃,W,c',R',τ,B,V,D,m,r',w,pending,queries,first,second,third,rank₃,model,
    high,hτ,language,full,elastic,pair,record',fun i x hi => (kept i x hi).trans (same i x hi),fun x => ⟨?_,?_⟩⟩
  · intro hx
    exact ((fn0_function_l (ZF.modelsKP hZF) full.tuple).1.2 n x ν hx record'.height).symm ▸ last
  · intro hx
    exact (fn.1.2 q x ν hx last).symm ▸ record'.height

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.8 的双图回答与实际一步扩展器

原 u 的完整前缀由不可分辨点提升到高处；低处在原位置插入指定 pending。
完整弹性 w 因而真实超过原 dcp(u)，再由原一步引理给出扩展器，而非输入
假定的 subtype 或扩展器存在性。两图顺序和原候选类型始终保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.demand_renew_l
    {ω e δ S ν κ k d₀ q n α A c R r B U E P u v b₀ a₀ z₀ χ s a b U₁ U₂ z : M.Domain}
    {σ : Fin 7 → M.Domain} {eqs : Ee_queries_d M}
    (low : Tg_low_d hZF ω e δ S ν) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (hd : Woodin_d I δ) (hκδ : M.mem κ δ)
    (add : M.IsOrdinalAddition I d₀ k k) (sq : M.SuccessorOf q d₀) (sn : M.SuccessorOf n q)
    (height : M.SuccessorOf α ν) (rank : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ q B U E eqs) (drop : Td_dcp_d I q n E u v)
    (elastic : Ee_elastic_d eqs v) (root : Rd_entry_d e S r) (last : Rd_entry_d q ν r)
    (groups : Td_groups_d I ω e q r a b) (node : Tg_node_d I k S s a b)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁)
    (prog : Ts_program_d hZF ω q b₀ σ a₀ z₀) (hχ : M.mem χ δ) :
    ∃ τ C V D w η Y c' H m r' pending, ∃ queries : Ee_queries_d M,
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Y ∧ Smem_d I c' Y H ∧
      Ee_language_d hZF ω τ m C V D queries ∧ Tt_realized_d I ω c' Y H m r' δ V D w ∧
      Ee_elastic_d queries w ∧ KPair_d M pending k z ∧
      Td_record_d I ω e k Y S a b pending ν d₀ q n m r' ∧
      (∀ i x, M.mem i q → (Rd_entry_d i x r' ↔ Rd_entry_d i x r)) ∧
      Tx_exceeds_d hZF ω δ κ q U E v τ m V D w ∧
      Ee_one_step_d hZF ω κ δ q v τ m w b₀ σ z₀ := by
  have woodin := hd
  obtain ⟨ω₀,_,hw₀,hwδ,regular,_⟩ := woodin
  have ew := hZF.1.eq_of_same_members ω₀ ω (fun i => ⟨hw₀.2 ω hw.1 i,hw.2 ω₀ hw₀.1 i⟩)
  subst ω₀
  have heω := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  obtain ⟨hδν,Z,hZ,hS⟩ := low.read_l hZF regular.isLimitOrdinal.1
  obtain ⟨γ,W,F,μ,hγ,hW,hwW,hδW,hSW,pool,pair⟩ :=
    low.band_l hZF hw empty heω regular.isLimitOrdinal.1 hwδ
  have labels := node.aux_labels_rank_l hZF hW hSW
  have values i x (hi : M.mem i q) (point : Rd_entry_d i x r) : M.mem x W ∧ x ≠ ν := by
    by_cases eq : i = e
    · have ex := (fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 e x S (eq ▸ point) root
      subst x
      exact ⟨hSW,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) ν
        (ZF.v_ordinal_height_l hZF hZ pair.1 (eq ▸ hS))⟩
    · rcases (groups.cover_l x).mpr ⟨i,hi,eq,point⟩ with ha | hb
      · obtain ⟨j,y,cp⟩ := node.2.1.1.1 x ha
        exact ⟨labels.1 x ha,fun eq => cp.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF))
          (eq.symm ▸ pair.1.transitive)⟩
      · obtain ⟨j,y,cp⟩ := node.2.2.1.1.1 x hb
        exact ⟨labels.2 x hb,fun eq => cp.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF))
          (eq.symm ▸ pair.1.transitive)⟩
  obtain ⟨α',A',c'',R',s',highsucc,hA',upper,pretype,kept⟩ := pair.raise_prefix_l hZF hw empty heω
    regular.isLimitOrdinal hwδ hγ hW hδW pool hκδ language.rank language.constants language.pool
    sn height rank model type drop last values
  obtain ⟨ξ,hξ,χξ,κξ⟩ : ∃ ξ, M.mem ξ δ ∧ (χ = ξ ∨ M.mem χ ξ) ∧ (κ = ξ ∨ M.mem κ ξ) := by
    rcases regular.isLimitOrdinal.1.wellOrder.linear.compare χ hχ κ hκδ with eq | lt | gt
    · exact ⟨κ,hκδ,Or.inl (hZF.1.eq_of_same_members χ κ eq),Or.inl rfl⟩
    · exact ⟨κ,hκδ,Or.inr lt,Or.inl rfl⟩
    · exact ⟨χ,hχ,Or.inl rfl,Or.inr gt⟩
  obtain ⟨ν₁,ν₂,η,Y,c',H,τ,C,V,D,m,r',w,pending,queries,s₁,s₂,s₃,hY,lower,above,hτδ,
    target,full,el,cp,record,original,_⟩ :=
    low.demand_elastic_l hZFC hw empty hd hξ type root last add sq sn groups node alphabet chosen
  have hχτ := χξ.elim (fun eq => eq.symm ▸ above) (target.limit.1.transitive ξ above χ)
  have hκτ := κξ.elim (fun eq => eq.symm ▸ above) (target.limit.1.transitive ξ above κ)
  obtain ⟨one,so,ho⟩ := hw.1.2 e heω
  obtain ⟨two,st,ht⟩ := hw.1.2 one ho
  obtain ⟨three,sr,hr⟩ := hw.1.2 two ht
  have zero : M.IsOrdinalAddition I ν ν e := (ZF.ordinalAddition_zero_iff hZF I empty).mpr rfl
  have add₁ := (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members empty) so).mpr ⟨ν,zero,s₁⟩
  have add₂ := (ZF.ordinalAddition_successor_iff hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) one ho) st).mpr ⟨ν₁,add₁,s₂⟩
  have add₃ := (ZF.ordinalAddition_successor_iff hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) two ht) sr).mpr ⟨ν₂,add₂,s₃⟩
  have below := pair.finite_gap_l hZF hw empty heω hW hwW pool hr add₃
  obtain ⟨η',oη',sη⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF) (v_ordinal_l I hY)
  have gap : M.mem η' α' := ordinal_down_l (ZF.modelsKP hZF) oη' (v_ordinal_l I hA') (b := μ)
    (fun x hx => ((sη x).mp hx).elim (pair.2.1.transitive η below x)
      (fun eq => (hZF.1.eq_of_same_members x η eq).symm ▸ below)) highsucc.predecessor_mem
  have included : M.MemberSubset q m := fun i hi =>
    (record.height_end i).mpr (Or.inl ((record.pending_end i).mpr (Or.inl hi)))
  have witness := ts_at_prefix_l hZF hw hY lower full included
    (fun i x hi => (kept i x hi).trans (original i x hi).symm)
  have exceeds : Tx_exceeds_d hZF ω δ κ q U E v τ m V D w :=
    ⟨hκτ,included,α',A',c'',R',s',hA',upper,pretype,η,η',sη,gap,witness⟩
  exact ⟨τ,C,V,D,w,η,Y,c',H,m,r',pending,queries,hχτ,hκτ,hτδ,⟨ν₁,ν₂,s₁,s₂,s₃⟩,
    hY,lower,target,full,el,cp,record,original,exceeds,
    ee_one_step_l hZFC hw prog language target.limit hτδ target.rank target.constants elastic exceeds⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双图回答与原完整类型在同一次实际超幂中的衔接

新回答保留原前缀，在两个新槽放入指定 pending 及低高度。
同一次扩展器搬运原 u 和 dcp(u)，三条查询由该回答自身的完整实现读出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.demand_step_l
    {ω e δ S ν κ k d₀ q n α A c R r B U E P u v b₀ a₀ z₀ χ s a b U₁ U₂ z A₀ : M.Domain}
    {σ : Fin 7 → M.Domain} {eqs : Ee_queries_d M}
    (low : Tg_low_d hZF ω e δ S ν) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e)
    (hd : Woodin_d I δ) (hκδ : M.mem κ δ)
    (add : M.IsOrdinalAddition I d₀ k k) (sq : M.SuccessorOf q d₀) (sn : M.SuccessorOf n q)
    (height : M.SuccessorOf α ν) (rank : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ q B U E eqs) (drop : Td_dcp_d I q n E u v)
    (elastic : Ee_elastic_d eqs v) (root : Rd_entry_d e S r) (last : Rd_entry_d q ν r)
    (groups : Td_groups_d I ω e q r a b) (node : Tg_node_d I k S s a b)
    (tree : Td_tree_d I ω A₀ S) (hA₀ : M.mem A₀ U)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁)
    (prog : Ts_program_d hZF ω q b₀ σ a₀ z₀) (hχ : M.mem χ δ) :
    ∃ τ C V D w η Z c' H m r' pending, ∃ queries : Ee_queries_d M,
    ∃ pp pb ph X K T L F c₀ d₁ Y T' j κ' U' E' u',
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Z ∧ Smem_d I c' Z H ∧
      Ee_language_d hZF ω τ m C V D queries ∧ Tt_realized_d I ω c' Z H m r' δ V D w ∧
      Ee_elastic_d queries w ∧ KPair_d M pending k z ∧
      Td_record_d I ω e k Z S a b pending ν d₀ q n m r' ∧
      (∀ i x, M.mem i q → (Rd_entry_d i x r' ↔ Rd_entry_d i x r)) ∧
      M.mem A₀ V ∧ Tg_query_request_d hZF ω τ k e A₀ ∧
      Td_pending_query_d I ω A₀ e m q V D k pp ∧ Tg_bound_query_d I ω e n m V D pb ∧
      Tg_height_query_d I ω n m V D ph ∧
      V_d I δ X ∧ Ep_source_d I ω κ K X T ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧
      It_local_d I ω X T κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d I ω κ L X F ∧
      Smem_d I c₀ X T ∧ Smem_d I d₁ Y T' ∧ It_ultra_d I ω κ L F c₀ d₁ j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d E E' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω q U' E' ∧
      Td_reply_d I ω q n m κ' τ U' E' D u' w b₀ z₀ pp pb ph σ := by
  obtain ⟨τ,C,V,D,w,η,Z,c',H,m,r',pending,queries,hχτ,hκτ,hτδ,level,hZ,lower,
    target,full,el,cp,record,kept,_,step⟩ := low.demand_renew_l hZFC hw empty hd hκδ
      add sq sn height rank model type language drop elastic root last groups node alphabet chosen prog hχ
  have woodin := hd
  obtain ⟨_,_,_,_,regular,_⟩ := woodin
  have hq := hw.transitive (ZF.modelsKP hZF) n type.finite q sn.predecessor_mem
  have hdω := hw.transitive (ZF.modelsKP hZF) q hq d₀ sq.predecessor_mem
  have ok : M.IsOrdinal k := add.elim (fun _ h => h.1.1.1)
  have hk := (ZF.ordinalAddition_left_eq_or_mem hZF I ok add).elim
    (fun eq => eq.symm ▸ hdω) (hw.transitive (ZF.modelsKP hZF) d₀ hdω k)
  have finite := tt_constants_finite_l hZF hw hk target.limit target.rank target.constants
  have hUC := tt_constants_rank_l hZF target.rank target.limit hκτ language.rank language.constants
  have hAV := (target.constants A₀).mpr (Or.inl ((v_transitive_l I target.rank) U hUC A₀ hA₀))
  have heω := num_mem_l hZF.1 hw (show Num_d 0 e from empty)
  have request : Tg_query_request_d hZF ω τ k e A₀ :=
    ⟨target.limit,hk,C,V,target.rank,target.constants,
      (tt_constants_finite_l hZF hw heω target.limit target.rank target.constants).2,hAV⟩
  obtain ⟨pp,pb,ph,pq,bq,hq',hp,hb,hh⟩ := low.demand_reply_queries_l hZF hw regular.isLimitOrdinal.1
    hZ lower full record level tree alphabet chosen cp finite.1 hAV finite.2
  obtain ⟨X,K,T,L,F,c₀,d₁,Y,T',j,κ',U',E',u',v',hX,source,hLδ,hκL,hτL,_,loc,inacc,
    strength,mx,my,ultra,critical,bound,κlimit,hU,hE,hu,pool,drop',subtype⟩ :=
    step.dcp_image_l hZF hw regular.isLimitOrdinal prog language rank model type sn drop
      target.limit record.finite hχ
  exact ⟨τ,C,V,D,w,η,Z,c',H,m,r',pending,queries,pp,pb,ph,X,K,T,L,F,c₀,d₁,Y,T',j,κ',U',E',u',
    hχτ,hκτ,hτδ,level,hZ,lower,target,full,el,cp,record,kept,hAV,request,pq,bq,hq',hX,source,hLδ,hκL,hτL,
    loc,inacc,strength,mx,my,ultra,critical,bound,κlimit,hU,hE,hu,pool,
    ⟨fun x hx => ((full.truth x).mp hx).1,v',drop',subtype,hp,hb,hh⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 回答的同一次超幂证书句子

源前缀 q、完整源元数 n、回答元数 m 分别保存。查询池的实际支撑秩界
和原 23 槽回答共同量化，后继只读取这一份扩展器及其实际像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_image_m {d} (ω κ δ q n m U E u τ D w b z pp pb ph : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  ∃ X K R L F c d Y T j κ' U' E' u',
    ⌜ti_image_m⌝ₚ(⌜ω⌝ₛ,⌜κ⌝ₛ,⌜δ⌝ₛ,⌜τ⌝ₛ,⌜U⌝ₛ,⌜E⌝ₛ,⌜u⌝ₛ,X,K,R,L,F,c,d,Y,T,j,κ',U',E',u') ∧
    (∃ W, ⌜v_sigma_m⌝ₚ(L,W) ∧ ⌜D⌝ₛ ∈ W) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,⌜q⌝ₛ,U',E') ∧
    ⌜fun ω q n m κ τ U E D u w b z pp pb ph s₀ s₁ s₂ s₃ s₄ s₅ s₆ =>
      td_reply_m ω q n m κ τ U E D u w b z pp pb ph
        (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ,⌜q⌝ₛ,⌜n⌝ₛ,⌜m⌝ₛ,κ',⌜τ⌝ₛ,U',E',⌜D⌝ₛ,u',⌜w⌝ₛ,⌜b⌝ₛ,⌜z⌝ₛ,⌜pp⌝ₛ,⌜pb⌝ₛ,⌜ph⌝ₛ,
        ⌜σ 0⌝ₛ,⌜σ 1⌝ₛ,⌜σ 2⌝ₛ,⌜σ 3⌝ₛ,⌜σ 4⌝ₛ,⌜σ 5⌝ₛ,⌜σ 6⌝ₛ)⟫

@[simp] theorem td_image_closed_l {d} (ω κ δ q n m U E u τ D w b z pp pb ph : Term d) (σ : Fin 7 → Term d)
    (hω : ω.freeSupport = []) (hκ : κ.freeSupport = []) (hδ : δ.freeSupport = [])
    (hq : q.freeSupport = []) (hn : n.freeSupport = []) (hm : m.freeSupport = [])
    (hU : U.freeSupport = []) (hE : E.freeSupport = []) (hu : u.freeSupport = [])
    (hτ : τ.freeSupport = []) (hD : D.freeSupport = []) (hw : w.freeSupport = [])
    (hb : b.freeSupport = []) (hz : z.freeSupport = []) (hp : pp.freeSupport = [])
    (hB : pb.freeSupport = []) (hH : ph.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) :
    (td_image_m ω κ δ q n m U E u τ D w b z pp pb ph σ).FreeClosed := by
  simp -implicitDefEqProofs [td_image_m,Definitional.Formula.FreeClosed,hω,hκ,hδ,hq,hn,hm,hU,hE,hu,
    hτ,hD,hw,hb,hz,hp,hB,hH,hσ,Fin.forall_fin_succ]

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 固定同一次 demanding 回答的支撑、超幂和三个类型像；源 q/n 与回答 m 分别保存。 -/
def Td_image_at_d (ω κ δ q n m U E u τ D w b z pp pb ph : M.Domain)
    (σ : Fin 7 → M.Domain) (L W X K R F c d Y T j κ' U' E' u' : M.Domain) : Prop :=
  V_d I δ X ∧ Ep_source_d I ω κ K X R ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧
  V_d I L W ∧ M.mem D W ∧
  It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d I ω κ L X F ∧
  Smem_d I c X R ∧ Smem_d I d Y T ∧ It_ultra_d I ω κ L F c d j ∧ Wd_crit_d I X j κ κ' ∧
  M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
  Rd_entry_d U U' j ∧ Rd_entry_d E E' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω q U' E' ∧
  Td_reply_d I ω q n m κ' τ U' E' D u' w b z pp pb ph σ

theorem td_image_sat_l {d} (ρ : Env M d) (ω κ δ q n m U E u τ D w b z pp pb ph : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (td_image_m ω κ δ q n m U E u τ D w b z pp pb ph σ) ↔
    ∃ X K R L F c d Y T j κ' U' E' u',
      V_d I (δ.eval ρ) X ∧ Ep_source_d I (ω.eval ρ) (κ.eval ρ) K X R ∧
      M.mem L (δ.eval ρ) ∧ M.mem (κ.eval ρ) L ∧ M.mem (τ.eval ρ) L ∧
      (∃ W, V_d I L W ∧ M.mem (D.eval ρ) W) ∧
      It_local_d I (ω.eval ρ) X R (κ.eval ρ) L F ∧ Sc_inaccessible_d (ω.eval ρ) X L ∧
      Ex_strength_d I (ω.eval ρ) (κ.eval ρ) L X F ∧ Smem_d I c X R ∧ Smem_d I d Y T ∧
      It_ultra_d I (ω.eval ρ) (κ.eval ρ) L F c d j ∧ Wd_crit_d I X j (κ.eval ρ) κ' ∧
      M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧ Rd_entry_d (U.eval ρ) U' j ∧
      Rd_entry_d (E.eval ρ) E' j ∧ Rd_entry_d (u.eval ρ) u' j ∧ Tt_pool_d I (ω.eval ρ) (q.eval ρ) U' E' ∧
      Td_reply_d I (ω.eval ρ) (q.eval ρ) (n.eval ρ) (m.eval ρ) κ' (τ.eval ρ) U' E' (D.eval ρ) u'
        (w.eval ρ) (b.eval ρ) (z.eval ρ) (pp.eval ρ) (pb.eval ρ) (ph.eval ρ) (fun i => (σ i).eval ρ) := by
  have eta (f : Fin 7 → M.Domain) :
      Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6)))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [td_image_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    ti_image_sat_l hKP,v_sigma_sat_l hKP,Formula.satisfies_mem_iff,tt_pool_sat_l I hKP,
    td_reply_sat_l hKP,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,
    tt_eval_cases_l,eta (fun i => (σ i).eval ρ)]
  constructor
  · rintro ⟨X,K,R,L,F,c,d,Y,T,j,κ',U',E',u',core,queryRank,pool,reply⟩
    obtain ⟨rank,source,hL,hk,ht,loc,card,strong,mx,my,ultra,critical,bound,limit,hU,hE,hu⟩ := core
    exact ⟨X,K,R,L,F,c,d,Y,T,j,κ',U',E',u',rank,source,hL,hk,ht,queryRank,
      loc,card,strong,mx,my,ultra,critical,bound,limit,hU,hE,hu,pool,reply⟩
  · rintro ⟨X,K,R,L,F,c,d,Y,T,j,κ',U',E',u',rank,source,hL,hk,ht,queryRank,
      loc,card,strong,mx,my,ultra,critical,bound,limit,hU,hE,hu,pool,reply⟩
    exact ⟨X,K,R,L,F,c,d,Y,T,j,κ',U',E',u',
      ⟨rank,source,hL,hk,ht,loc,card,strong,mx,my,ultra,critical,bound,limit,hU,hE,hu⟩,
      queryRank,pool,reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际 demanding 更新的有限原语言句子

原输入用 43 个坐标保存，新见证用 19 个坐标保存。两个元组分开编号，
以免量词栈反向排列混淆 q、n、m。完整原类型与两图记录均进入同一句子。
树的两个辅助出现域不交也写入原输入；整轮沿父边运输及存档时自动保留，
不增加坐标，也不在恢复端另设不交假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 0–31：ω,e,δ,S,ν,κ,k,d,q,n,α,A,c,R,r,B,U,E,P,u,v,b₀,a₀,z₀,χ,s,a,b,U₁,U₂,z,A₀。
-- 32–35 是原弹性四查询，36–42 是同一 subtype 程序的七个槽。
def td_seed_m {d} (p : Fin 43 → Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜p 1⌝ₛ) ∧
  ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 2⌝ₛ) ∧
  ⌜tg_low_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 2⌝ₛ,⌜p 3⌝ₛ,⌜p 4⌝ₛ) ∧ ⌜p 5⌝ₛ ∈ ⌜p 2⌝ₛ ∧
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(⌜p 7⌝ₛ,⌜p 6⌝ₛ,⌜p 6⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜p 8⌝ₛ,⌜p 7⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜p 9⌝ₛ,⌜p 8⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜p 10⌝ₛ,⌜p 4⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜p 10⌝ₛ,⌜p 11⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 12⌝ₛ,⌜p 11⌝ₛ,⌜p 13⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜p 0⌝ₛ,⌜p 12⌝ₛ,⌜p 11⌝ₛ,⌜p 13⌝ₛ,⌜p 9⌝ₛ,⌜p 14⌝ₛ,⌜p 2⌝ₛ,⌜p 16⌝ₛ,⌜p 18⌝ₛ,⌜p 19⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜p 0⌝ₛ,⌜p 5⌝ₛ,⌜p 8⌝ₛ,⌜p 15⌝ₛ,⌜p 16⌝ₛ,⌜p 17⌝ₛ,⌜p 32⌝ₛ,⌜p 33⌝ₛ,⌜p 34⌝ₛ,⌜p 35⌝ₛ) ∧
  ⌜td_dcp_m⌝ₚ(⌜p 8⌝ₛ,⌜p 9⌝ₛ,⌜p 17⌝ₛ,⌜p 19⌝ₛ,⌜p 20⌝ₛ) ∧
  ⌜ee_elastic_m⌝ₚ(⌜p 32⌝ₛ,⌜p 33⌝ₛ,⌜p 34⌝ₛ,⌜p 35⌝ₛ,⌜p 20⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜p 1⌝ₛ,⌜p 3⌝ₛ,⌜p 14⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜p 8⌝ₛ,⌜p 4⌝ₛ,⌜p 14⌝ₛ) ∧
  ⌜td_groups_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 8⌝ₛ,⌜p 14⌝ₛ,⌜p 26⌝ₛ,⌜p 27⌝ₛ) ∧
  ⌜tg_node_m⌝ₚ(⌜p 6⌝ₛ,⌜p 3⌝ₛ,⌜p 25⌝ₛ,⌜p 26⌝ₛ,⌜p 27⌝ₛ) ∧
  ⌜td_tree_m⌝ₚ(⌜p 0⌝ₛ,⌜p 31⌝ₛ,⌜p 3⌝ₛ) ∧ ⌜p 31⌝ₛ ∈ ⌜p 16⌝ₛ ∧
  ⌜td_alphabet_m⌝ₚ(⌜p 3⌝ₛ,⌜p 28⌝ₛ,⌜p 29⌝ₛ) ∧ ⌜p 30⌝ₛ ∈ ⌜p 28⌝ₛ ∧
  ⌜fun ω q b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω q b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p 0⌝ₛ,⌜p 8⌝ₛ,⌜p 21⌝ₛ,⌜p 22⌝ₛ,⌜p 23⌝ₛ,⌜p 36⌝ₛ,⌜p 37⌝ₛ,⌜p 38⌝ₛ,⌜p 39⌝ₛ,⌜p 40⌝ₛ,⌜p 41⌝ₛ,⌜p 42⌝ₛ) ∧
  ⌜p 24⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜td_separated_m⌝ₚ(⌜p 3⌝ₛ)⟫

-- 新坐标依次为 τ,C,V,D,w,η,Z,c′,H,m,r′,pending、四弹性查询、pp,pb,ph。
def td_round_m {d} (p : Fin 43 → Term d) (v : Fin 19 → Term d) : Formula 1 d := set[d] ⟪
  ⌜p 24⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜p 5⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 0⌝ₛ ∈ ⌜p 2⌝ₛ ∧
  (∃ ξ ζ, ⌜Formula.isSuccessor⌝ₚ(ξ,⌜p 4⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(ζ,ξ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜v 5⌝ₛ,ζ)) ∧
  ⌜v_sigma_m⌝ₚ(⌜v 5⌝ₛ,⌜v 6⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 7⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜p 0⌝ₛ,⌜v 0⌝ₛ,⌜v 9⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 12⌝ₛ,⌜v 13⌝ₛ,⌜v 14⌝ₛ,⌜v 15⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜p 0⌝ₛ,⌜v 7⌝ₛ,⌜v 6⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜p 2⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ) ∧
  ⌜ee_elastic_m⌝ₚ(⌜v 12⌝ₛ,⌜v 13⌝ₛ,⌜v 14⌝ₛ,⌜v 15⌝ₛ,⌜v 4⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(⌜v 11⌝ₛ,⌜p 6⌝ₛ,⌜p 30⌝ₛ) ∧
  ⌜td_record_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 6⌝ₛ,⌜v 6⌝ₛ,⌜p 3⌝ₛ,⌜p 26⌝ₛ,⌜p 27⌝ₛ,⌜v 11⌝ₛ,⌜p 4⌝ₛ,
    ⌜p 7⌝ₛ,⌜p 8⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ) ∧
  (∀ i ∈ ⌜p 8⌝ₛ, ∀ x, ⌜rd_entry0_m⌝ₚ(i,x,⌜v 10⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i,x,⌜p 14⌝ₛ)) ∧
  ⌜p 31⌝ₛ ∈ ⌜v 2⌝ₛ ∧ ⌜tg_query_request_m⌝ₚ(⌜p 0⌝ₛ,⌜v 0⌝ₛ,⌜p 6⌝ₛ,⌜p 1⌝ₛ,⌜p 31⌝ₛ) ∧
  ⌜td_pending_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 31⌝ₛ,⌜p 1⌝ₛ,⌜v 9⌝ₛ,⌜p 8⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜p 6⌝ₛ,⌜v 16⌝ₛ) ∧
  ⌜tg_bound_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 17⌝ₛ) ∧
  ⌜tg_height_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 18⌝ₛ) ∧
  ⌜v 16⌝ₛ ∈ ⌜v 4⌝ₛ ∧ ⌜v 17⌝ₛ ∈ ⌜v 4⌝ₛ ∧ ⌜v 18⌝ₛ ∈ ⌜v 4⌝ₛ ∧
  ⌜p 21⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 23⌝ₛ ∈ ⌜p 0⌝ₛ ∧
  ⌜p 36⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 37⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 38⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 39⌝ₛ ∈ ⌜p 0⌝ₛ ∧
  ⌜p 40⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 41⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 42⌝ₛ ∈ ⌜p 0⌝ₛ ∧
  ⌜fun ω κ δ q n m U E u τ D w b z pp pb ph s₀ s₁ s₂ s₃ s₄ s₅ s₆ =>
    td_image_m ω κ δ q n m U E u τ D w b z pp pb ph
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p 0⌝ₛ,⌜p 5⌝ₛ,⌜p 2⌝ₛ,⌜p 8⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜p 16⌝ₛ,⌜p 17⌝ₛ,⌜p 19⌝ₛ,
      ⌜v 0⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜p 21⌝ₛ,⌜p 23⌝ₛ,⌜v 16⌝ₛ,⌜v 17⌝ₛ,⌜v 18⌝ₛ,
      ⌜p 36⌝ₛ,⌜p 37⌝ₛ,⌜p 38⌝ₛ,⌜p 39⌝ₛ,⌜p 40⌝ₛ,⌜p 41⌝ₛ,⌜p 42⌝ₛ)⟫

def td_seed0_m : Formula 1 43 := td_seed_m Term.bound
def td_witness0_m : Formula 1 62 := td_round_m
  (fun i => .bound ⟨19+i.val,by omega⟩) (fun i => .bound ⟨i.val,by omega⟩)
def td_successor0_m : Formula 1 43 := rt_exists_m 19 td_witness0_m
def td_round0_m : Formula 1 62 := .conj
  (td_seed0_m.rename (fun i => ⟨19+i.val,by omega⟩)) td_witness0_m

theorem td_seed0_closed_l : td_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_seed0_m,td_seed_m,Definitional.Formula.FreeClosed,Fin.forall_fin_succ]
theorem td_witness0_closed_l : td_witness0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_witness0_m,td_round_m,Definitional.Formula.FreeClosed,Fin.forall_fin_succ]
theorem td_successor0_closed_l : td_successor0_m.FreeClosed :=
  (rt_exists_closed_l (d := 43) (n := 19) td_witness0_m).mpr td_witness0_closed_l
theorem td_round0_closed_l : td_round0_m.FreeClosed :=
  ⟨(Definitional.Formula.freeClosed_rename _ _).mpr td_seed0_closed_l,td_witness0_closed_l⟩

def td_renewal_m : Formula 1 0 := Formula.forallClosure 43 (.imp td_seed0_m td_successor0_m)
theorem td_renewal_closed_l : td_renewal_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨td_seed0_closed_l,td_successor0_closed_l⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 更新句子的实际实例

全称句子的每次调用都使用已经证明的同一次 demand_step。
查询池进入所选支撑的秩界由该次扩展器自产，未将更新存在性加入前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem td_renewal_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0,ε⟩ : Env M 0) td_renewal_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [Formula.satisfies_imp_iff]
  intro seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    Formula.satisfies_isEmpty_iff,woodin_sat_l I hZF.1,tg_low_sat_l hZF,Formula.satisfies_mem_iff,
    Formula.satisfies_isOrdinalAddition_iff I hZF.1,Formula.satisfies_isSuccessor_iff,
    v_sat_l I hZF.1,smem_sat_l I,tt_realized_sat_l I (ZF.modelsKP hZF),ee_language_sat_l hZFC,
    td_dcp_sat_l I hZF.1,ee_elastic_sat_l,rd_entry0_sat_l hZF.1,td_groups_sat_l I hZF.1,
    tg_node_sat_l I hZF.1,td_tree_sat_l I hZF.1,td_alphabet_sat_l hZF.1,ts_program_sat_l hZF,
    tt_eval_cases_l] at seed
  obtain ⟨hw,empty,hd,low,hκδ,add,sq,sn,height,rank,model,type,language,drop,elastic,root,last,
    groups,node,tree,hA,alphabet,chosen,prog,hχ,_⟩ := seed
  obtain ⟨τ,C,V,D,w,η,Z,c',H,m,r',pending,queries,pp,pb,ph,X,K,T,L,F,c₀,d₁,Y,T',j,κ',U',E',u',
    hχτ,hκτ,hτδ,level,hZ,lower,target,full,el,cp,record,kept,hAV,request,pq,bq,hq,hX,source,hLδ,hκL,hτL,
    loc,inacc,strength,mx,my,ultra,critical,bound,κlimit,hU,hE,hu,pool,reply⟩ :=
    low.demand_step_l hZFC hw empty hd hκδ add sq sn height rank model type language drop elastic
      root last groups node tree hA alphabet chosen prog hχ
  have limitL := inacc.limit_l (ZF.modelsKP hZF) source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨W,rankW⟩ := ZF.v_exists_l I hZF limitL.1
  have hwL := ordinal_down_l (ZF.modelsKP hZF) (hw.isOrdinal (ZF.modelsKP hZF)) limitL.1 source.below hκL
  have hVW := tt_constants_rank_l hZF rankW limitL hτL target.rank target.constants
  have hDW := target.pool.rank_mem_l (ZF.modelsKP hZF) hw rankW limitL
    (ZF.v_ordinal_mem_l I hZF rankW hwL) full.finite hVW
  have slots i := hw.transitive (ZF.modelsKP hZF) _ prog.length _ (prog.slots i)
  have seen := reply
  obtain ⟨_,_,_,_,hp,hb,hh⟩ := seen
  let v : Fin 19 → M.Domain := fun i =>
    [τ,C,V,D,w,η,Z,c',H,m,r',pending,queries.largest,queries.domain,queries.inaccessible,queries.stretch,pp,pb,ph].get i
  apply (rt_exists_sat_l (n := 19) (⟨p,ε⟩ : Env M 43) td_witness0_m).mpr
  refine ⟨v,?_⟩
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_isSuccessor_iff,v_sigma_sat_l (ZF.modelsKP hZF),
    smem_sat_l I,ee_language_sat_l hZFC,tt_realized_sat_l I (ZF.modelsKP hZF),ee_elastic_sat_l,
    kpair0_sat_l hZF.1,td_record_sat_l I hZF.1,Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hZF.1,
    tg_query_request_sat_l hZF,td_pending_query_sat_l I (ZF.modelsKP hZF),tg_bound_query_sat_l I (ZF.modelsKP hZF),
    tg_height_query_sat_l I (ZF.modelsKP hZF),td_image_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken,tt_eval_cases_l]
  exact ⟨hχτ,hκτ,hτδ,level,hZ,lower,target,full,el,cp,record,(fun i hi x => kept i x hi),hAV,request,pq,bq,hq,
    hp,hb,hh,prog.length,prog.natural,slots 0,slots 1,slots 2,slots 3,slots 4,slots 5,slots 6,
    X,K,T,L,F,c₀,d₁,Y,T',j,κ',U',E',u',hX,source,hLδ,hκL,hτL,⟨W,rankW,hDW⟩,
    loc,inacc,strength,mx,my,ultra,critical,bound,κlimit,hU,hE,hu,pool,reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原固定查询行在同一 demanding 回答中为真

更新时编译的码不被当作原表的码。完整实现使原表中任意正确的
pending、严格秩界和高度码都属于同一 w；整项性质随更新核一起反射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_reply_compare0_m : Formula 1 62 :=
  let p : Fin 43 → Term 62 := fun i => .bound ⟨19+i.val,by omega⟩
  let v : Fin 19 → Term 62 := fun i => .bound ⟨i.val,by omega⟩
  set[62] ⟪∀ pp pb ph,
    ⌜td_pending_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 31⌝ₛ,⌜p 1⌝ₛ,⌜v 9⌝ₛ,⌜p 8⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜p 6⌝ₛ,pp) →
    ⌜tg_bound_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 1⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,pb) →
    ⌜tg_height_query_m⌝ₚ(⌜p 0⌝ₛ,⌜p 9⌝ₛ,⌜v 9⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,ph) →
    pp ∈ ⌜v 4⌝ₛ ∧ pb ∈ ⌜v 4⌝ₛ ∧ ph ∈ ⌜v 4⌝ₛ⟫

theorem td_reply_compare0_closed_l : td_reply_compare0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_reply_compare0_m,Definitional.Formula.FreeClosed]

def td_reply_compare_m : Formula 1 0 := Formula.forallClosure 62 (.imp td_round0_m td_reply_compare0_m)
theorem td_reply_compare_closed_l : td_reply_compare_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨td_round0_closed_l,td_reply_compare0_closed_l⟩

theorem td_reply_compare_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0,ε⟩ : Env M 0) td_reply_compare_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  apply (Formula.satisfies_imp_iff ..).mpr
  intro round
  have data := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    v_sigma_sat_l (ZF.modelsKP hZF),smem_sat_l I,tt_realized_sat_l I (ZF.modelsKP hZF),
    td_record_sat_l I hZF.1,tg_query_request_sat_l hZF,td_pending_query_sat_l I (ZF.modelsKP hZF),
    tg_bound_query_sat_l I (ZF.modelsKP hZF),tg_height_query_sat_l I (ZF.modelsKP hZF)] at data
  obtain ⟨_,_,_,_,rank,model,_,real,_,_,record,_,_,_,pq₀,bq₀,hq₀,hp,hb,hh,_⟩ := data
  simp only [td_reply_compare0_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,td_pending_query_sat_l I (ZF.modelsKP hZF),
    tg_bound_query_sat_l I (ZF.modelsKP hZF),tg_height_query_sat_l I (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  intro pp pb ph pq bq hq
  exact ⟨(pq.2 _ _ _ _ _ _ _ _ _ rank model real record.root record.pending).mpr
      ((pq₀.2 _ _ _ _ _ _ _ _ _ rank model real record.root record.pending).mp hp),
    (bq.2 _ _ _ _ _ _ _ _ _ rank model real record.root record.height).mpr
      ((bq₀.2 _ _ _ _ _ _ _ _ _ rank model real record.root record.height).mp hb),
    (hq.2 _ _ _ _ _ _ _ _ rank model real record.height).mpr
      ((hq₀.2 _ _ _ _ _ _ _ _ rank model real record.height).mp hh)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 更新核的实际有限反射层

双图更新、同高度恢复与原查询比较使用自己的已证句子；一步伸展、
真实 subtype 实现及有界代表池仍共用原数学核。全部新参数均受全称句子约束。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_kernel_m : Formula 1 0 := .conj td_renewal_m
  (.conj tc_transfer_m (.conj ee_rebuild_m (.conj tc_realize_m
    (.conj td_rigid_m (.conj td_recover_m (.conj td_reply_compare_m eo_kernel_m))))))

theorem td_kernel_closed_l : td_kernel_m.FreeClosed :=
  ⟨td_renewal_closed_l,tc_transfer_closed_l,ee_rebuild_closed_l,tc_realize_closed_l,
    td_rigid_closed_l,td_recover_closed_l,td_reply_compare_closed_l,eo_kernel_closed_l⟩

def Td_kernel_d (N : Structure.{u}) : Prop := ∀ ρ : Env N 0, Formula.satisfies ρ td_kernel_m

theorem td_kernel_true_l (hZFC : M.Models ZFC) (z : M.Domain) :
    Formula.satisfies (⟨Fin.elim0,fun _ => z⟩ : Env M 0) td_kernel_m := by
  simp only [td_kernel_m,Formula.satisfies_conj_iff]
  exact ⟨td_renewal_true_l hZFC (fun _ => z),tc_transfer_true_l hZFC (fun _ => z),
    ee_rebuild_true_l hZFC (fun _ => z),tc_realize_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    td_rigid_true_l (ZFC.models_zf_l hZFC) (fun _ => z),td_recover_true_l (ZFC.models_zf_l hZFC) (fun _ => z),
    td_reply_compare_true_l (ZFC.models_zf_l hZFC) (fun _ => z),eo_kernel_true_l hZFC (fun _ => z)⟩

def td_context_m : Formula 1 1 := lr_rel_m td_kernel_m .newest (fun i => .bound i.succ)
theorem td_context_closed_l : td_context_m.FreeClosed :=
  lr_rel_closed_l _ td_kernel_closed_l _ _ rfl (fun i => Fin.elim0 i)
theorem td_context_delta_l : td_context_m.IsDelta0 := lr_rel_delta_l ..

structure Td_context_d (I : kpair_convention_l.Interpretation M) (ω X R η C : M.Domain) : Prop where
  rank : Rr_truth_d (n := 1) I X R (v_sigma_m (.bound 1) .newest) (Fin.cases C (fun _ => η))
  limit : Rr_truth_d (n := 0) I X R (Formula.isLimitOrdinal .newest) (fun _ => η)
  finite : Rr_truth_d (n := 1) I X R (fs_read_m (.bound 1) .newest) (Fin.cases C (fun _ => ω))
  kernel : Rr_truth_d I X R td_context_m (fun _ => C)

namespace Td_context_d
variable {I : kpair_convention_l.Interpretation M} {ω X R η C : M.Domain} (h : Td_context_d I ω X R η C)
include h

theorem height : M.mem η X := h.rank.elim fun m _ => m 1
theorem member : M.mem C X := h.rank.elim fun m _ => m 0
theorem omega_mem : M.mem ω X := h.finite.elim fun m _ => m 1

theorem finite_l (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx)) :
    Fs_read_d (M := smdl_structure_l I (R := R) nx) ⟨ω,h.omega_mem⟩ ⟨C,h.member⟩ := by
  let N := smdl_structure_l I (R := R) nx
  let v : Fin 2 → N.Domain := fun i => ⟨(Fin.cases C (fun _ => ω) : Fin 2 → M.Domain) i,
    Fin.cases h.member (fun _ => h.omega_mem) i⟩
  exact (fs_read_sat_l ext (⟨v,fun _ => v 0⟩ : Env N 2) (.bound 1) .newest).mp
    ((rr_truth_native_l I nx _ (by simp -implicitDefEqProofs) v).mp h.finite)

theorem kernel_l (nx : ∃ x, M.mem x X)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C,h.member⟩}) :
    Td_kernel_d (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C,h.member⟩ nc) := by
  let N := smdl_structure_l I (R := R) nx
  let Cn : N.Domain := ⟨C,h.member⟩
  let v : Fin 2 → N.Domain := fun i => ⟨(Fin.cases C (fun _ => ω) : Fin 2 → M.Domain) i,
    Fin.cases h.member (fun _ => h.omega_mem) i⟩
  have finite := (rr_truth_native_l I nx (fs_read_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) v).mp h.finite
  simp only [fs_read_m,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff] at finite
  have kernel := (rr_truth_native_l I nx td_context_m td_context_closed_l (fun _ => Cn)).mp h.kernel
  intro ρ
  exact (sc_relative_sat_l finite.1 nc td_kernel_m td_kernel_closed_l ρ
    (⟨fun _ => Cn,fun _ => Cn⟩ : Env N 1) .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp kernel

theorem kernel_mem_l (trans : M.TransitiveSet X) (model : ∃ c, Smem_d I c X R)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) : Td_kernel_d (rt_model_l C nc) := by
  obtain ⟨c,code⟩ := model
  have valid := ((rr_truth_mem_l I trans code td_context_m td_context_delta_l (fun _ => C)).mp h.kernel).2
  intro ρ
  exact (sc_relative_sat_l ct nc td_kernel_m td_kernel_closed_l ρ
    (⟨fun _ => C,fun _ => C⟩ : Env M 1) .newest (fun i => .bound i.succ) rfl (fun i => Fin.elim0 i)).mp valid

omit h in
theorem of_mem_l (hKP : M.Models KP) {c : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    (hη : M.mem η X) (hC : M.mem C X) (rank : Vr_d X η C) (limit : M.IsLimitOrdinal η)
    (finite : Fs_read_d ω C)
    (kernel : Formula.satisfies ((⟨Fin.elim0,fun _ => ω⟩ : Env M 0).push C) td_context_m) :
    Td_context_d I ω X R η C := by
  obtain ⟨rank,limit,finite⟩ := ir_context_data_l I hKP trans model hη hC rank limit finite
  refine ⟨rank,limit,finite,?_⟩
  exact (rr_truth_mem_l I trans model td_context_m td_context_delta_l (fun _ => C)).mpr
    ⟨fun _ => hC,(Formula.closed_env_l td_context_m td_context_closed_l
      (ρ := (⟨Fin.elim0,fun _ => ω⟩ : Env M 0).push C)
      (η := ⟨fun _ => C,fun _ => C⟩) (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel⟩
end Td_context_d

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_context_d.map_l {Ω ω ω' X R c Y S d j η C : M.Domain}
    (h : Td_context_d I ω X R η C) (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (hj : Smap_d I Ω c d X Y j) (hw : Rd_entry_d ω ω' j) :
    ∃ η' C', Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Td_context_d I ω' Y S η' C' := by
  obtain ⟨η',_,hη⟩ := hj.1.1.2.2 η h.height
  obtain ⟨C',_,hC⟩ := hj.1.1.2.2 C h.member
  exact ⟨η',C',hη,hC,h.rank.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (Fin.cases hC (fun _ => hη)),
    h.limit.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (fun _ => hη),
    h.finite.map_l I hZF hΩ mx my hj (by simp -implicitDefEqProofs) (Fin.cases hC (fun _ => hw)),
    h.kernel.map_l I hZF hΩ mx my hj td_context_closed_l (fun _ => hC)⟩

/-- 内外层与新增核均由同一次有限反射产生，保留原参数集合。 -/
theorem td_context_l (hZFC : M.Models ZFC) {ω : M.Domain} (hw : M.IsOmega ω) (A : M.Domain) (Φ : List Lr_formula) :
    ∃ θ X R c K η C, M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R ∧
      Ic_model_d (ZFC.models_zf_l hZFC) ω ω K X R ∧
      Td_context_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R η C ∧
      Fs_read_d ω C ∧ M.mem A C ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨θ,X,R,c,K,η,C,regular,rank,model,source,hη,hC,relative,limit,finite,hA,reflect⟩ :=
    ir_context_l hZFC hw A (⟨0,td_kernel_m,td_kernel_closed_l⟩ :: Φ)
  exact ⟨θ,X,R,c,K,η,C,regular,rank,model,source,
    Td_context_d.of_mem_l (ZF.modelsKP hZF) source.source.transitive model hη hC relative limit finite
      ((reflect ⟨0,td_kernel_m,td_kernel_closed_l⟩ (List.mem_cons_self ..)
        (⟨Fin.elim0,fun _ => ω⟩ : Env M 0) (fun i => Fin.elim0 i)).mp (td_kernel_true_l hZFC ω)),
    finite,hA,fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 反射核直接产生完整 demanding 更新记录

任意当前结构中的原输入都得到同一组实际见证。新旧坐标沿实际量词栈
逐项对应，原 seed 与新 witness 一起保留，供后续固定表项及档案读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Td_kernel_d.renew_l (kernel : Td_kernel_d M) (ρ : Env M 43)
    (seed : Formula.satisfies ρ td_seed0_m) :
    ∃ η : Env M 62, (∀ i : Fin 43, η.bound ⟨19+i.val,by omega⟩ = ρ.bound i) ∧
      Formula.satisfies η td_round0_m := by
  have valid := (Formula.satisfies_conj_iff ..).mp (kernel ⟨Fin.elim0,ρ.free⟩) |>.1
  have result := (Formula.satisfies_imp_iff ..).mp
    ((Formula.satisfies_forallClosure_iff (ℳ := M) ρ.free (.imp td_seed0_m td_successor0_m)).mp valid ρ.bound) seed
  obtain ⟨v,truth⟩ := (rt_exists_sat_l (n := 19) ρ td_witness0_m).mp result
  let η := rt_push_d ρ 19 v
  refine ⟨η,rt_push_old_l ρ v,?_⟩
  apply (Formula.satisfies_conj_iff ..).mpr
  refine ⟨?_,truth⟩
  apply (Formula.satisfies_rename ..).mpr
  exact (Formula.closed_env_l td_seed0_m td_seed0_closed_l
    (ρ := ρ) (η := η.reindex (fun i => ⟨19+i.val,by omega⟩))
    (funext fun i => (rt_push_old_l ρ v i).symm)).mp seed

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生 demanding 更新及其实际施加范围

已恢复的双图输入在所属模型自身调用更新核。全部旧坐标不变，
支撑和完整回答由同次更新产生；秩切片只需包含旧临界点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem td_seed_native_l (hZFC : M.Models ZFC) (ρ : Env M 43) (seed : Formula.satisfies ρ td_seed0_m) :
    ∃ ε : Env M 62, (∀ i : Fin 43, ε.bound ⟨19+i.val,by omega⟩ = ρ.bound i) ∧
      Formula.satisfies ε td_round0_m := by
  have kernel : Td_kernel_d M := fun η =>
    (Formula.closed_env_l td_kernel_m td_kernel_closed_l
      (ρ := ⟨Fin.elim0,fun _ => η.free 0⟩) (η := η) (funext fun i => Fin.elim0 i)).mp
      (td_kernel_true_l hZFC (η.free 0))
  exact kernel.renew_l ρ seed

theorem td_round_native_l (hKP : M.Models KP) (ρ : Env M 62) (valid : Formula.satisfies ρ td_round0_m) :
    M.IsOmega (ρ.bound 19) ∧ M.IsLimitOrdinal (ρ.bound 21) ∧
    M.IsLimitOrdinal (ρ.bound 0) ∧ M.mem (ρ.bound 24) (ρ.bound 0) ∧
    M.mem (ρ.bound 43) (ρ.bound 0) ∧
    ∃ L W X K R F c d Y T j κ' U' E' u',
      Td_image_at_d hKP (ρ.bound 19) (ρ.bound 24) (ρ.bound 21)
        (ρ.bound 27) (ρ.bound 28) (ρ.bound 9) (ρ.bound 35) (ρ.bound 36) (ρ.bound 38)
        (ρ.bound 0) (ρ.bound 3) (ρ.bound 4) (ρ.bound 40) (ρ.bound 42)
        (ρ.bound 16) (ρ.bound 17) (ρ.bound 18) (fun i => ρ.bound ⟨55+i.val,by omega⟩)
        L W X K R F c d Y T j κ' U' E' u' := by
  obtain ⟨seed,answer⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  have omega := (Formula.satisfies_isOmega_iff ..).mp seed.1
  have woodin := (woodin_sat_l (kp_pair_l hKP) hKP.1 ..).mp seed.2.2.1
  obtain ⟨_,_,_,_,regular,_⟩ := woodin
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at answer
  obtain ⟨above,growth,_,_,_,_,language,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,image⟩ := answer
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limit := (Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1
  obtain ⟨X,K,R,L,F,c,d,Y,T,j,κ',U',E',u',rank,source,hL,hκ,hτ,⟨W,rankW,hDW⟩,rest⟩ :=
    (td_image_sat_l hKP ..).mp image
  have slots : (fun i : Fin 7 => Fin.cases (ρ.bound 55) (Fin.cases (ρ.bound 56)
      (Fin.cases (ρ.bound 57) (Fin.cases (ρ.bound 58) (Fin.cases (ρ.bound 59)
        (Fin.cases (ρ.bound 60) (fun _ => ρ.bound 61)))))) i) =
      (fun i => ρ.bound ⟨55+i.val,by omega⟩) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [tt_eval_cases_l,Term.eval_bound] at rest
  refine ⟨omega,regular.isLimitOrdinal,limit,growth,above,L,W,X,K,R,F,c,d,Y,T,j,κ',U',E',u',
    rank,source,hL,hκ,hτ,rankW,hDW,?_⟩
  rw [← slots]
  exact rest

theorem td_round_native_scope_l (hZF : M.Models ZF) {α B : M.Domain}
    (ρ : Env M 62) (valid : Formula.satisfies ρ td_round0_m)
    (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) α B) (limit : M.IsLimitOrdinal α)
    (member : M.mem (ρ.bound 24) B) :
    M.mem (ρ.bound 35) B ∧ M.mem (ρ.bound 36) B ∧ M.mem (ρ.bound 38) B ∧
      M.mem (ρ.bound 27) (ρ.bound 19) ∧ M.mem (ρ.bound 9) (ρ.bound 19) ∧
      M.mem (ρ.bound 40) (ρ.bound 19) ∧ M.mem (ρ.bound 42) (ρ.bound 19) ∧
      ∀ i : Fin 7, M.mem (ρ.bound ⟨55+i.val,by omega⟩) (ρ.bound 19) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨seed,answer⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨hw,_,_,_,_,_,_,successor,_,_,_,realized,language,_⟩ := seed
  have omega := (Formula.satisfies_isOmega_iff ..).mp hw
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  obtain ⟨domain,hκ,base,constants,_⟩ := language
  have hκ := (Formula.satisfies_isLimitOrdinal_iff ..).mp hκ
  have base := (v_sigma_sat_l (ZF.modelsKP hZF) ..).mp base
  have constants := (tt_constants0_sat_l hZF.1 ..).mp constants
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,Formula.satisfies_conj_iff] at domain
  have pool := (tt_pool_sat_l I (ZF.modelsKP hZF) ..).mp domain.2.1
  have type := (tt_realized_sat_l I (ZF.modelsKP hZF) ..).mp realized
  have hU := tt_constants_rank_l hZF rank limit
    (ZF.v_ordinal_height_l hZF rank hκ.1 member) base constants
  have hwB := v_subset_mem_l I rank member (omega.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  have hP := type.pool.rank_mem_l (ZF.modelsKP hZF) omega rank limit hwB type.finite hU
  have succ := (Formula.satisfies_isSuccessor_iff ..).mp successor
  have hq := omega.transitive (ZF.modelsKP hZF) _ type.finite _ succ.predecessor_mem
  have hE := pool.rank_mem_l (ZF.modelsKP hZF) omega rank limit hwB hq hU
  have hu := v_subset_mem_l I rank hP (fun x hx => ((type.truth x).mp hx).1)
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at answer
  obtain ⟨_,_,_,_,_,_,_,reply,_,_,_,_,_,_,_,_,_,_,_,_,hb,hz,h₀,h₁,h₂,h₃,h₄,h₅,h₆,_⟩ := answer
  have reply := (tt_realized_sat_l I (ZF.modelsKP hZF) ..).mp reply
  exact ⟨hU,hE,hu,hq,reply.finite,hb,hz,Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂
    (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (Fin.cases h₆ (fun i => Fin.elim0 i)))))))⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 完整轮的施加范围

包含旧 κ 的极限秩段容纳原常量域、q 元查询池及 n 元完整类型。
回答的 m 元数与程序槽来自同一轮，不能与 q、n 混同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_round_members_l {ω η C α B : M.Domain} (hω : M.IsOmega ω)
    (rankC : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 62) (hw : (ρ.bound 19).val = ω)
    (rank : V_d I α B) (limit : M.IsLimitOrdinal α) (member : M.mem (ρ.bound 24).val B)
    (valid : Formula.satisfies ρ td_round0_m) :
    M.mem (ρ.bound 35).val B ∧ M.mem (ρ.bound 36).val B ∧ M.mem (ρ.bound 38).val B ∧
      M.mem (ρ.bound 27).val ω ∧ M.mem (ρ.bound 28).val ω ∧ M.mem (ρ.bound 9).val ω ∧
      M.mem (ρ.bound 40).val ω ∧ M.mem (ρ.bound 42).val ω ∧
      ∀ i : Fin 7, M.mem (ρ.bound ⟨55+i.val,by omega⟩).val ω := by
  obtain ⟨seed,answer⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,successor,_,_,_,realized,language,_⟩ := seed
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,
    Formula.satisfies_conj_iff] at language
  obtain ⟨domain,hκ,base,constants,_⟩ := language
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 24)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hκ)
  have hκα := ZF.v_ordinal_height_l hZF rank hκ.1 member
  obtain ⟨A,rA⟩ := ZF.v_exists_l I hZF hκ.1
  have hA := ZF.v_mem_l I hZF rA rankC
    (ZF.v_ordinal_height_l hZF rankC hκ.1 (ρ.bound 24).property)
  have base : Vr_d C (ρ.bound 24).val (ρ.bound 34).val :=
    (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp base
  have eq := vr_agree_l hZF fs.transitive (ρ.bound 34).property rA (fs.transitive A hA) base
  have full : V_d I (ρ.bound 24).val (ρ.bound 34).val := by rw [eq]; exact rA
  have constants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) _).mp constants)
  have hU : M.mem (ρ.bound 35).val B := tt_constants_rank_l hZF rank limit hκα full constants
  have hwB : M.mem ω B := v_subset_mem_l I rank member
    (hω.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  simp only [tt_realized_m,Formula.satisfies_bind,tt_realized0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at realized
  obtain ⟨_,hn,_,_,_,pool,truth⟩ := realized
  have hn : M.mem (ρ.bound 28).val ω := hw ▸ hn
  obtain ⟨A₀,E,_,_,names,seq,product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc _ _ _ _ _ (by exact hw)).mp pool
  have actual : Tt_pool_d I ω (ρ.bound 28).val (ρ.bound 35).val (ρ.bound 37).val :=
    ⟨A₀,E,names,seq,product⟩
  have hP := actual.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hn hU
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,
    Formula.satisfies_conj_iff] at domain
  obtain ⟨A₁,E₁,_,_,names₁,seq₁,product₁⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc _ _ _ _ _ (by exact hw)).mp domain.2.1
  have small : Tt_pool_d I ω (ρ.bound 27).val (ρ.bound 35).val (ρ.bound 36).val :=
    ⟨A₁,E₁,names₁,seq₁,product₁⟩
  have successor : (rt_model_l C nc).SuccessorOf (ρ.bound 28) (ρ.bound 27) :=
    (Formula.satisfies_isSuccessor_iff ..).mp successor
  have hq := hω.transitive (ZF.modelsKP hZF) _ hn _ successor.predecessor_mem
  have hE := small.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hq hU
  simp only [tt_truth_m,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at truth
  have sub : M.MemberSubset (ρ.bound 38).val (ρ.bound 37).val := fun x hx =>
    ((truth ⟨x,fs.transitive _ (ρ.bound 38).property x hx⟩).mp hx).1
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at answer
  obtain ⟨_,_,_,_,_,_,_,reply,_,_,_,_,_,_,_,_,_,_,_,_,hb,hz,h₀,h₁,h₂,h₃,h₄,h₅,h₆,_⟩ := answer
  simp only [tt_realized_m,Formula.satisfies_bind,tt_realized0_m,Formula.satisfies_conj_iff] at reply
  exact ⟨hU,hE,v_subset_mem_l I rank hP sub,hq,hn,hw ▸ reply.2.1,hw ▸ hb,hw ▸ hz,
    Fin.cases (hw ▸ h₀) (Fin.cases (hw ▸ h₁) (Fin.cases (hw ▸ h₂) (Fin.cases (hw ▸ h₃)
      (Fin.cases (hw ▸ h₄) (Fin.cases (hw ▸ h₅) (Fin.cases (hw ▸ h₆)
        (fun i => Fin.elim0 i)))))))⟩

end YesMetaZFC.SetTheory.LargeCardinal
