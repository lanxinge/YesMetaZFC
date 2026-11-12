import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp

/-! # 同一树中两组辅助字母的最小载体

沿已有节点编码 (x,(a,b)) 读取真实出现值。载体不来自额外参数，空树
及只有空根的树没有辅助字母；两组最小载体都由同一树实际分离得到。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Td_letter_d (side : Bool) (S z : M.Domain) : Prop :=
  ∃ q i p x a b t, M.mem q S ∧ Rd_entry_d i p q ∧
    KPair_d M p x t ∧ KPair_d M t a b ∧ z = (if side then b else a)

def td_letter_m {d} (side : Bool) (S z : Term d) : Formula 1 d := set[d] ⟪
  ∃ q ∈ ⌜S⌝ₛ, ∃ i p x a b t,
    ⌜rd_entry0_m⌝ₚ(i,p,q) ∧ ⌜kpair0_m⌝ₚ(p,x,t) ∧ ⌜kpair0_m⌝ₚ(t,a,b) ∧
    ⌜fun a b z => Formula.extensionalEq z (if side then b else a)⌝ₚ(a,b,⌜z⌝ₛ)⟫

@[simp] theorem td_letter_closed_l {d} (side : Bool) (S z : Term d)
    (hS : S.freeSupport = []) (hz : z.freeSupport = []) : (td_letter_m side S z).FreeClosed := by
  cases side <;> simp -implicitDefEqProofs [td_letter_m,Definitional.Formula.FreeClosed,hS,hz]

theorem td_letter_sat_l (hE : Extensional M) {d} (ρ : Env M d) (side : Bool) (S z : Term d) :
    Formula.satisfies ρ (td_letter_m side S z) ↔ Td_letter_d side (S.eval ρ) (z.eval ρ) := by
  cases side <;> simp only [td_letter_m,Td_letter_d,Formula.satisfies_existsMem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,rd_entry0_sat_l hE,kpair0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken]
  all_goals
    exact ⟨fun ⟨q,hq,i,p,x,a,b,t,hi,hp,ht,eq⟩ => ⟨q,i,p,x,a,b,t,hq,hi,hp,ht,eq⟩,
      fun ⟨q,i,p,x,a,b,t,hq,hi,hp,ht,eq⟩ => ⟨q,hq,i,p,x,a,b,t,hi,hp,ht,eq⟩⟩

theorem Td_letter_d.mem_l {side : Bool} {S z X : M.Domain}
    (h : Td_letter_d side S z) (trans : M.TransitiveSet X) (hS : M.mem S X) : M.mem z X := by
  obtain ⟨q,i,p,x,a,b,t,hq,hi,hp,ht,eq⟩ := h
  have hqX := trans S hS q hq
  have hpX := (rd_entry_transitive_l trans hqX hi).2
  have htX := (hp.mem_l M trans hpX).2
  have pair := ht.mem_l M trans htX
  cases side with
  | false => exact eq.symm ▸ pair.1
  | true => exact eq.symm ▸ pair.2

/-- 实际出现值的全部见证都在树的传递容器中，无需源的替换或幂集。 -/
theorem td_letter_source_l {X : M.Domain} (trans : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) (hE : Extensional M) {d}
    (ρ : Env (rt_model_l X nx) d) (side : Bool) (S z : Term d) :
    Formula.satisfies ρ (td_letter_m side S z) ↔ Td_letter_d side (S.eval ρ).val (z.eval ρ).val := by
  have entry {n} (η : Env (rt_model_l X nx) n) (a b f : Term n) :
      Formula.satisfies η (rd_entry0_m a b f) ↔
        Rd_entry_d (a.eval η).val (b.eval η).val (f.eval η).val :=
    (rt_model_delta_l trans nx (rd_entry0_delta_l ..) η).trans (by
      simpa only [@eval_image_env_l (rt_model_l X nx) M Subtype.val] using
        rd_entry0_sat_l hE (image_env_l Subtype.val η) a b f)
  have pair {n} (η : Env (rt_model_l X nx) n) (p a b : Term n) :
      Formula.satisfies η (kpair0_m p a b) ↔
        KPair_d M (p.eval η).val (a.eval η).val (b.eval η).val :=
    (rt_model_delta_l trans nx (kpair0_delta_l ..) η).trans (by
      simpa only [@eval_image_env_l (rt_model_l X nx) M Subtype.val] using
        kpair0_sat_l hE (image_env_l Subtype.val η) p a b)
  cases side <;> simp only [td_letter_m,Td_letter_d,Formula.satisfies_existsMem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry,pair,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE trans nx),
    Definitional.Term.eval_weaken]
  all_goals
    constructor
    · rintro ⟨q,hq,i,p,x,a,b,t,hi,hp,ht,eq⟩
      exact ⟨q.val,i.val,p.val,x.val,a.val,b.val,t.val,hq,hi,hp,ht,congrArg Subtype.val eq⟩
    · rintro ⟨q,i,p,x,a,b,t,hq,hi,hp,ht,eq⟩
      have hqX := trans _ (S.eval ρ).property q hq
      have bounds := rd_entry_transitive_l trans hqX hi
      have pBounds := hp.mem_l M trans bounds.2
      have tBounds := ht.mem_l M trans pBounds.2
      exact ⟨⟨q,hqX⟩,hq,⟨i,bounds.1⟩,⟨p,bounds.2⟩,⟨x,pBounds.1⟩,
        ⟨a,tBounds.1⟩,⟨b,tBounds.2⟩,⟨t,pBounds.2⟩,hi,hp,ht,Subtype.ext eq⟩

def Td_alphabet_d (S A B : M.Domain) : Prop :=
  (∀ z, M.mem z A ↔ Td_letter_d false S z) ∧ (∀ z, M.mem z B ↔ Td_letter_d true S z)

/-! 同一树上的最小字母域由外延性唯一确定。 -/
theorem Td_alphabet_d.ext_l (hE : Extensional M)
    {S A B A' B' : M.Domain}
    (h : Td_alphabet_d S A B) (h' : Td_alphabet_d S A' B') :
    A = A' ∧ B = B' := by
  constructor
  · apply hE.eq_of_same_members
    intro z
    exact ⟨fun hz => (h'.1 z).mpr ((h.1 z).mp hz),
      fun hz => (h.1 z).mpr ((h'.1 z).mp hz)⟩
  · apply hE.eq_of_same_members
    intro z
    exact ⟨fun hz => (h'.2 z).mpr ((h.2 z).mp hz),
      fun hz => (h.2 z).mpr ((h'.2 z).mp hz)⟩

/-- 两个最小辅助字母载体由同一树的传递闭包内实际分离。 -/
theorem td_alphabet_exists_l (hZF : M.Models ZF) (S : M.Domain) : ∃ A B, Td_alphabet_d S A B := by
  obtain ⟨T,trans,hST,_⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF S
  have build (side : Bool) : ∃ A, ∀ z, M.mem z A ↔ Td_letter_d side S z := by
    let ρ : Env M 1 := ⟨fun _ => S,fun _ => S⟩
    let φ : UnarySchema 1 := { body := td_letter_m side (.bound 1) .newest }
    obtain ⟨A,ha⟩ := ZF.separation_exists_d hZF φ ρ T
    refine ⟨A,fun z => (ha z).trans ?_⟩
    exact ⟨fun hz => (td_letter_sat_l hZF.1 ..).mp hz.2,
      fun hz => ⟨hz.mem_l trans hST,(td_letter_sat_l hZF.1 ..).mpr hz⟩⟩
  obtain ⟨A,ha⟩ := build false
  obtain ⟨B,hb⟩ := build true
  exact ⟨A,B,ha,hb⟩

/-- 同一完整节点的两张辅助图自动落在从该树恢复的对应最小字母载体。 -/
theorem Td_alphabet_d.node_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {S A B k s a b : M.Domain} (alph : Td_alphabet_d S A B) (node : Tg_node_d I k S s a b) :
    (∀ i z, Rd_entry_d i z a → M.mem z A) ∧ (∀ i z, Rd_entry_d i z b → M.mem z B) := by
  obtain ⟨hs,ha,hb,q,hq,join⟩ := node
  have codes : I.Codes = KPair_d M := by
    funext p x y
    let ρ : Env M 3 := ⟨fun i => [p,x,y].get i,fun _ => p⟩
    exact propext ((I.realizes ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (kpair_sat_l M hE ρ (.bound 0) (.bound 1) (.bound 2)))
  have point {i z f : M.Domain} : Rd_entry_d i z f ↔ M.PairMember I i z f := by
    change (∃ p, KPair_d M p i z ∧ M.mem p f) ↔ ∃ p, I.Codes p i z ∧ M.mem p f
    rw [codes]
  constructor
  · intro i z iz
    have iz := point.mp iz
    obtain ⟨x,y,w,t,p,_,iy,_,ht,hp,ip⟩ := join.2 i ((ha.2 i).mpr ⟨z,iz⟩)
    have eq := ha.1.2 i y z iy iz
    rw [codes] at ht hp
    exact (alph.1 z).mpr ⟨q,i,p,x,y,w,t,hq,point.mpr ip,hp,ht,eq.symm⟩
  · intro i z iz
    have iz := point.mp iz
    obtain ⟨x,y,w,t,p,_,_,iw,ht,hp,ip⟩ := join.2 i ((hb.2 i).mpr ⟨z,iz⟩)
    have eq := hb.1.2 i w z iw iz
    rw [codes] at ht hp
    exact (alph.2 z).mpr ⟨q,i,p,x,y,w,t,hq,point.mpr ip,hp,ht,eq.symm⟩

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.Internal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Td_alphabet_d.source_l
    (hE : Extensional M)
    {X : M.Domain} (trans : M.TransitiveSet X)
    (nx : Nonempty {x : M.Domain // M.mem x X})
    {S A B : M.Domain} (hS : M.mem S X) (hA : M.mem A X) (hB : M.mem B X)
    (alphabet : Td_alphabet_d S A B) :
    Td_alphabet_d (M := rt_model_l X nx)
      ⟨S, hS⟩ ⟨A, hA⟩ ⟨B, hB⟩ := by
  let N := rt_model_l X nx
  let extN := rt_model_ext_l hE trans nx
  have letter (side : Bool) (z : N.Domain) :
      Td_letter_d (M := N) side ⟨S, hS⟩ z ↔
        Td_letter_d (M := M) side S z.val := by
    let ρ : Env N 2 :=
      ⟨Fin.cases z (fun _ => ⟨S, hS⟩), fun _ => ⟨S, hS⟩⟩
    have hρ1 : ρ.bound (1 : Fin 2) = ⟨S, hS⟩ := by rfl
    have hρ0 : ρ.bound (0 : Fin 2) = z := by rfl
    have hletter := (td_letter_sat_l extN ρ side (.bound 1) (.bound 0)).symm.trans
      (td_letter_source_l trans nx hE ρ side (.bound 1) (.bound 0))
    change Td_letter_d (M := N) side (ρ.bound (1 : Fin 2)) (ρ.bound (0 : Fin 2)) ↔
      Td_letter_d (M := M) side (ρ.bound (1 : Fin 2)).val (ρ.bound (0 : Fin 2)).val at hletter
    rw [hρ1, hρ0] at hletter
    exact hletter
  constructor
  · intro z
    change M.mem z.val A ↔ Td_letter_d (M := N) false ⟨S, hS⟩ z
    exact (alphabet.1 z.val).trans (letter false z).symm
  · intro z
    change M.mem z.val B ↔ Td_letter_d (M := N) true ⟨S, hS⟩ z
    exact (alphabet.2 z.val).trans (letter true z).symm

theorem Td_alphabet_d.carrier_mem_l
    (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
    {δ V S T A B : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hT : M.mem T V)
    (transT : M.TransitiveSet T) (hST : M.mem S T)
    (alphabet : Td_alphabet_d S A B) :
    M.mem A V ∧ M.mem B V := by
  obtain ⟨P, hP⟩ := v_power_exists_l I (ZF.modelsKP hZF) hV hT
  have hPm : M.mem P V := v_power_mem_l I hV hδ hT hP
  have subA : M.MemberSubset A T := by
    intro z hz
    exact Td_letter_d.mem_l ((alphabet.1 z).mp hz) transT hST
  have subB : M.MemberSubset B T := by
    intro z hz
    exact Td_letter_d.mem_l ((alphabet.2 z).mp hz) transT hST
  exact ⟨(v_transitive_l I hV) P hPm A ((hP A).mpr subA),
    (v_transitive_l I hV) P hPm B ((hP B).mpr subB)⟩

/-! 直接从树根属于极限秩层恢复字母载体的层内归属。

先把根的幂集放回同一极限层，再从该幂集的层展开取得一个传递层；
这样不需要外部可数性或额外的传递闭包假设。 -/
theorem Td_alphabet_d.carrier_mem_rank_l
    (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
    {δ V S A B : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hS : M.mem S V)
    (alphabet : Td_alphabet_d S A B) :
    M.mem A V ∧ M.mem B V := by
  obtain ⟨P, hP⟩ := v_power_exists_l I (ZF.modelsKP hZF) hV hS
  have hPV : M.mem P V := v_power_mem_l I hV hδ hS hP
  have hSP : M.mem S P := (hP S).mpr (fun _ hx => hx)
  obtain ⟨β, W, hβ, hW, hPW⟩ := (ZF.v_unfold_l I hZF hV P).mp hPV
  have hSW : M.mem S W := hPW S hSP
  have hWV : M.mem W V := ZF.v_mem_l I hZF hW hV hβ
  exact Td_alphabet_d.carrier_mem_l I hZF hV hδ hWV (v_transitive_l I hW) hSW alphabet

end YesMetaZFC.SetTheory.Internal

/-! ## 同一树的两个最小辅助字母域的一阶表示

两侧均精确读取原树中出现的值，不把载体包含关系替代最小性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def td_alphabet_m {d} (S A B : Term d) : Formula 1 d := set[d] ⟪
  (∀ z, z ∈ ⌜A⌝ₛ ↔ ⌜(td_letter_m false)⌝ₚ(⌜S⌝ₛ,z)) ∧
  (∀ z, z ∈ ⌜B⌝ₛ ↔ ⌜(td_letter_m true)⌝ₚ(⌜S⌝ₛ,z))⟫
derive_free_closed td_alphabet_m

theorem td_alphabet_sat_l (hE : Extensional M) {d} (ρ : Env M d) (S A B : Term d) :
    Formula.satisfies ρ (td_alphabet_m S A B) ↔
      Td_alphabet_d (S.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [td_alphabet_m,Td_alphabet_d,Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    td_letter_sat_l hE,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## demanding 查询所用的内在完整树性质

直接检查树内每个有限三元组图及全部有限限制。公式不量化整张有限列
空间，因而可在真实后继秩层解释；在 ZF 中它与通常的树表示实际互通。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

structure Td_tree_d (I : kpair_convention_l.Interpretation M) (ω A S : M.Domain) : Prop where
  nodes : ∀ q, M.mem q S → ∃ n, M.mem n ω ∧ Tg_graph_d I n q ∧
    ∀ i p, M.PairMember I i p q → ∃ x a b t, M.mem x A ∧ I.Codes p x t ∧ I.Codes t a b
  restriction : ∀ q t n, M.mem q S → M.mem n ω → Tg_graph_d I n t → M.MemberSubset t q → M.mem t S

def td_tree_m {d} (ω A S : Term d) : Formula 1 d := set[d] ⟪
  (∀ q ∈ ⌜S⌝ₛ, ∃ n ∈ ⌜ω⌝ₛ, ⌜tg_graph_m⌝ₚ(n,q) ∧
    (∀ i p, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,p,q) →
      ∃ x a b t, x ∈ ⌜A⌝ₛ ∧ ⌜kpair_convention_l.code⌝ₚ(p,x,t) ∧ ⌜kpair_convention_l.code⌝ₚ(t,a,b))) ∧
  (∀ q ∈ ⌜S⌝ₛ, ∀ t n, n ∈ ⌜ω⌝ₛ → ⌜tg_graph_m⌝ₚ(n,t) → t ⊆ q → t ∈ ⌜S⌝ₛ)⟫
derive_free_closed td_tree_m

theorem td_tree_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω A S : Term d) :
    Formula.satisfies ρ (td_tree_m ω A S) ↔ Td_tree_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) := by
  simp only [td_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,tg_graph_sat_l I hE,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,
    I.satisfies_code_iff,Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b⟩ => ⟨a,fun q t n hq => b q hq t n⟩,
    fun h => ⟨h.nodes,fun q hq t n => h.restriction q t n hq⟩⟩

/-- 原有限列空间、笛卡尔积及树封闭性实际产生内在树证书。 -/
theorem td_tree_of_l (I : kpair_convention_l.Interpretation M)
    {ω X A B P Y F S : M.Domain} (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P A B) (triple : M.IsCartesianProduct I Y X P) : Td_tree_d I ω X S := by
  refine ⟨?_,?_⟩
  · intro q hq
    obtain ⟨n,hn,fn⟩ := (space q).mp (tree.1 q hq)
    refine ⟨n,hn,⟨fn.1,fn.2.1⟩,fun i p ip => ?_⟩
    obtain ⟨x,hx,t,ht,hp⟩ := (triple p).mp (fn.output_mem_of_pairMember ip)
    obtain ⟨a,ha,b,hb,code⟩ := (pair t).mp ht
    exact ⟨x,a,b,t,hx,hp,code⟩
  · intro q t n hq hn graph sub
    obtain ⟨m,hm,fn⟩ := (space q).mp (tree.1 q hq)
    have bound i p (ip : M.PairMember I i p t) : M.mem p Y := by
      obtain ⟨r,code,hr⟩ := ip
      exact fn.output_mem_of_pairMember ⟨r,code,sub r hr⟩
    have ft : M.IsSetFunctionFromTo I t n Y := ⟨graph.1,graph.2,
      fun i hi => ((graph.2 i).mp hi).imp fun p hp => ⟨bound i p hp,hp⟩⟩
    exact tree.2 q hq t ((space t).mpr ⟨n,hn,ft⟩) sub

/-- 真正秩层对已有对象的子集封闭，完整有限限制因而能双向读出。 -/
theorem td_tree_source_l {X : M.Domain} (trans : M.TransitiveSet X)
    (nx : Nonempty {x // M.mem x X}) (hE : Extensional M)
    (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
    (subsets : ∀ a b, M.mem a X → M.MemberSubset b a → M.mem b X)
    {d} (ρ : Env (rt_model_l X nx) d) (ω A S : Term d) :
    Formula.satisfies ρ (td_tree_m ω A S) ↔
      Td_tree_d (kpair_interpretation_l M hE hP) (ω.eval ρ).val (A.eval ρ).val (S.eval ρ).val := by
  let I := kpair_interpretation_l M hE hP
  simp only [td_tree_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,tg_graph_source_l trans nx hE hP,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,rt_entry_formula_l trans nx hE,
    Formula.satisfies_exists_iff,rt_kpair_formula_l trans nx hE,
    Formula.satisfies_mem_iff,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨nodes,restricted⟩
    refine ⟨?_,?_⟩
    · intro q hq
      have hqX := trans _ (S.eval ρ).property q hq
      obtain ⟨n,hn,graph,triples⟩ := nodes ⟨q,hqX⟩ hq
      refine ⟨n.val,hn,graph,fun i p ip => ?_⟩
      have hp := rd_entry_transitive_l trans hqX ip
      obtain ⟨x,a,b,t,hx,first,second⟩ := triples ⟨i,hp.1⟩ ⟨p,hp.2⟩ ip
      exact ⟨x.val,a.val,b.val,t.val,hx,first,second⟩
    · intro q t n hq hn graph sub
      have hqX := trans _ (S.eval ρ).property q hq
      exact restricted ⟨q,hqX⟩ hq ⟨t,subsets q t hqX sub⟩
        ⟨n,trans _ (ω.eval ρ).property n hn⟩ hn graph (fun x hx => sub x.val hx)
  · intro tree
    constructor
    · intro q hq
      obtain ⟨n,hn,graph,triples⟩ := tree.nodes q.val hq
      refine ⟨⟨n,trans _ (ω.eval ρ).property n hn⟩,hn,graph,?_⟩
      intro i p ip
      obtain ⟨x,a,b,t,hx,first,second⟩ := triples i.val p.val ip
      have hp := first.mem_l M trans p.property
      have ht := second.mem_l M trans hp.2
      exact ⟨⟨x,hp.1⟩,⟨a,ht.1⟩,⟨b,ht.2⟩,⟨t,hp.2⟩,hx,first,second⟩
    · intro q hq t n hn graph sub
      exact tree.restriction q.val t.val n.val hq hn graph
        (fun x hx => sub ⟨x,trans t.val t.property x hx⟩ hx)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 内在树实际恢复通常表示，并使两个辅助域恰为该树的最小出现域。 -/
theorem Td_tree_d.space_l {ω X S : M.Domain} (tree : Td_tree_d I ω X S) (hω : M.IsOmega ω) :
    ∃ A B P Y F, Td_alphabet_d S A B ∧ M.IsCartesianProduct I P A B ∧
      M.IsCartesianProduct I Y X P ∧ Fseq_space_d I ω Y F ∧ Tree_d F S := by
  obtain ⟨A,B,alph⟩ := td_alphabet_exists_l hZF S
  obtain ⟨P,pair⟩ := ZF.exists_cartesianProduct hZF I A B
  obtain ⟨Y,triple⟩ := ZF.exists_cartesianProduct hZF I X P
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hω Y
  have members q (hq : M.mem q S) : M.mem q F := by
    obtain ⟨n,hn,graph,triples⟩ := tree.nodes q hq
    have bound i p (ip : Rd_entry_d i p q) : M.mem p Y := by
      obtain ⟨x,a,b,t,hx,hp,ht⟩ := triples i p ip
      have aA := (alph.1 a).mpr ⟨q,i,p,x,a,b,t,hq,ip,hp,ht,rfl⟩
      have bB := (alph.2 b).mpr ⟨q,i,p,x,a,b,t,hq,ip,hp,ht,rfl⟩
      exact (triple p).mpr ⟨x,hx,t,(pair t).mpr ⟨a,aA,b,bB,ht⟩,hp⟩
    exact (space q).mpr ⟨n,hn,graph.1,graph.2,
      fun i hi => ((graph.2 i).mp hi).imp fun p hp => ⟨bound i p hp,hp⟩⟩
  refine ⟨A,B,P,Y,F,alph,pair,triple,space,members,?_⟩
  intro q hq t ht sub
  obtain ⟨n,hn,fn⟩ := (space t).mp ht
  exact tree.restriction q t n hq hn ⟨fn.1,fn.2.1⟩ sub

end YesMetaZFC.SetTheory.Internal

/-! ## 7.1 的指定待回应标签及实际类型成员

待回应对象严格是 (k,z)，且 z 属于由同一完整树恢复的最小第一辅助域。
固定第一字母表 A 是真实低常量，完整树的每个三元组首坐标均属于 A；
实际秩实现供应全部有限限制读取所需的子集闭包。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def Td_pending_d (I : kpair_convention_l.Interpretation M) (ω A k S p : M.Domain) : Prop :=
  Td_tree_d I ω A S ∧ ∃ z, KPair_d M p k z ∧ Td_letter_d false S z

def td_pending_m {d} (ω A k S p : Term d) : Formula 1 d :=
  .conj (td_tree_m ω A S) (.existsE (.conj (kpair0_m p.weaken k.weaken .newest)
    (td_letter_m false S.weaken .newest)))
derive_free_closed td_pending_m

theorem td_pending_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω A k S p : Term d) :
    Formula.satisfies ρ (td_pending_m ω A k S p) ↔ Td_pending_d I (ω.eval ρ) (A.eval ρ) (k.eval ρ) (S.eval ρ) (p.eval ρ) := by
  simp only [td_pending_m,Td_pending_d,Formula.satisfies_conj_iff,td_tree_sat_l I hE,
    Formula.satisfies_exists_iff,kpair0_sat_l hE,td_letter_sat_l hE,Definitional.Term.eval_weaken]
  rfl

def Td_pending_query_d (I : kpair_convention_l.Interpretation M) (ω A e n j U D k q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ ν X c R r δ T S p, V_d I ν X → Smem_d I c X R →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r → Rd_entry_d j p r →
      (M.mem q T ↔ Td_pending_d I ω A k S p)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_pending_source_l {ν X : M.Domain} (rank : V_d I ν X)
    (nx : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X nx) d) (ω A k S p : Term d) :
    Formula.satisfies ρ (td_pending_m ω A k S p) ↔
      Td_pending_d I (ω.eval ρ).val (A.eval ρ).val (k.eval ρ).val (S.eval ρ).val (p.eval ρ).val := by
  have trans := v_transitive_l I rank
  have pair {n} (η : Env (rt_model_l X nx) n) (a b c : Term n) :
      Formula.satisfies η (kpair0_m a b c) ↔ KPair_d M (a.eval η).val (b.eval η).val (c.eval η).val :=
    (rt_model_delta_l trans nx (kpair0_delta_l ..) η).trans (by
      simpa only [@eval_image_env_l (rt_model_l X nx) M Subtype.val] using
        kpair0_sat_l hZF.1 (image_env_l Subtype.val η) a b c)
  simp only [td_pending_m,Td_pending_d,Formula.satisfies_conj_iff,
    td_tree_source_l trans nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
      (fun a b ha sub => v_subset_mem_l I rank ha sub),
    Formula.satisfies_exists_iff,pair,td_letter_source_l trans nx hZF.1,Definitional.Term.eval_weaken]
  apply and_congr_right
  intro _
  exact ⟨fun ⟨z,hz,letter⟩ => ⟨z.val,hz,letter⟩,
    fun ⟨z,hz,letter⟩ => ⟨⟨z,(hz.mem_l M trans (p.eval ρ).property).2⟩,hz,letter⟩⟩

/-- 已选第一辅助字母真实出现，完整树的限制封闭性因此给出空根。 -/
theorem Td_pending_d.root_l {ω A k S p e : M.Domain} (hω : M.IsOmega ω)
    (pending : Td_pending_d I ω A k S p) (empty : ∀ x, ¬ M.mem x e) : M.mem e S := by
  obtain ⟨tree,z,_,q,i,t,x,a,b,v,hq,_⟩ := pending
  exact tree.restriction q e e hq (num_mem_l hZF.1 hω (show Num_d 0 e from empty))
    (tg_graph_empty_l I empty) (fun x hx => (empty x hx).elim)

/-- 查询码保留原第一字母表 A；不依赖所选 z 或具体实现模型。 -/
theorem tt_demand_pending_query_l {ω A e n j U D k : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (he : M.mem e n) (hj : M.mem j n)
    (pool : Tt_pool_d I ω n U D) (hωU : M.mem ω U) (hAU : M.mem A U) (hk : M.mem k U) :
    ∃ q, Td_pending_query_d I ω A e n j U D k q := by
  obtain ⟨N,C,names,sequences,product⟩ := pool
  obtain ⟨b,σ,hb,nb,bound,_,columns⟩ := tt_column_build_l hZF hω hn 3
  let a : Fin 3 → M.Domain := fun i => [ω,A,k].get i
  have ha : ∀ i, M.mem (a i) U := Fin.cases hωU (Fin.cases hAU (Fin.cases hk (fun i => Fin.elim0 i)))
  obtain ⟨v,hv⟩ := Classical.axiomOfChoice (fun i => (I).total (a i) (a i))
  obtain ⟨J,column,original,params⟩ := columns U N names v
    (fun i => (names (v i)).mpr (Or.inr (Or.inr ⟨a i,ha i,hv i⟩)))
  obtain ⟨z₀,empty⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have base : Sfm_d I ω z₀ z₀ := ⟨num_mem_l hZF.1 hω (show Num_d 0 z₀ from empty),
    Structure.IsSequenceOfLength.empty I empty,fun _ _ h => h.elim fun p hp => (empty p hp.2).elim⟩
  let φ : Formula 1 5 := td_pending_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  have closed : φ.FreeClosed := td_pending_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  let slots : Fin 5 → M.Domain := fun i => [σ 0,σ 1,σ 2,e,j].get i
  have bounded : ∀ i, M.mem (slots i) b := Fin.cases (bound 0) (Fin.cases (bound 1)
    (Fin.cases (bound 2) (Fin.cases (nb e he) (Fin.cases (nb j hj) (fun i => Fin.elim0 i)))))
  obtain ⟨m,G,u,build,compile⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ closed) slots hb bounded base
  obtain ⟨f,formCode⟩ := (I).total G u
  have form : Sformula_d I ω f m G u := ⟨formCode,build.program,build.root⟩
  obtain ⟨z,code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨q,cq⟩ := (I).total z J
  have hz := sc_num_natural_l I hZF hω code
  have hq := (product q).mpr ⟨z,hz,J,(sequences J).mpr ⟨b,hb,column⟩,cq⟩
  refine ⟨q,hq,fun ν X c R r δ T S p rank model type rS rp => ?_⟩
  have trans := v_transitive_l I rank
  obtain ⟨r₁,assign,fr₁⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n hn)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f₁,fill,ff₁⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value i j x (hj : Rd_entry_d i j J) (hx : Tn_value_d n r δ j x) : Rd_entry_d i x f₁ :=
    (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) b hb i (column.input_mem_of_pairMember hj),
      Or.inl ⟨column.input_mem_of_pairMember hj,(assign.2 i x).mpr ⟨j,hj,hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x r) : Rd_entry_d i x f₁ :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have constants i : Rd_entry_d (σ i) (a i) f₁ := value (σ i) (v i) (a i) (params i) (Or.inr (Or.inr (hv i)))
  obtain ⟨E,hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hf₁ := (hE f₁).mpr ff₁
  let nx : Nonempty {x // M.mem x X} := ⟨⟨S,(type.tuple.bound_l rS).2⟩⟩
  let ρ : Env (rt_model_l X nx) 5 := ⟨fun i =>
    [⟨ω,type.constants ω hωU⟩,⟨A,type.constants A hAU⟩,⟨k,type.constants k hk⟩,
      ⟨S,(type.tuple.bound_l rS).2⟩,⟨p,(type.tuple.bound_l rp).2⟩].get i,fun _ => ⟨S,(type.tuple.bound_l rS).2⟩⟩
  let η : Env (smdl_structure_l I (R := R) model.1.2.1) 5 := ⟨ρ.bound,ρ.free⟩
  have points : ∀ i, Rd_entry_d (slots i) (η.bound i).val f₁ := Fin.cases (constants 0)
    (Fin.cases (constants 1) (Fin.cases (constants 2)
      (Fin.cases (vars e S rS) (Fin.cases (vars j p rp) (fun i => Fin.elim0 i)))))
  have read := (satisfies_decode_l I hZF.1 model.1 form hE).trans
    ((compile X R model.1.2.1 E hE f₁ hf₁ η points).trans ((source_core_sat_l φ η).trans
      ((smem_formula_l I model nx φ ρ).symm.trans (td_pending_source_l hZF rank nx ρ _ _ _ _ _))))
  exact (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb column.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans read)))

/-- 同一实际树、元组和已选 z 直接生成含完整待回应查询的真实类型。 -/
theorem tt_demand_pending_realize_l
    {ω e n j U k ν X c R r δ S p z U₁ U₂ A P Y F : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (he : M.mem e n) (hj : M.mem j n)
    (rank : V_d I ν X) (model : Smem_d I c X R) (tuple : Fn0_d n X r)
    (point : M.mem δ X) (constants : M.MemberSubset U X)
    (hωU : M.mem ω U) (hAU : M.mem A U) (hk : M.mem k U)
    (rS : Rd_entry_d e S r) (rp : Rd_entry_d j p r)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P U₁ U₂) (triple : M.IsCartesianProduct I Y A P)
    (alphabet : Td_alphabet_d S U₁ U₂) (chosen : M.mem z U₁) (pending : KPair_d M p k z) :
    ∃ D T q, Tt_realized_d I ω c X R n r δ U D T ∧
      Td_pending_query_d I ω A e n j U D k q ∧ M.mem q T := by
  obtain ⟨D,T,pool,truth,_⟩ := tt_type_exists_l I hZF hω c n r δ U
  have actual : Tt_realized_d I ω c X R n r δ U D T := ⟨model.1,hn,tuple,point,constants,pool,truth⟩
  obtain ⟨q,query⟩ := tt_demand_pending_query_l hZF hω hn he hj pool hωU hAU hk
  have full : Td_pending_d I ω A k S p :=
    ⟨td_tree_of_l I space tree pair triple,z,pending,(alphabet.1 z).mp chosen⟩
  exact ⟨D,T,q,actual,query,(query.2 ν X c R r δ T S p rank model actual rS rp).mpr full⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 固定待回应查询的一阶证书

证书量化同一完整类型的全部秩实现，并保留原第一字母表与指定长度。
因此固定表中的查询码不依赖以后选择的树、待回应字母或实现模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def td_pending_query0_m : Formula 1 9 :=
  let ω := Term.bound 0; let A := Term.bound 1; let e := Term.bound 2
  let n := Term.bound 3; let j := Term.bound 4; let U := Term.bound 5
  let D := Term.bound 6; let k := Term.bound 7; let q := Term.bound 8
  set[9] ⟪
  ⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧ (∀ ν X c R r δ T S p,
    ⌜(v_m kpair_convention_l)⌝ₚ(ν, X) →
    ⌜(smem_m (𝒞 := kpair_convention_l))⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) →
    ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) → ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ, p, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜td_pending_m⌝ₚ(⌜ω⌝ₛ, ⌜A⌝ₛ, ⌜k⌝ₛ, S, p)))⟫
theorem td_pending_query0_closed_l : td_pending_query0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_pending_query0_m,Definitional.Formula.FreeClosed]

def td_pending_query_m {d} (ω A e n j U D k q : Term d) : Formula 1 d :=
  td_pending_query0_m.bind (fun i => [ω,A,e,n,j,U,D,k,q].get i)

@[simp] theorem td_pending_query_m_freeClosed {d} (ω A e n j U D k q : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (he : e.freeSupport = [])
    (hn : n.freeSupport = []) (hj : j.freeSupport = []) (hU : U.freeSupport = [])
    (hD : D.freeSupport = []) (hk : k.freeSupport = []) (hq : q.freeSupport = []) :
    (td_pending_query_m ω A e n j U D k q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_pending_query0_closed_l
  exact Fin.cases hω (Fin.cases hA (Fin.cases he (Fin.cases hn (Fin.cases hj
    (Fin.cases hU (Fin.cases hD (Fin.cases hk (Fin.cases hq (fun i => Fin.elim0 i)))))))))

theorem td_pending_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω A e n j U D k q : Term d) :
    Formula.satisfies ρ (td_pending_query_m ω A e n j U D k q) ↔
      Td_pending_query_d I (ω.eval ρ) (A.eval ρ) (e.eval ρ) (n.eval ρ)
        (j.eval ρ) (U.eval ρ) (D.eval ρ) (k.eval ρ) (q.eval ρ) := by
  simp only [td_pending_query_m,Formula.satisfies_bind,td_pending_query0_m, Td_pending_query_d, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, v_sat_l I hKP.1, smem_sat_l I,
    tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, td_pending_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 同一待回应查询在扩大常量池中的读取

只把实际完整类型限制到原查询池，秩模型、元组、树及待回应点均保持不变。
查询码及固定的 ω、A、k 不变，不重新编译查询。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
include hKP

theorem Td_pending_query_d.scope_l {ω A e n j U D k q V W : M.Domain}
    (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω n V W)
    (sub : M.MemberSubset U V) (query : Td_pending_query_d I ω A e n j U D k q) :
    Td_pending_query_d I ω A e n j V W k q := by
  refine ⟨small.mono_l I large sub q query.1, fun ν X c R r δ T S p rank model type rS rp => ?_⟩
  obtain ⟨t, restricted, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q query.1).symm.trans (query.2 ν X c R r δ t S p rank model restricted rS rp)

end YesMetaZFC.SetTheory.Internal

/-! ## 7.1 回答的三个原查询与真实下降实现

读取原 subtype 的任意排列见证。只恢复回答实际声称的树和 pending，
不擅自将回答元组的奇偶组认作旧两图；原前缀的逐点搬运方程完整保留。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原 dcp 的实际类型消费原 subtype 查询，产生较低实现及严格高度下降。 -/
theorem td_reply_read_l
    {ω A k e j l n m κ τ U D V W B C v w b a z η Y c R r δ α q₁ q₂ q₃ : M.Domain}
    {σ : Fin 7 → M.Domain}
    (hw : M.IsOmega ω) (prog : Ts_program_d hZF ω n b σ a z)
    (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n r δ U D v) (oldHeight : M.SuccessorOf η α)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hm : M.mem m ω)
    (hB : V_d I κ B) (oldConstants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hC : V_d I τ C) (constants : ∀ x, M.mem x V ↔ M.mem x C ∨ x = τ)
    (pool : Tt_pool_d I ω m V W) (sub : M.MemberSubset w W)
    (subtype : Ts_subtype_d ω n κ τ m U w b σ z v)
    (he : M.mem e m) (hj : M.mem j m) (hl : M.mem l m)
    (pendingQuery : Td_pending_query_d I ω A e m j V W k q₁)
    (boundQuery : Tg_bound_query_d I ω e l m V W q₂)
    (heightQuery : Tg_height_query_d I ω l m V W q₃)
    (qp : M.mem q₁ w) (qb : M.mem q₂ w) (qh : M.mem q₃ w) :
    ∃ ν X d H s S p β π, M.mem ν η ∧ V_d I ν X ∧ Smem_d I d X H ∧
      Tt_realized_d I ω d X H m s δ V W w ∧
      Rd_entry_d e S s ∧ Rd_entry_d j p s ∧ Rd_entry_d l β s ∧
      Td_pending_d I ω A k S p ∧ Tg_bound_d I δ S β ∧ Tg_height_d β ν ∧ M.mem β α ∧
      M.IsSetBijectionFromTo I π m m ∧
      (∀ i t x, Rd_entry_d t i π → M.mem i n → (Rd_entry_d i x r ↔ Rd_entry_d t x s)) := by
  obtain ⟨_,ν,hν,witness⟩ := (ts_subtype_realized_l hZF hw prog hY model type
    hκ hτ subtype.1 hm hB oldConstants hC constants pool sub).mp subtype
  obtain ⟨X,d,H,s,f,g,π,hX,lower,actual,ff,_,graph,orig,bij,perm⟩ := witness
  obtain ⟨S,_,root⟩ := actual.tuple.2.1 e he
  obtain ⟨p,_,pending⟩ := actual.tuple.2.1 j hj
  obtain ⟨β,_,last⟩ := actual.tuple.2.1 l hl
  have hp := (pendingQuery.2 ν X d H s δ w S p hX lower actual root pending).mp qp
  have hb := (boundQuery.2 ν X d H s δ w S β hX lower actual root last).mp qb
  have hh := (heightQuery.2 ν X d H s δ w β hX lower actual last).mp qh
  have lt : M.mem β α := by
    obtain ⟨β₁,β₂,h₁,h₂,h₃⟩ := hh
    have oν := v_ordinal_l I hX
    have βν := oν.transitive β₂ h₃.predecessor_mem β
      ((oν.mem h₃.predecessor_mem).transitive β₁ h₂.predecessor_mem β h₁.predecessor_mem)
    exact ((oldHeight ν).mp hν).elim
      (fun h => ((v_ordinal_l I hY).mem oldHeight.predecessor_mem).transitive ν h β βν)
      (fun eq => (eq β).mp βν)
  refine ⟨ν,X,d,H,s,S,p,β,π,hν,hX,lower,actual,root,pending,last,hp,hb,hh,lt,bij,?_⟩
  intro i t x ti hi
  have ht := bij.1.1.input_mem_of_pairMember ti
  constructor
  · intro ix
    have fx := (orig i x hi).mp ix
    exact (graph t x).mp ((perm t ht x (ff.output_mem_of_pairMember fx)).mpr
      ⟨i,bij.1.1.output_mem_of_pairMember ti,ti,fx⟩)
  · intro tx
    obtain ⟨i',_,ti',fx⟩ := (perm t ht x (actual.tuple.bound_l tx).2).mp ((graph t x).mpr tx)
    exact (orig i x hi).mpr (bij.1.1.1.2 t i' i ti' ti ▸ fx)

end YesMetaZFC.SetTheory.Internal
