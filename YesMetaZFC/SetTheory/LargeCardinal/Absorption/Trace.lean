import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.SetTheory.FunctionCoordinates

/-! # 7.23 专用博弈的有限合法历史

I 在偶数时刻选择 (x,q)，II 在奇数时刻选择小力迫的稠密集。
下一次 I 的条件属于刚指定的稠密集，并加强上一次 I 的条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Ag_hit_d (T h n q : M.Domain) : Prop :=
  ∀ i D, M.SuccessorOf n i → Entry_d M i D h →
    M.mem q D ∧ ∀ k a x p, M.SuccessorOf i k → Entry_d M k a h → KPair_d M a x p → Entry_d M q p T

def ag_hit_m {d} (T h n q : Term d) : Formula 1 d := set[d] ⟪
  ∀ i D, ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ,i) → ⌜entry_m⌝ₚ(i,D,⌜h⌝ₛ) →
    ⌜q⌝ₛ ∈ D ∧ (∀ k a x p, ⌜Formula.isSuccessor⌝ₚ(i,k) →
      ⌜entry_m⌝ₚ(k,a,⌜h⌝ₛ) → ⌜kpair_m⌝ₚ(a,x,p) → ⌜entry_m⌝ₚ(⌜q⌝ₛ,p,⌜T⌝ₛ))⟫
derive_free_closed ag_hit_m

theorem ag_hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T h n q : Term d) :
    Formula.satisfies ρ (ag_hit_m T h n q) ↔ Ag_hit_d (T.eval ρ) (h.eval ρ) (n.eval ρ) (q.eval ρ) := by
  simp only [ag_hit_m,Ag_hit_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isSuccessor_iff,entry_sat_l M hE,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,kpair_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

def Ag_pos_d (I : kpair_convention_l.Interpretation M) (ω X Q T D h : M.Domain) : Prop :=
  ∀ n a, Entry_d M n a h →
    (Gm_even_d I ω n → ∃ x q, M.mem x X ∧ M.mem q Q ∧ KPair_d M a x q ∧ Ag_hit_d T h n q) ∧
    (¬ Gm_even_d I ω n → M.mem a D)

def ag_pos_m {d} (ω X Q T D h : Term d) : Formula 1 d := set[d] ⟪
  ∀ n a, ⌜entry_m⌝ₚ(n,a,⌜h⌝ₛ) →
    ((⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,n) →
      ∃ x q, x ∈ ⌜X⌝ₛ ∧ q ∈ ⌜Q⌝ₛ ∧ ⌜kpair_m⌝ₚ(a,x,q) ∧ ⌜ag_hit_m⌝ₚ(⌜T⌝ₛ,⌜h⌝ₛ,n,q)) ∧
     (¬ ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,n) → a ∈ ⌜D⌝ₛ))⟫
derive_free_closed ag_pos_m

theorem ag_pos_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω X Q T D h : Term d) :
    Formula.satisfies ρ (ag_pos_m ω X Q T D h) ↔
      Ag_pos_d I (ω.eval ρ) (X.eval ρ) (Q.eval ρ) (T.eval ρ) (D.eval ρ) (h.eval ρ) := by
  simp only [ag_pos_m,Ag_pos_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    entry_sat_l M hE,Formula.satisfies_conj_iff,gm_even_sat_l I hE,Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff,kpair_sat_l M hE,ag_hit_sat_l hE,Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken]
  rfl

/-- 所有约束只读取已经出现的坐标，故对任意子图保持。 -/
theorem Ag_pos_d.restrict_l {I : kpair_convention_l.Interpretation M} {ω X Q T D h s : M.Domain}
    (legal : Ag_pos_d I ω X Q T D h) (sub : M.MemberSubset s h) : Ag_pos_d I ω X Q T D s := by
  have edge {i a} (ia : Entry_d M i a s) : Entry_d M i a h := ia.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  intro n a na
  refine ⟨fun even => ?_,(legal n a (edge na)).2⟩
  obtain ⟨x,q,hx,hq,pair,hit⟩ := (legal n a (edge na)).1 even
  exact ⟨x,q,hx,hq,pair,fun i D ni iD => ⟨(hit i D ni (edge iD)).1,
    fun k a x p ik ka ap => (hit i D ni (edge iD)).2 k a x p ik (edge ka) ap⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.23 专用合法树的实际集合构造

稠密集族由小条件域的内部幂集分离；实数字母对和稠密集的并集构成走法域。
合法树由全部内部有限历史分离，空图与前缀封闭性直接来自局部规则。
游戏证书允许指定的稠密子族，以便在扩张中使用旧稠密集族的像；构造定理
另外返回地模型中全部稠密集的精确分离方程。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Ag_game_d (ω X Q T D P A F R : M.Domain) : Prop where
  dense : ∀ E, M.mem E D → Dense_set_d M Q T Q E
  full : M.mem Q D
  pair : M.IsCartesianProduct I P X Q
  alphabet : ∀ a, M.mem a A ↔ M.mem a P ∨ M.mem a D
  space : Fseq_space_d I ω A F
  legal : ∀ s, M.mem s R ↔ M.mem s F ∧ Ag_pos_d I ω X Q T D s

theorem ag_game_l {ω Q T : M.Domain} (hw : M.IsOmega ω) (X : M.Domain) (O : Cond_order_d M Q T Q) :
    ∃ D P A F R, Ag_game_d hZF ω X Q T D P A F R ∧
      ∀ E, M.mem E D ↔ Dense_set_d M Q T Q E := by
  obtain ⟨D,dense⟩ := dense_family_l hZF Q T Q
  obtain ⟨P,pair⟩ := ZF.exists_cartesianProduct hZF I X Q
  obtain ⟨A,alphabet⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) P D
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hw A
  let η : Env M 5 := ⟨fun i => [ω,X,Q,T,D].get i,fun _ => ω⟩
  let ψ : UnarySchema 5 := {
    body := ag_pos_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest }
  obtain ⟨R,read⟩ := ZF.separation_exists_d hZF ψ η F
  have full : M.mem Q D := (dense Q).mpr
    ⟨fun _q hq => ⟨hq,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hq)⟩,
      fun q hq nz => ⟨q,below_refl_l O hq nz,hq⟩⟩
  exact ⟨D,P,A,F,R,⟨fun E => (dense E).mp,full,pair,alphabet,space,fun s =>
    (read s).trans (and_congr_right fun _ => ag_pos_sat_l I hZF.1 ..)⟩,dense⟩

theorem Ag_game_d.tree_l {ω X Q T D P A F R : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) : Tree_d F R :=
  ⟨fun s hs => ((game.legal s).mp hs).1,fun s hs t ht sub =>
    (game.legal t).mpr ⟨ht,((game.legal s).mp hs).2.restrict_l sub⟩⟩

theorem Ag_game_d.root_l {ω X Q T D P A F R e : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) :
    M.mem e R := by
  obtain ⟨o,ho,how⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members o e (fun x => iff_of_false (ho x) (empty x))
  refine (game.legal e).mpr ⟨(game.space e).mpr ⟨e,eq ▸ how,ds_empty_fun_l I empty⟩,?_⟩
  exact fun _ _ ⟨p,_,hp⟩ => (empty p hp).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 专用合法树进入大坍缩扩张

旧有限历史及其坐标全部由成员满嵌入拉回。奇偶、后继、条件序和旧稠密集
逐项保持；扩张中的游戏仍使用旧稠密集族的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN inj full

theorem ag_pos_image_l {ω X Q T D h : M.Domain} (hw : M.IsOmega ω) (rel : M.IsSetRelation I h) :
    Ag_pos_d I ω X Q T D h ↔ Ag_pos_d J (j ω) (j X) (j Q) (j T) (j D) (j h) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have succ {n i} := image_successor_iff_l (ZF.modelsKP hM) hN.1 j inj full (a := n) (b := i)
  have pair {p x q} := image_kpair_iff_l (ZF.modelsKP hM) hN.1 j inj full (p := p) (a := x) (b := q)
  constructor
  · intro legal n a na
    obtain ⟨n₀,a₀,na₀,rfl,rfl⟩ := (image_entries_l j full rel n a).mp na
    refine ⟨fun even => ?_,fun odd => ?_⟩
    · obtain ⟨x,q,hx,hq,xq,hit⟩ := (legal n₀ a₀ na₀).1 ((image_even_l hM hN j inj full hw).mpr even)
      refine ⟨j x,j q,(image_member_l j inj full).mpr hx,(image_member_l j inj full).mpr hq,
        pair.mp xq,?_⟩
      intro i E ni iE
      obtain ⟨i₀,E₀,iE₀,rfl,rfl⟩ := (image_entries_l j full rel i E).mp iE
      have ni := succ.mpr ni
      refine ⟨(image_member_l j inj full).mpr (hit i₀ E₀ ni iE₀).1,?_⟩
      intro k a x' p ik ka ap
      obtain ⟨k₀,a₀,ka₀,rfl,rfl⟩ := (image_entries_l j full rel k a).mp ka
      obtain ⟨x₀,p₀,ap₀,rfl,rfl⟩ := image_kpair_pull_l (ZF.modelsKP hM) hN.1 j inj full ap
      exact (entry q p₀ T).mp ((hit i₀ E₀ ni iE₀).2 k₀ a₀ x₀ p₀ (succ.mpr ik) ka₀ ap₀)
    · exact (image_member_l j inj full).mpr ((legal n₀ a₀ na₀).2
        (fun even => odd ((image_even_l hM hN j inj full hw).mp even)))
  · intro legal n a na
    refine ⟨fun even => ?_,fun odd => ?_⟩
    · obtain ⟨x,q,hx,hq,xq,hit⟩ := (legal (j n) (j a) ((entry n a h).mp na)).1
        ((image_even_l hM hN j inj full hw).mp even)
      obtain ⟨x₀,hx₀,rfl⟩ := (full X x).mp hx
      obtain ⟨q₀,hq₀,rfl⟩ := (full Q q).mp hq
      refine ⟨x₀,q₀,hx₀,hq₀,pair.mpr xq,?_⟩
      intro i E ni iE
      have accepted := hit (j i) (j E) (succ.mp ni) ((entry i E h).mp iE)
      refine ⟨(image_member_l j inj full).mp accepted.1,fun k a x p ik ka ap => ?_⟩
      exact (entry q₀ p T).mpr (accepted.2 (j k) (j a) (j x) (j p) (succ.mp ik) ((entry k a _).mp ka) (pair.mp ap))
    · exact (image_member_l j inj full).mp ((legal (j n) (j a) ((entry n a h).mp na)).2
        (fun even => odd ((image_even_l hM hN j inj full hw).mpr even)))

theorem Ag_game_d.image_l {ω X Q T D P A F R : M.Domain}
    (game : Ag_game_d hM ω X Q T D P A F R) (hw : M.IsOmega ω) (hw' : N.IsOmega (j ω)) :
    Ag_game_d hN (j ω) (j X) (j Q) (j T) (j D) (j P) (j A) (j F) (j R) := by
  refine ⟨?_,(image_member_l j inj full).mpr game.full,image_product_l j inj full game.pair,
    ?_,image_fseq_l hM hN j inj full hw hw' game.space,?_⟩
  · intro E hE
    obtain ⟨D,hD,rfl⟩ := (full _ E).mp hE
    exact image_global_dense_l hM hN.1 j inj full (game.dense D hD)
  · intro a
    constructor
    · intro ha
      obtain ⟨x,hx,eq⟩ := (full A a).mp ha
      exact ((game.alphabet x).mp hx).elim
        (fun h => Or.inl ((full P a).mpr ⟨x,h,eq⟩)) (fun h => Or.inr ((full D a).mpr ⟨x,h,eq⟩))
    · intro ha
      rcases ha with ha | ha
      · obtain ⟨x,hx,eq⟩ := (full P a).mp ha
        exact (full A a).mpr ⟨x,(game.alphabet x).mpr (Or.inl hx),eq⟩
      · obtain ⟨x,hx,eq⟩ := (full D a).mp ha
        exact (full A a).mpr ⟨x,(game.alphabet x).mpr (Or.inr hx),eq⟩
  · intro s
    constructor
    · intro hs
      obtain ⟨h,hh,rfl⟩ := (full R s).mp hs
      obtain ⟨hf,legal⟩ := (game.legal h).mp hh
      obtain ⟨_,_,fn⟩ := (game.space h).mp hf
      exact ⟨(image_member_l j inj full).mpr hf,(ag_pos_image_l hM hN j inj full hw fn.1.1).mp legal⟩
    · rintro ⟨hf,legal⟩
      obtain ⟨h,hf₀,rfl⟩ := (full F s).mp hf
      obtain ⟨_,_,fn⟩ := (game.space h).mp hf₀
      exact (image_member_l j inj full).mpr ((game.legal h).mpr
        ⟨hf₀,(ag_pos_image_l hM hN j inj full hw fn.1.1).mpr legal⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 专用博弈的合法追加与无终端性

旧约束只涉及旧坐标。I 的新条件由上一次条件下的稠密性取得，
II 总可指定整个条件域；因此每个实际内部有限历史都有合法后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Ag_pos_d.append_l {ω X Q T D A n s t a : M.Domain}
    (legal : Ag_pos_d I ω X Q T D s) (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fs : M.IsSetFunctionFromTo I s n A) (end' : Fseq_end_d I ω t s a)
    (move : (Gm_even_d I ω n → ∃ x q, M.mem x X ∧ M.mem q Q ∧ KPair_d M a x q ∧ Ag_hit_d T s n q) ∧
      (¬ Gm_even_d I ω n → M.mem a D)) : Ag_pos_d I ω X Q T D t := by
  obtain ⟨m,n',d⟩ := end'
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  have ord := hw.members_areOrdinals (ZF.modelsKP hZF) n hn
  have earlier {i k} (ik : M.SuccessorOf k i) (hk : M.mem k n ∨ k = n) : M.mem i n :=
    hk.elim (fun hk => ord.transitive k hk i ik.predecessor_mem) (fun eq => eq ▸ ik.predecessor_mem)
  have hit {k q} (hk : M.mem k n ∨ k = n) (h : Ag_hit_d T s k q) : Ag_hit_d T t k q := by
    intro i E ki iE
    have hi := earlier ki hk
    have iE' := (d.prefix_restriction.2 i E).mpr ⟨hi,iE⟩
    refine ⟨(h i E ki iE').1,fun j v x p ij jv vp => ?_⟩
    exact (h i E ki iE').2 j v x p ij
      ((d.prefix_restriction.2 j v).mpr ⟨ord.transitive i hi j ij.predecessor_mem,jv⟩) vp
  intro k v kv
  have km := (d.source.2.2.2 k).mpr ⟨v,kv⟩
  rcases (d.length_successor k).mp km with kn | eq
  · have ks := (d.prefix_restriction.2 k v).mpr ⟨kn,kv⟩
    refine ⟨fun even => ?_,(legal k v ks).2⟩
    obtain ⟨x,q,hx,hq,pair,h⟩ := (legal k v ks).1 even
    exact ⟨x,q,hx,hq,pair,hit (Or.inl kn) h⟩
  · have eq := hZF.1.eq_of_same_members k n eq
    subst k
    have eq := d.source.2.2.1.2 n v a kv d.last_value
    subst v
    refine ⟨fun even => ?_,move.2⟩
    obtain ⟨x,q,hx,hq,pair,h⟩ := move.1 even
    exact ⟨x,q,hx,hq,pair,hit (Or.inr rfl) h⟩

/-- 偶数回合命中前一稠密集；非首轮同时加强前一小条件。 -/
theorem Ag_game_d.first_move_l {ω X Q T D P A F R n s : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (nonempty : ∃ q, M.mem q Q)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) (hs : M.mem s R)
    (even : Gm_even_d I ω n) : ∃ q, M.mem q Q ∧ Ag_hit_d T s n q := by
  classical
  by_cases empty : ∀ i, ¬ M.mem i n
  · obtain ⟨q,hq⟩ := nonempty
    exact ⟨q,hq,fun i _ succ _ => (empty i succ.predecessor_mem).elim⟩
  · obtain ⟨i,hi,ni⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hn
      (Classical.not_forall.mp empty |>.elim fun i h => ⟨i,Classical.not_not.mp h⟩)
    have odd := (gm_even_successor_l I hZF hw hi ni).mp even
    obtain ⟨E,_,iE⟩ := fs.2.2 i ni.predecessor_mem
    have dense := game.dense E ((((game.legal s).mp hs).2 i E iE).2 odd)
    have ine : ∃ k, M.mem k i := by
      apply Classical.byContradiction
      intro no
      exact odd (gm_even_zero_l I hZF hw (fun k hk => no ⟨k,hk⟩))
    obtain ⟨k,hk,ik⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hi ine
    have keven : Gm_even_d I ω k := Classical.byContradiction
      (fun no => odd ((gm_even_successor_l I hZF hw hk ik).mpr no))
    have kn := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i ni.predecessor_mem k ik.predecessor_mem
    obtain ⟨a,_,ka⟩ := fs.2.2 k kn
    obtain ⟨x,p,_,hp,pair,_⟩ := (((game.legal s).mp hs).2 k a ka).1 keven
    obtain ⟨q,hq,qE⟩ := dense.2 p hp (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hp))
    refine ⟨q,hq.1,fun i' E' ni' iE' => ?_⟩
    have eq := ni.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) ni'
    subst i'
    have eq := fs.1.2 i E' E iE' iE
    subst E'
    refine ⟨qE,fun k' a' x' p' ik' ka' pair' => ?_⟩
    have eq := ik.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) k hk) ik'
    subst k'
    have eq := fs.1.2 k a' a ka' ka
    subst a'
    exact (kpair_injective_l M pair' pair).2.symm ▸ hq.2.2

theorem Ag_game_d.pruned_l {ω X Q T D P A F R : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (nonempty : ∃ q, M.mem q Q) (inh : ∃ x, M.mem x X) :
    ∀ s, M.mem s R → ∃ t, M.mem t R ∧ Step_d I ω s t := by
  classical
  intro s hs
  obtain ⟨n,hn,fs⟩ := (game.space s).mp ((game.legal s).mp hs).1
  have move : ∃ a, M.mem a A ∧
      (Gm_even_d I ω n → ∃ x q, M.mem x X ∧ M.mem q Q ∧ KPair_d M a x q ∧ Ag_hit_d T s n q) ∧
      (¬ Gm_even_d I ω n → M.mem a D) := by
    by_cases even : Gm_even_d I ω n
    · obtain ⟨x,hx⟩ := inh
      obtain ⟨q,hq,hit⟩ := game.first_move_l hZF hw nonempty hn fs hs even
      obtain ⟨a,pair⟩ := (I).total x q
      exact ⟨a,(game.alphabet a).mpr (Or.inl ((game.pair a).mpr ⟨x,hx,q,hq,pair⟩)),
        fun _ => ⟨x,q,hx,hq,pair,hit⟩,fun no => (no even).elim⟩
    · have full := game.full
      exact ⟨Q,(game.alphabet Q).mpr (Or.inr full),fun yes => (even yes).elim,fun _ => full⟩
  obtain ⟨a,ha,first,second⟩ := move
  obtain ⟨m,t,hm,ft,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn fs ha
  exact ⟨t,(game.legal t).mpr ⟨(game.space t).mpr ⟨m,hm,ft⟩,
    ((game.legal s).mp hs).2.append_l hZF hw hn fs end' ⟨first,second⟩⟩,a,end'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 按指定稠密集枚举与 I 策略对弈

II 在第 2k+1 项严格选择给定枚举的第 k 项。策略图由唯一的内部奇数分解
构造，实际树上对弈同时保证全部前缀合法；不以宿主自然数替代内部 ω。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem ag_odd_index_l {ω n : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (odd : ¬ Gm_even_d I ω n) :
    ∃ k j, M.mem k ω ∧ M.IsOrdinalAddition I j k k ∧ M.SuccessorOf n j := by
  have ne : ∃ i, M.mem i n := by
    apply Classical.byContradiction
    intro no
    exact odd (gm_even_zero_l I hZF hw (fun i hi => no ⟨i,hi⟩))
  obtain ⟨j,hj,succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hn ne
  have even : Gm_even_d I ω j := Classical.byContradiction
    (fun no => odd ((gm_even_successor_l I hZF hw hj succ).mpr no))
  obtain ⟨k,hk,add⟩ := even
  exact ⟨k,j,hk,add,succ⟩

private theorem ag_odd_unique_l {ω n k j k' j' : M.Domain} (hw : M.IsOmega ω)
    (hk : M.mem k ω) (add : M.IsOrdinalAddition I j k k) (succ : M.SuccessorOf n j)
    (hk' : M.mem k' ω) (add' : M.IsOrdinalAddition I j' k' k') (succ' : M.SuccessorOf n j') : k = k' := by
  have hj := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  have eq := succ.predecessor_eq hZF.1 (hw.members_areOrdinals (ZF.modelsKP hZF) j hj) succ'
  exact dg_twice_inj_l hZF hw hk hk' add (eq.symm ▸ add')

theorem Ag_game_d.enumeration_strategy_l {ω X Q T D P A F R e : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω) (ef : Fn0_d ω D e) :
    ∃ τ, Gt_strategy_d hZF false ω A R τ ∧
      ∀ n h k j d, Fn0_d n A h → M.mem k ω → M.IsOrdinalAddition I j k k →
        M.SuccessorOf n j → Rd_entry_d h d τ → Rd_entry_d k d e := by
  obtain ⟨O,own⟩ := gm_turns_l hZF false ω A R
  let ρ : Env M 3 := ⟨fun i => [ω,A,e].get i,fun _ => ω⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪∃ n k j,
    n ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜(.bound 3 : Term 5)⌝ₛ,⌜(.bound 1 : Term 5)⌝ₛ) ∧
    k ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧ ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(j,k,k) ∧
    ⌜Formula.isSuccessor⌝ₚ(n,j) ∧ ⌜rd_entry0_m⌝ₚ(k,⌜(.newest : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ)⟫ }
  have sat h d : φ.denote ρ h d ↔ ∃ n k j, M.mem n ω ∧ Fn0_d n A h ∧
      M.mem k ω ∧ M.IsOrdinalAddition I j k k ∧ M.SuccessorOf n j ∧ Rd_entry_d k d e := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,fn0_sat_l hZF.1,Formula.satisfies_isOrdinalAddition_iff I hZF.1,
      Formula.satisfies_isSuccessor_iff,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨τ,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := O) (target := A)
    (fun h hh => by
      obtain ⟨_,n,hn,fh,odd⟩ := (own h).mp hh
      obtain ⟨k,j,hk,add,succ⟩ := ag_odd_index_l hZF hw hn odd
      obtain ⟨d,_,kd⟩ := ef.2.1 k hk
      exact ⟨d,(sat h d).mpr ⟨n,k,j,hn,fh,hk,add,succ,kd⟩⟩)
    (by
      intro h _ d d' hd hd'
      obtain ⟨n,k,j,_,fh,hk,add,succ,kd⟩ := (sat h d).mp hd
      obtain ⟨n',k',j',_,fh',hk',add',succ',kd'⟩ := (sat h d').mp hd'
      have eq := fh'.domain_eq_l hZF.1 fh
      subst n'
      have eq := ag_odd_unique_l hZF hw hk add succ hk' add' succ'
      exact (fn0_function_l (ZF.modelsKP hZF) ef).1.2 k d d' kd (eq.symm ▸ kd'))
    (by
      intro h d _ hd
      obtain ⟨_,_,_,_,_,_,_,_,kd⟩ := (sat h d).mp hd
      exact (game.alphabet d).mpr (Or.inr (ef.bound_l kd).2))
  have read h d := (graph h d).trans (and_congr_right fun _ => sat h d)
  refine ⟨τ,⟨⟨O,own,fn0_of_function_l (ZF.modelsKP hZF) fn⟩,?_⟩,?_⟩
  · intro h d hd
    obtain ⟨ho,n,k,j,hn,fh,hk,add,succ,kd⟩ := (read h d).mp hd
    obtain ⟨hr,n',_,fh',odd⟩ := (own h).mp ho
    have eq := fh'.domain_eq_l hZF.1 fh
    subst n'
    obtain ⟨m,t,hm,ft,end'⟩ := ZF.fseq_end_exists_l I hZF hw hn (fn0_function_l (ZF.modelsKP hZF) fh)
      (fn.output_mem_of_pairMember hd)
    exact ⟨t,(game.legal t).mpr ⟨(game.space t).mpr ⟨m,hm,ft⟩,
      ((game.legal h).mp hr).2.append_l hZF hw hn (fn0_function_l (ZF.modelsKP hZF) fh) end'
        ⟨fun even => (odd even).elim,fun _ => (ef.bound_l kd).2⟩⟩,end'⟩
  · intro n h k j d fh hk add succ hd
    obtain ⟨_,n',k',j',_,fh',hk',add',succ',kd⟩ := (read h d).mp hd
    have eq := fh'.domain_eq_l hZF.1 fh
    subst n'
    exact ag_odd_unique_l hZF hw hk' add' succ' hk add succ ▸ kd

theorem Ag_game_d.enumerated_play_l {ω X Q T D P A F R e σ : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω) (ef : Fn0_d ω D e)
    (first : Gt_strategy_d hZF true ω A R σ) :
    ∃ f, Fn0_d ω A f ∧ Branch_d F R f ∧ Gm_follows_d I true ω σ f ∧
      ∀ k j n d, M.mem k ω → M.IsOrdinalAddition I j k k → M.SuccessorOf n j →
        Rd_entry_d n d f → Rd_entry_d k d e := by
  obtain ⟨τ,second,read⟩ := game.enumeration_strategy_l hZF hw ef
  obtain ⟨o,empty,_⟩ := hw.1.1
  obtain ⟨f,ff,branch,left,right⟩ := gt_battle_l hZF hw game.space empty (game.root_l hZF hw empty) first second
  refine ⟨f,ff,branch,left,?_⟩
  intro k j n d hk add succ nd
  have hn := (ff.bound_l nd).1
  have hj := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  have odd : ¬ Gm_even_d I ω n := fun even => ((gm_even_successor_l I hZF hw hj succ).mp even) ⟨k,hk,add⟩
  obtain ⟨h,fh,cut,_⟩ := ds_prefix_l I hZF hw (fn0_function_l (ZF.modelsKP hZF) ff) hn
  exact read n h k j d (fn0_of_function_l (ZF.modelsKP hZF) fh) hk add succ (right n hn odd h cut d nd)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从同一合法对局读取实数与小条件列

第 2k 项是实际有序对 (x_k,q_k)。先收集偶数项，再分解两张坐标图；
每个有限约束由足够长的同一原对局前缀读出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_game_d.branch_rules_l {ω X Q T D P A F R f : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (ff : Fn0_d ω A f) (branch : Branch_d F R f) : Ag_pos_d I ω X Q T D f := by
  intro n a na
  have hn := (ff.bound_l na).1
  obtain ⟨m,succ,hm⟩ := hw.1.2 n hn
  obtain ⟨s,fs,cut,_⟩ := ds_prefix_l I hZF hw (fn0_function_l (ZF.modelsKP hZF) ff) hm
  have sub := (ds_restrict_iff_l I fs (fn0_function_l (ZF.modelsKP hZF) ff).1).mp cut
  have hs := branch s ((game.space s).mpr ⟨m,hm,fs⟩) sub
  have ns := (cut.2 n a).mpr ⟨succ.predecessor_mem,na⟩
  refine ⟨fun even => ?_,(((game.legal s).mp hs).2 n a ns).2⟩
  obtain ⟨x,q,hx,hq,pair,hit⟩ := (((game.legal s).mp hs).2 n a ns).1 even
  refine ⟨x,q,hx,hq,pair,fun i E ni iE => ?_⟩
  have hin := ni.predecessor_mem
  have him := (succ i).mpr (Or.inl hin)
  have iE' := (cut.2 i E).mpr ⟨him,iE⟩
  refine ⟨(hit i E ni iE').1,fun k a x p ik ka ap => ?_⟩
  have hkn := (hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i hin k ik.predecessor_mem
  exact (hit i E ni iE').2 k a x p ik ((cut.2 k a).mpr ⟨(succ k).mpr (Or.inl hkn),ka⟩) ap

theorem Ag_game_d.coordinates_l {ω X Q T D P A F R f : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (ff : Fn0_d ω A f) (branch : Branch_d F R f) :
    ∃ x q, Fn0_d ω X x ∧ Fn0_d ω Q q ∧
      ∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n a f →
        KPair_d M a y p → Rd_entry_d k y x ∧ Rd_entry_d k p q := by
  have rules := game.branch_rules_l hZF hw ff branch
  let ρ : Env M 1 := ⟨fun _ => f,fun _ => f⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ n,
    ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(n,⌜(.bound 1 : Term 3)⌝ₛ,⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(n,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat k a : φ.denote ρ k a ↔ ∃ n, M.IsOrdinalAddition I n k k ∧ Rd_entry_d n a f := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_isOrdinalAddition_iff I hZF.1,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨g,fg,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := P)
    (fun k hk => by
      obtain ⟨n,add,_⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
      have hn := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
      obtain ⟨a,_,na⟩ := ff.2.1 n hn
      exact ⟨a,(sat k a).mpr ⟨n,add,na⟩⟩)
    (by
      intro k hk a b ha hb
      obtain ⟨n,add,na⟩ := (sat k a).mp ha
      obtain ⟨m,add',mb⟩ := (sat k b).mp hb
      obtain ⟨_,_,unique⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
      have eq := (unique n add).trans (unique m add').symm
      exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 n a b na (eq.symm ▸ mb))
    (by
      intro k a hk ha
      obtain ⟨n,add,na⟩ := (sat k a).mp ha
      obtain ⟨x,p,hx,hp,pair,_⟩ := (rules n a na).1 ⟨k,hk,add⟩
      exact (game.pair a).mpr ⟨x,hx,p,hp,pair⟩)
  obtain ⟨x,q,fx,fq,coords⟩ := ZF.function_coords_l I hZF fg
    (fun a ha => ((game.pair a).mp ha).elim fun x h => h.2.elim fun p hp => ⟨x,p,h.1,hp.1,hp.2⟩)
  exact ⟨x,q,fn0_of_function_l (ZF.modelsKP hZF) fx,fn0_of_function_l (ZF.modelsKP hZF) fq,
    fun k n a y p hk add na pair => coords k a y p ((graph k a).mpr ⟨hk,(sat k a).mpr ⟨n,add,na⟩⟩) pair⟩

/-- 任一指定轮的两个坐标来自该轮实际偶数落子。 -/
theorem Ag_game_d.coordinate_read_l {ω X Q T D P A F R f x q : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (ff : Fn0_d ω A f) (branch : Branch_d F R f) (fx : Fn0_d ω X x) (fq : Fn0_d ω Q q)
    (coords : ∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n a f →
      KPair_d M a y p → Rd_entry_d k y x ∧ Rd_entry_d k p q)
    {k y p} (ky : Rd_entry_d k y x) (kp : Rd_entry_d k p q) :
    ∃ n a, M.IsOrdinalAddition I n k k ∧ Rd_entry_d n a f ∧ KPair_d M a y p := by
  have hk := (fx.bound_l ky).1
  obtain ⟨n,add,_⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
  obtain ⟨a,_,na⟩ := ff.2.1 n (ZF.ordinalAddition_mem_omega hZF I hw hk hk add)
  obtain ⟨y',p',_,_,pair,_⟩ := ((game.branch_rules_l hZF hw ff branch) n a na).1 ⟨k,hk,add⟩
  have points := coords k n a y' p' hk add na pair
  have ey := (fn0_function_l (ZF.modelsKP hZF) fx).1.2 k y' y points.1 ky
  have ep := (fn0_function_l (ZF.modelsKP hZF) fq).1.2 k p' p points.2 kp
  exact ⟨n,a,add,na,ey ▸ ep ▸ pair⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 小条件列递降并命中指定枚举

第 k 轮、第 k+1 轮的小条件，连同中间唯一的 II 落子，均从同一原对局读取。
原合法规则直接给出加强和命中；这里不增添独立的链或泛型假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X Q T D P A F R f x q : M.Domain}

theorem Ag_game_d.round_l (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (ff : Fn0_d ω A f) (branch : Branch_d F R f) (fx : Fn0_d ω X x) (fq : Fn0_d ω Q q)
    (coords : ∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n a f →
      KPair_d M a y p → Rd_entry_d k y x ∧ Rd_entry_d k p q)
    {k l p r} (succ : M.SuccessorOf l k) (kp : Rd_entry_d k p q) (lr : Rd_entry_d l r q) :
    ∃ n m E, M.IsOrdinalAddition I n k k ∧ M.SuccessorOf m n ∧ Rd_entry_d m E f ∧
      M.mem r E ∧ Entry_d M r p T := by
  have hk := (fq.bound_l kp).1
  have hl := (fq.bound_l lr).1
  obtain ⟨y,_,ky⟩ := fx.2.1 k hk
  obtain ⟨n,a,add,na,pair⟩ := game.coordinate_read_l hZF hw ff branch fx fq coords ky kp
  have hn := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  obtain ⟨m,sn,hm⟩ := hw.1.2 n hn
  obtain ⟨n',sm,hn'⟩ := hw.1.2 m hm
  have add' := dg_twice_next_l hZF hw hk succ sn sm add
  obtain ⟨a',_,na'⟩ := ff.2.1 n' hn'
  obtain ⟨y',r',_,_,pair',hit⟩ := ((game.branch_rules_l hZF hw ff branch) n' a' na').1 ⟨l,hl,add'⟩
  have rp := (coords l n' a' y' r' hl add' na' pair').2
  have eq := (fn0_function_l (ZF.modelsKP hZF) fq).1.2 l r' r rp lr
  subst r'
  obtain ⟨E,_,mE⟩ := ff.2.1 m hm
  have result := hit m E sm mE
  exact ⟨n,m,E,add,sn,mE,result.1,result.2 n a y p sn na pair⟩

theorem Ag_game_d.chain_meets_l {e : M.Domain}
    (game : Ag_game_d hZF ω X Q T D P A F R) (hw : M.IsOmega ω)
    (ff : Fn0_d ω A f) (branch : Branch_d F R f) (fx : Fn0_d ω X x) (fq : Fn0_d ω Q q)
    (coords : ∀ k n a y p, M.mem k ω → M.IsOrdinalAddition I n k k → Rd_entry_d n a f →
      KPair_d M a y p → Rd_entry_d k y x ∧ Rd_entry_d k p q)
    (ef : Fn0_d ω D e) (onto : M.IsSetSurjectiveOnto I e ω D)
    (schedule : ∀ k n m E, M.mem k ω → M.IsOrdinalAddition I n k k → M.SuccessorOf m n →
      Rd_entry_d m E f → Rd_entry_d k E e) :
    (∀ k l p r, M.SuccessorOf l k → Rd_entry_d k p q → Rd_entry_d l r q → Entry_d M r p T) ∧
      ∀ E, M.mem E D → ∃ k p, Rd_entry_d k p q ∧ M.mem p E := by
  refine ⟨fun k l p r succ kp lr => (game.round_l hZF hw ff branch fx fq coords succ kp lr).elim
    fun n h => h.elim fun m h => h.elim fun E h => h.2.2.2.2,?_⟩
  intro E hE
  obtain ⟨k,hk,kE⟩ := onto E hE
  obtain ⟨l,succ,hl⟩ := hw.1.2 k hk
  obtain ⟨p,_,kp⟩ := fq.2.1 k hk
  obtain ⟨r,_,lr⟩ := fq.2.1 l hl
  obtain ⟨n,m,E',add,sn,mE',rE',_⟩ := game.round_l hZF hw ff branch fx fq coords succ kp lr
  have eq := (fn0_function_l (ZF.modelsKP hZF) ef).1.2 k E' E (schedule k n m E' hk add sn mE') kE
  exact ⟨l,r,lr,eq ▸ rE'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原对局在同一实数和小泛型中的坐标解释

每个偶数位置的小条件属于对局生成的滤子，实数坐标按同一内部加法读取。
这些性质直接由已构造的坐标图和上闭包推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Descriptive InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Ag_trace_d (ω X A F R f x H : M.Domain) : Prop where
  play : Fn0_d ω A f
  branch : Branch_d F R f
  real : Fn0_d ω X x
  small : ∀ n a y r, Entry_d M n a f → KPair_d M a y r → Gm_even_d I ω n → M.mem r H
  values : ∀ k n a y r, M.mem k ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
    KPair_d M a y r → Entry_d M k y x

theorem ag_trace_l {ω X Q T A F R f x q H : M.Domain}
    (O : Cond_order_d M Q T Q) (ff : Fn0_d ω A f) (branch : Branch_d F R f)
    (fx : Fn0_d ω X x) (fq : Fn0_d ω Q q)
    (coords : ∀ k n a y r, M.mem k ω → M.IsOrdinalAddition I n k k → Entry_d M n a f →
      KPair_d M a y r → Entry_d M k y x ∧ Entry_d M k r q)
    (members : ∀ r, M.mem r H ↔ M.mem r Q ∧ ∃ k t, Entry_d M k t q ∧ Entry_d M t r T) :
    Ag_trace_d hZF ω X A F R f x H := by
  refine ⟨ff,branch,fx,?_,fun k n a y r hk add na pair => (coords k n a y r hk add na pair).1⟩
  rintro n a y r na pair ⟨k,hk,add⟩
  have kr := (coords k n a y r hk add na pair).2
  have hr := (fq.bound_l kr).2
  exact (members r).mpr ⟨hr,k,r,kr,O.refl r hr⟩

end YesMetaZFC.SetTheory.LargeCardinal
