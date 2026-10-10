import YesMetaZFC.SetTheory.Descriptive.Borel.Rules
import YesMetaZFC.SetTheory.Descriptive.TreeCons

/-! # 在叶节点增加一层并节点

连续逆像把一个柱集叶替换成若干柱集的并。只增加旧叶的直接子节点，
旧补节点和旧边保持原义；良基性直接从旧树传递，不用选择新的 Borel 码。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem step_sub_l {ω a b} (h : Step_d I ω a b) : M.MemberSubset a b := by
  obtain ⟨_, _, _, h⟩ := h
  intro p hp
  obtain ⟨i, v, hi⟩ := h.prefix_restriction.1 p hp
  obtain ⟨q, hq, hqb⟩ := ((h.prefix_restriction.2 i v).mp ⟨p, hi, hp⟩).2
  exact (I.unique hi hq).symm ▸ hqb

theorem step_parent_l (hE : Extensional M) {ω a b c} (h : Step_d I ω a c) (k : Step_d I ω b c) : a = b := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hj⟩ := k
  exact (fseq_end_unique_l I hE hi hj).1

/-- 一步延拓的真前缀已经是原节点的前缀。 -/
theorem step_prefix_l (hZF : M.Models ZF) {ω A a b t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (ha : M.mem a A) (hb : M.mem b A) (ht : M.mem t A)
    (hab : Step_d I ω a b) (htb : M.MemberSubset t b) : M.MemberSubset t a ∨ t = b := by
  obtain ⟨n, hn, ha⟩ := (hA a).mp ha
  obtain ⟨m, hm, hb⟩ := (hA b).mp hb
  obtain ⟨l, hl, ht⟩ := (hA t).mp ht
  obtain ⟨hs, hab⟩ := (tree_step_iff_l I hZF hω hn hm ha hb).mp hab
  have hle : M.MemberSubset l m := fun i hi => by
    obtain ⟨v, _, hv⟩ := ht.2.2 i hi
    exact hb.input_mem_of_pairMember (hv.elim fun p hp => ⟨p, hp.1, htb p hp.2⟩)
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare l hl m hm with e | e | e
  · have e := hZF.1.eq_of_same_members l m e
    subst l
    exact Or.inr (((ds_restrict_iff_l I ht hb.1).mpr htb).eq hZF.1
      ((ds_restrict_iff_l I hb hb.1).mpr (fun _ => id)))
  · have hln : M.MemberSubset l n := by
      rcases (hs l).mp e with e | e
      · exact ((hω.isOrdinal hZF).mem hn).transitive l e
      · exact fun i hi => (e i).mp hi
    exact Or.inl (ds_prefix_mono_l I ht ha.1 ((ds_restrict_iff_l I ht hb.1).mpr htb)
      ((ds_restrict_iff_l I ha hb.1).mpr hab) hln)
  · exact ((hω.isOrdinal hZF).mem hm).wellOrder.linear.irrefl m (hle m e) (hle m e) |>.elim

/-- 只在原叶后增加带标签的直接子节点。 -/
structure Blext_d (ω A S T F U Q G : M.Domain) : Prop where
  nodes : ∀ a, M.mem a U ↔ M.mem a T ∨ ∃ s, M.PairMember I a s G
  edges : Edge_d I ω U Q
  labels : M.IsSetFunction I G
  bound : ∀ b s, M.PairMember I b s G → M.mem b A ∧ M.mem s S
  parent : ∀ b s, M.PairMember I b s G → ∃ a t, M.PairMember I a t F ∧ Step_d I ω a b

theorem blext_new_l {ω A S T R N F U Q G}
    (hc : Btree_d I ω A S T R N F) (h : Blext_d I ω A S T F U Q G)
    {b s} (hb : M.PairMember I b s G) : ¬ M.mem b T := by
  obtain ⟨a, t, ha, hab⟩ := h.parent b s hb
  exact fun hbT => (hc.leaf a t ha).2.2.2 b hbT ((hc.edges.2 a b).mpr ⟨(hc.leaf a t ha).1, hbT, hab⟩)

theorem blext_child_l {ω A S T R N F U Q G}
    (hc : Btree_d I ω A S T R N F) (h : Blext_d I ω A S T F U Q G) {a b} (ha : M.mem a T) :
    Rd_entry_d b a Q ↔ Rd_entry_d b a R ∨ (Step_d I ω a b ∧ ∃ s, M.PairMember I b s G) := by
  constructor
  · intro hr
    obtain ⟨_, hb, hab⟩ := (h.edges.2 a b).mp hr
    exact ((h.nodes b).mp hb).elim (fun hb => Or.inl ((hc.edges.2 a b).mpr ⟨ha, hb, hab⟩))
      (fun hb => Or.inr ⟨hab, hb⟩)
  · rintro (hr | ⟨hab, s, hs⟩)
    · obtain ⟨_, hb, hab⟩ := (hc.edges.2 a b).mp hr
      exact (h.edges.2 a b).mpr ⟨(h.nodes a).mpr (Or.inl ha), (h.nodes b).mpr (Or.inl hb), hab⟩
    · exact (h.edges.2 a b).mpr ⟨(h.nodes a).mpr (Or.inl ha), (h.nodes b).mpr (Or.inr ⟨s, hs⟩), hab⟩

theorem blext_terminal_l (hE : Extensional M) {ω A S T R N F U Q G}
    (hc : Btree_d I ω A S T R N F) (h : Blext_d I ω A S T F U Q G)
    {a s} (ha : M.PairMember I a s G) : ∀ b, M.mem b U → ¬ Rd_entry_d b a Q := by
  intro b hb hr
  obtain ⟨_, _, hab⟩ := (h.edges.2 a b).mp hr
  rcases (h.nodes b).mp hb with hb | ⟨t, hb⟩
  · exact blext_new_l I hc h ha (hc.tree.2 b hb a (h.bound a s ha).1 (step_sub_l I hab))
  · obtain ⟨p, t, hp, hpb⟩ := h.parent b t hb
    exact blext_new_l I hc h ha (step_parent_l I hE hpb hab ▸ (hc.leaf p t hp).1)

theorem blext_valid_l (hZF : M.Models ZF) {ω A S T R N F U Q G} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A S T R N F)
    (h : Blext_d I ω A S T F U Q G) : Btree_d I ω A S U Q N G := by
  classical
  have old a (ha : M.mem a T) : M.mem a U := (h.nodes a).mpr (Or.inl ha)
  have tree : Tree_d A U := by
    refine ⟨fun a ha => ((h.nodes a).mp ha).elim (hc.tree.1 a)
      (fun ⟨s, hs⟩ => (h.bound a s hs).1), ?_⟩
    intro b hb t ht htb
    rcases (h.nodes b).mp hb with hb | ⟨s, hb⟩
    · exact old t (hc.tree.2 b hb t ht htb)
    · obtain ⟨a, v, ha, hab⟩ := h.parent b s hb
      rcases step_prefix_l I hZF hω hA (hc.tree.1 a (hc.leaf a v ha).1) (h.bound b s hb).1 ht hab htb with hta | e
      · exact old t (hc.tree.2 a (hc.leaf a v ha).1 t ht hta)
      · exact e.symm ▸ (h.nodes b).mpr (Or.inr ⟨s, hb⟩)
  have wf : Wf_rel_d U Q := by
    intro Y hY hn
    by_cases hnw : ∃ a s, M.mem a Y ∧ M.PairMember I a s G
    · obtain ⟨a, s, ha, hs⟩ := hnw
      exact ⟨a, ha, fun b hb => blext_terminal_l I hZF.1 hc h hs b (hY b hb)⟩
    · have sub : M.MemberSubset Y T := fun a ha => ((h.nodes a).mp (hY a ha)).elim id
        (fun ⟨s, hs⟩ => (hnw ⟨a, s, ha, hs⟩).elim)
      obtain ⟨a, ha, hm⟩ := hc.wf Y sub hn
      exact ⟨a, ha, fun b hb hr => hm b hb ((hc.edges.2 a b).mpr
        ⟨sub a ha, sub b hb, ((h.edges.2 a b).mp hr).2.2⟩)⟩
  obtain ⟨z, hz, hzT⟩ := hc.root
  refine ⟨tree, h.edges, wf, ⟨z, hz, old z hzT⟩, fun a ha => old a (hc.neg_sub a ha), h.labels, ?_, ?_⟩
  · intro a s ha
    exact ⟨(h.nodes a).mpr (Or.inr ⟨s, ha⟩), (h.bound a s ha).2,
      fun hn => blext_new_l I hc h ha (hc.neg_sub a hn), blext_terminal_l I hZF.1 hc h ha⟩
  · intro a ha
    have hn : ¬ ∃ s, M.PairMember I a s F := fun ⟨s, hs⟩ => (hc.leaf a s hs).2.2.1 ha
    have edges b : Rd_entry_d b a Q ↔ Rd_entry_d b a R :=
      (blext_child_l I hc h (hc.neg_sub a ha)).trans ⟨fun hr => hr.elim id (fun ⟨hab, s, hs⟩ => by
        obtain ⟨p, t, hp, hpb⟩ := h.parent b s hs
        exact (hn ⟨t, step_parent_l I hZF.1 hpb hab ▸ hp⟩).elim), Or.inl⟩
    obtain ⟨b, hb, hr, hu⟩ := hc.neg a ha
    exact ⟨b, old b hb, (edges b).mpr hr, fun c _ hca => hu c ((hc.edges.2 a c).mp ((edges c).mp hca)).2.1 ((edges c).mp hca)⟩

end YesMetaZFC.SetTheory.Descriptive
