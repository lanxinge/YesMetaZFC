import YesMetaZFC.SetTheory.Descriptive.Borel.Relabel
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Descriptive.Topology.Continuous

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
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare l hl m hm with e | e | e
  · have e := hZF.1.eq_of_same_members l m e
    subst l
    exact Or.inr (((ds_restrict_iff_l I ht hb.1).mpr htb).eq hZF.1
      ((ds_restrict_iff_l I hb hb.1).mpr (fun _ => id)))
  · have hln : M.MemberSubset l n := by
      rcases (hs l).mp e with e | e
      · exact ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).transitive l e
      · exact fun i hi => (e i).mp hi
    exact Or.inl (ds_prefix_mono_l I ht ha.1 ((ds_restrict_iff_l I ht hb.1).mpr htb)
      ((ds_restrict_iff_l I ha hb.1).mpr hab) hln)
  · exact ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm).wellOrder.linear.irrefl m (hle m e) (hle m e) |>.elim

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

/-! ## 连续逆像码的唯一原公式构造 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bplab_d (ω A E f F b t : M.Domain) : Prop := M.mem b A ∧ M.mem t A ∧ ∃ a s i,
  M.PairMember I a s F ∧ M.PairMember I t i E ∧ Cov_d I f s t ∧ Fseq_end_d I ω b a i
def bplab_m {d} (ω A E f F b t : Term d) : Formula 1 d := .conj (.mem b A) (.conj (.mem t A)
  (.existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 t.weaken.weaken.weaken .newest E.weaken.weaken.weaken) (.conj
      (cov_m (𝒞 := 𝒞) f.weaken.weaken.weaken (.bound 1) t.weaken.weaken.weaken)
      (fseq_end_m (𝒞 := 𝒞) ω.weaken.weaken.weaken b.weaken.weaken.weaken (.bound 2) .newest))))))))
derive_free_closed bplab_m
theorem bplab_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f F b t : Term d) :
    Formula.satisfies ρ (bplab_m (𝒞 := 𝒞) ω A E f F b t) ↔
      Bplab_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (F.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [bplab_m, Bplab_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, cov_sat_l I,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Bpex_d (ω A E f T F U Q G : M.Domain) : Prop :=
  (∀ a, M.mem a U ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s) ∧ Edge_d I ω U Q ∧
  M.IsSetRelation I G ∧ ∀ a s, M.PairMember I a s G ↔ Bplab_d I ω A E f F a s
def bpex_m {d} (ω A E f T F U Q G : Term d) : Formula 1 d := .conj
  (.forallE (.iff (.mem .newest U.weaken) (.disj (.mem .newest T.weaken) (.existsE
    (bplab_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken E.weaken.weaken f.weaken.weaken F.weaken.weaken (.bound 1) .newest)))))
  (.conj (edge_m (𝒞 := 𝒞) ω U Q) (.conj (Formula.isRelation 𝒞 G)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
      (bplab_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken E.weaken.weaken f.weaken.weaken F.weaken.weaken (.bound 1) .newest))))))
derive_free_closed bpex_m
theorem bpex_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f T F U Q G : Term d) :
    Formula.satisfies ρ (bpex_m (𝒞 := 𝒞) ω A E f T F U Q G) ↔
      Bpex_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (T.eval ρ) (F.eval ρ) (U.eval ρ) (Q.eval ρ) (G.eval ρ) := by
  simp only [bpex_m, Bpex_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, bplab_sat_l I hE, edge_sat_l I hE,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem bpex_exists_l (hZF : M.Models ZF) {ω A E f T F} (hT : M.MemberSubset T A) :
    ∃ U Q G, Bpex_d I ω A E f T F U Q G := by
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push E).push f).push F
  let φ : BinarySchema 5 := { body := bplab_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp a s : φ.denote ρ a s ↔ Bplab_d I ω A E f F a s := bplab_sat_l I hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨G, hG, hg⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have labels a s : M.PairMember I a s G ↔ Bplab_d I ω A E f F a s :=
    ((hg a s).trans (and_congr_right fun _ => and_congr_right fun _ => hp a s)).trans
      ⟨fun h => h.2.2, fun h => ⟨h.1, h.2.1, h⟩⟩
  let η : Env M 2 := (⟨fun _ => T, fun _ => T⟩ : Env M 1).push G
  let ψ : UnarySchema 2 := {
    body := .disj (.mem .newest (.bound 2)) (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))) }
  obtain ⟨U, hU⟩ := ZF.separation_exists_d hZF ψ η A
  have nodes a : M.mem a U ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s := by
    have eqn : ψ.denote η a ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
        Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]
      exact or_congr Iff.rfl (exists_congr fun s => labels a s)
    exact ((hU a).trans (and_congr_right fun _ => eqn)).trans
      ⟨And.right, fun h => ⟨h.elim (hT a) (fun ⟨_, h⟩ => h.1), h⟩⟩
  obtain ⟨Q, hQ⟩ := tree_edges_l I hZF ω U
  exact ⟨U, Q, G, nodes, hQ, hG.1, labels⟩

theorem bpex_blext_l (hE : Extensional M) {ω A E f T F U Q G}
    (he : M.IsSetInjectionFromTo I E A ω) (h : Bpex_d I ω A E f T F U Q G) :
    Blext_d I ω A A T F U Q G := by
  refine ⟨fun a => (h.1 a).trans (or_congr Iff.rfl (exists_congr fun s => (h.2.2.2 a s).symm)),
    h.2.1, ⟨h.2.2.1, ?_⟩, ?_, ?_⟩
  · intro b t u ht hu
    obtain ⟨_, _, a, s, i, _, hit, _, hb⟩ := (h.2.2.2 b t).mp ht
    obtain ⟨_, _, a', s', j, _, hiu, _, hb'⟩ := (h.2.2.2 b u).mp hu
    exact he.2 t u i hit ((fseq_end_unique_l I hE hb' hb).2 ▸ hiu)
  · intro b t ht
    have ht := (h.2.2.2 b t).mp ht
    exact ⟨ht.1, ht.2.1⟩
  · intro b t ht
    obtain ⟨_, _, a, s, i, ha, _, _, hb⟩ := (h.2.2.2 b t).mp ht
    exact ⟨a, s, ha, i, hb⟩

def Bpull_d (ω A E f c d : M.Domain) : Prop := ∃ T R N F U Q G,
  Bpack_d I c T R N F ∧ Bpack_d I d U Q N G ∧ Bpex_d I ω A E f T F U Q G
def bpull_m {d} (ω A E f c e : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3)) (.conj
    (bpack_m (𝒞 := 𝒞) e.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 4) .newest)
    (bpex_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      E.weaken.weaken.weaken.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 6) (.bound 3) (.bound 2) (.bound 1) .newest)))))))))
derive_free_closed bpull_m
theorem bpull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f c e : Term d) :
    Formula.satisfies ρ (bpull_m (𝒞 := 𝒞) ω A E f c e) ↔
      Bpull_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [bpull_m, Bpull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, bpex_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bpull_unique_l (hE : Extensional M) {ω A E f c d e}
    (h : Bpull_d I ω A E f c d) (k : Bpull_d I ω A E f c e) : d = e := by
  obtain ⟨T, R, N, F, U, Q, G, hc, hd, h⟩ := h
  obtain ⟨T', R', N', F', U', Q', G', hc', he, k⟩ := k
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hc hc'
  have e := hE.eq_of_same_members U U' (fun a => (h.1 a).trans (k.1 a).symm)
  subst U'
  have e := tree_edges_unique_l I hE h.2.1 k.2.1
  subst Q'
  have e := h.2.2.1.eq_of_pairMember_iff hE k.2.2.1 (fun a s => (h.2.2.2 a s).trans (k.2.2.2 a s).symm)
  subst G'
  exact bpack_ext_l I hd he

theorem bpull_exists_l (hZF : M.Models ZF) {ω A E f c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hc : Bcode_d I ω A A c) :
    ∃ d, Bpull_d I ω A E f c d ∧ Bcode_d I ω A A d := by
  obtain ⟨T, R, N, F, hp, hc⟩ := hc
  obtain ⟨U, Q, G, h⟩ := bpex_exists_l I hZF (E := E) (f := f) (F := F) hc.tree.1
  obtain ⟨d, hd⟩ := bpack_exists_l I U Q N G
  exact ⟨d, ⟨T, R, N, F, U, Q, G, hp, hd, h⟩,
    U, Q, N, G, hd, blext_valid_l I hZF hω hA hc (bpex_blext_l I hZF.1 he h)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 连续逆像码的整树求值对应 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bpex_agree_l (hZF : M.Models ZF) {ω A B E f T R N F U Q G x y V W}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω)
    (hf : Cont_d I A B f) (hxy : M.PairMember I x y f) (hc : Btree_d I ω A A T R N F)
    (h : Bpex_d I ω A E f T F U Q G) (hv : Bsem_d I T R N F y V) (hw : Bsem_d I U Q N G x W) :
    ∀ a, M.mem a T → (M.mem a V ↔ M.mem a W) := by
  classical
  have ext := bpex_blext_l I hZF.1 he h
  have code := blext_valid_l I hZF hω hA hc ext
  have old a (ha : M.mem a T) : M.mem a U := (ext.nodes a).mpr (Or.inl ha)
  have no_new a (ha : M.mem a T) : ¬ ∃ s, M.PairMember I a s G :=
    fun ⟨s, hs⟩ => blext_new_l I hc ext hs ha
  have leaf b t (ht : M.PairMember I b t G) : M.mem b W ↔ M.MemberSubset t x :=
    bsem_leaf_l I hw code.leaf_fn (code.leaf b t ht).1 (code.leaf b t ht).2.2.1 ht
  let ρ : Env M 2 := (⟨fun _ => V, fun _ => V⟩ : Env M 1).push W
  let φ : UnarySchema 2 := { body := .iff (.mem .newest (.bound 2)) (.mem .newest (.bound 1)) }
  have hp a : φ.denote ρ a ↔ (M.mem a V ↔ M.mem a W) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]; rfl
  have all := wf_rel_ind_l hZF hc.wf φ ρ (fun a ha ih => (hp a).mpr (by
    by_cases hl : ∃ s, M.PairMember I a s F
    · obtain ⟨s, hs⟩ := hl
      have hs' := hc.leaf a s hs
      refine (bsem_leaf_l I hv hc.leaf_fn ha hs'.2.2.1 hs).trans
        ((?_ : M.MemberSubset s y ↔ ∃ b, M.mem b U ∧ Rd_entry_d b a Q ∧ M.mem b W).trans
          (bsem_union_l I hw (old a ha) hs'.2.2.1 (no_new a ha)).symm)
      constructor
      · intro hsy
        obtain ⟨t, ht, htx, cov⟩ := hf.2 x y s hxy hs'.2.1 hsy
        obtain ⟨i, hi, hit⟩ := he.1.2.2 t ht
        obtain ⟨n, hn, haF⟩ := (hA a).mp (hc.tree.1 a ha)
        obtain ⟨m, b, hm, hbF, hb⟩ := ZF.fseq_end_exists_l I hZF hω hn haF hi
        have hbg := (h.2.2.2 b t).mpr ⟨(hA b).mpr ⟨m, hm, hbF⟩, ht, a, s, i, hs, hit, cov, hb⟩
        have hbU := (ext.nodes b).mpr (Or.inr ⟨t, hbg⟩)
        exact ⟨b, hbU, (ext.edges.2 a b).mpr ⟨old a ha, hbU, i, hb⟩, (leaf b t hbg).mpr htx⟩
      · rintro ⟨b, _, hba, hbW⟩
        rcases (blext_child_l I hc ext ha).mp hba with hbR | ⟨hab, t, hbt⟩
        · exact (hs'.2.2.2 b ((hc.edges.2 a b).mp hbR).2.1 hbR).elim
        · obtain ⟨_, _, a', s', i, ha', _, cov, hb⟩ := (h.2.2.2 b t).mp hbt
          have e := step_parent_l I hZF.1 (show Step_d I ω a' b from ⟨i, hb⟩) hab
          subst a'
          have e := hc.leaf_fn.2 a s' s ha' hs
          exact e ▸ cov x y hxy ((leaf b t hbt).mp hbW)
    · have edges b : Rd_entry_d b a Q ↔ Rd_entry_d b a R :=
        (blext_child_l I hc ext ha).trans ⟨fun hr => hr.elim id (fun ⟨hab, s, hs⟩ => by
          obtain ⟨p, t, hp, hpb⟩ := ext.parent b s hs
          exact (hl ⟨t, step_parent_l I hZF.1 hpb hab ▸ hp⟩).elim), Or.inl⟩
      have children : (∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) ↔
          ∃ b, M.mem b U ∧ Rd_entry_d b a Q ∧ M.mem b W := by
        constructor
        · rintro ⟨b, hb, hr, hv⟩
          exact ⟨b, old b hb, (edges b).mpr hr, ((hp b).mp (ih b hb hr)).mp hv⟩
        · rintro ⟨b, _, hr, hw⟩
          have hr := (edges b).mp hr
          have hb := ((hc.edges.2 a b).mp hr).2.1
          exact ⟨b, hb, hr, ((hp b).mp (ih b hb hr)).mpr hw⟩
      have nlit : ¬ Blit_d I F y a := fun ⟨s, hs, _⟩ => hl ⟨s, hs⟩
      have nlit' : ¬ Blit_d I G x a := fun ⟨s, hs, _⟩ => no_new a ha ⟨s, hs⟩
      rw [bsem_node_l I hv ha, bsem_node_l I hw (old a ha)]
      simp only [nlit, nlit', false_or, Buni_d, hl, no_new a ha, not_false_eq_true, and_true, children]))
  exact fun a ha => (hp a).mp (all a ha)

theorem bpull_correct_l (hZF : M.Models ZF) {ω A B E f c d} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω)
    (hf : Cont_d I A B f) (hc : Bcode_d I ω A A c) (h : Bpull_d I ω A E f c d) :
    ∀ x y, M.PairMember I x y f → (Bsat_d I ω A A d x ↔ Bsat_d I ω A A c y) := by
  obtain ⟨T, R, N, F, U, Q, G, hp, hq, h⟩ := h
  obtain ⟨T', R', N', F', hp', hc⟩ := hc
  obtain ⟨eT, eR, eN, eF⟩ := bpack_unique_l I hp' hp
  subst T' R' N' F'
  have hd := blext_valid_l I hZF hω hA hc (bpex_blext_l I hZF.1 he h)
  intro x y hxy
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F y
  obtain ⟨W, hw, _⟩ := bsem_exists_unique_l I hZF hd.wf N G x
  obtain ⟨z, hz, hzT⟩ := hc.root
  exact (bsat_root_l I hZF hq hd hw hz).trans ((bpex_agree_l I hZF hω hA he hf hxy hc h hv hw z hzT).symm.trans
    (bsat_root_l I hZF hp hc hv hz).symm)

theorem borel_pull_l (hZF : M.Models ZF) {ω A B f K L} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω)
    (hf : Cont_d I A B f) (hk : Borel_d I ω A A B K) (hl : Ip_d I B f K L) : Borel_d I ω A A B L := by
  obtain ⟨E, he⟩ := ha
  obtain ⟨c, hc, hK⟩ := hk
  obtain ⟨d, hd, hd'⟩ := bpull_exists_l I hZF hω hA he hc
  refine ⟨d, hd', fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨hxB, y, hxy, hy⟩ := (hl x).mp hx
    exact ⟨hxB, (bpull_correct_l I hZF hω hA he hf hc hd x y hxy).mpr ((hK y).mp hy).2⟩
  · rintro ⟨hx, hx'⟩
    obtain ⟨y, hy, hxy⟩ := hf.1.2.2 x hx
    exact (hl x).mpr ⟨hx, y, hxy, (hK y).mpr ⟨hy, (bpull_correct_l I hZF hω hA he hf hc hd x y hxy).mp hx'⟩⟩

end YesMetaZFC.SetTheory.Descriptive
