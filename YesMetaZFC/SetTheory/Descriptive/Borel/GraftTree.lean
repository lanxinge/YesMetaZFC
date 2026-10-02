import YesMetaZFC.SetTheory.Descriptive.Borel.Graft

/-! # 拼接树的前缀封闭性与子边

不同首项的子树互不相交。根的子节点恰为各旧根；非根节点的子边与旧树精确对应。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_tree_l (hZF : M.Models ZF) {ω A S z H E T R N F} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) : Tree_d A T := by
  have hzA := (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  constructor
  · intro t ht
    exact ((hG.nodes t).mp ht).elim (fun e => e.symm ▸ hzA)
      (fun ⟨_, _, _, h⟩ => (bshift_type_l I hZF hω hA hz hH h).1)
  · intro t ht u hu hut
    apply (hG.nodes u).mpr
    rcases (hG.nodes t).mp ht with e | ⟨s, Q, G, i, U, V, hc, hs, ht⟩
    · exact Or.inl (hZF.1.eq_of_same_members u z (fun p => iff_of_false (fun hp => hz p (e ▸ hut p hp)) (hz p)))
    · rcases cons_cases_l I hZF hω hA hz hu with e | ⟨j, r, _, hr, hu⟩
      · exact Or.inl e
      · obtain ⟨n, hn, hrf⟩ := (hA r).mp hr
        obtain ⟨e, hrs⟩ := (cons_subset_l I hZF hω hz hn hrf hu ht).mp hut
        subst j
        have hrU := (bsub_valid_l I hH hc).2.tree.2 s hs r hr hrs
        exact Or.inr ⟨r, Q, G, i, U, V, hc, hrU, hu⟩

theorem bsub_root_l (hE : Extensional M) {ω A S z H i T R N F}
    (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H) (hc : Bsub_d I H i T R N F) : M.mem z T := by
  obtain ⟨e, he, het⟩ := (bsub_valid_l I hH hc).2.root
  exact hE.eq_of_same_members e z (fun p => iff_of_false (he p) (hz p)) ▸ het

theorem bgraft_child_l (hZF : M.Models ZF) {ω A S z H E T R N F i U V Q G s t}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hc : Bsub_d I H i U V Q G) (hs : M.mem s U) (ht : Cons_d I z i s t) (v : M.Domain) :
    Rd_entry_d v t R ↔ ∃ r, M.mem r U ∧ Cons_d I z i r v ∧ Rd_entry_d r s V := by
  obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
  obtain ⟨n, hn, hsf⟩ := (hA s).mp (hU.tree.1 s hs)
  have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, i, U, V, hc, hs, ht⟩)
  constructor
  · intro hv
    obtain ⟨_, hvT, htv⟩ := (hG.edges.2 t v).mp hv
    rcases (hG.nodes v).mp hvT with e | ⟨r, Q', G', j, U', V', hc', hr, hv⟩
    · exact (tree_step_not_empty_l I hz (e ▸ htv)).elim
    · obtain ⟨hj, hU'⟩ := bsub_valid_l I hH hc'
      obtain ⟨m, hm, hrf⟩ := (hA r).mp (hU'.tree.1 r hr)
      obtain ⟨e, hsr⟩ := (cons_step_l I hZF hω hz hi hj hn hm hsf hrf ht hv).mp htv
      subst j
      obtain ⟨rfl, rfl, rfl, rfl⟩ := bsub_unique_l I hH.1 hc hc'
      exact ⟨r, hr, hv, (hU.edges.2 s r).mpr ⟨hs, hr, hsr⟩⟩
  · rintro ⟨r, hr, hv, hsr⟩
    obtain ⟨m, hm, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
    have hvT := (hG.nodes v).mpr (Or.inr ⟨r, Q, G, i, U, V, hc, hr, hv⟩)
    exact (hG.edges.2 t v).mpr ⟨htT, hvT, (cons_step_l I hZF hω hz hi hi hn hm hsf hrf ht hv).mpr
      ⟨rfl, ((hU.edges.2 s r).mp hsr).2.2⟩⟩

theorem bgraft_root_child_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) (v : M.Domain) :
    Rd_entry_d v z R ↔ ∃ i U V Q G, Bsub_d I H i U V Q G ∧ Cons_d I z i z v := by
  have hzT := (hG.nodes z).mpr (Or.inl rfl)
  constructor
  · intro hv
    obtain ⟨_, hvT, hv⟩ := (hG.edges.2 z v).mp hv
    rcases (hG.nodes v).mp hvT with e | ⟨s, Q, G, i, U, V, hc, hs, ht⟩
    · exact (tree_step_not_empty_l I hz (e ▸ hv)).elim
    · obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
      have e := (cons_root_l I hZF hω hA hz hzω hi (hU.tree.1 s hs) ht).mp hv
      exact ⟨i, U, V, Q, G, hc, e ▸ ht⟩
  · rintro ⟨i, U, V, Q, G, hc, ht⟩
    obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
    have hzU := bsub_root_l I hZF.1 hz hH hc
    have hvT := (hG.nodes v).mpr (Or.inr ⟨z, Q, G, i, U, V, hc, hzU, ht⟩)
    exact (hG.edges.2 z v).mpr ⟨hzT, hvT,
      (cons_root_l I hZF hω hA hz hzω hi (hU.tree.1 z hzU) ht).mpr rfl⟩

theorem bgraft_negs_l (hZF : M.Models ZF) {ω A S z H E T R N F t s Q G}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (h : Bshift_d I z H t s Q G) : M.mem t N ↔ M.mem s Q := by
  refine (hG.negs t).trans ⟨?_, fun hs => Or.inr ⟨s, Q, G, h, hs⟩⟩
  rintro (⟨e, _⟩ | ⟨s', Q', G', h', hs'⟩)
  · exact ((bshift_type_l I hZF hω hA hz hH h).2 e).elim
  · obtain ⟨rfl, rfl, rfl⟩ := bshift_unique_l I hZF hω hA hz hH h h'
    exact hs'

theorem bgraft_labels_l (hZF : M.Models ZF) {ω A S z H E T R N F t s Q G}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (h : Bshift_d I z H t s Q G) (v : M.Domain) : M.PairMember I t v F ↔ M.PairMember I s v G := by
  refine (hG.labels t v).trans ⟨?_, fun hs => ⟨s, Q, G, h, hs⟩⟩
  rintro ⟨s', Q', G', h', hs'⟩
  obtain ⟨rfl, rfl, rfl⟩ := bshift_unique_l I hZF hω hA hz hH h h'
  exact hs'

theorem bgraft_root_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) :
    (M.mem z N ↔ M.mem z E) ∧ ¬ ∃ v, M.PairMember I z v F := by
  constructor
  · refine (hG.negs z).trans ⟨?_, fun h => Or.inl ⟨rfl, h⟩⟩
    rintro (⟨_, h⟩ | ⟨_, _, _, h, _⟩)
    · exact h
    · exact ((bshift_type_l I hZF hω hA hz hH h).2 rfl).elim
  · rintro ⟨v, hv⟩
    obtain ⟨_, _, _, h, _⟩ := (hG.labels z v).mp hv
    exact (bshift_type_l I hZF hω hA hz hH h).2 rfl

end YesMetaZFC.SetTheory.Descriptive
