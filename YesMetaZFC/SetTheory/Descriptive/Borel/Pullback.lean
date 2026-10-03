import YesMetaZFC.SetTheory.Descriptive.Borel.PullbackSyntax

/-! # 连续逆像码的整树求值对应 -/
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
