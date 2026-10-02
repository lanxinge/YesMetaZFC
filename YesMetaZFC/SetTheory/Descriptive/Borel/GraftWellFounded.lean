import YesMetaZFC.SetTheory.Descriptive.Borel.GraftTree

/-! # 拼接树的内部良基性与码合法性

在任意非空内部节点集中，若出现非根节点，就在对应旧树的内部截面取极小元。
因此无需把内部良基性升级成外部良基性，也无需选择一个码族的求值。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_wf_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) : Wf_rel_d T R := by
  classical
  intro Y hY hn
  by_cases h : ∃ t, M.mem t Y ∧ t ≠ z
  · obtain ⟨t, htY, htz⟩ := h
    obtain ⟨s, Q, G, i, U, V, hc, hs, ht⟩ := ((hG.nodes t).mp (hY t htY)).resolve_left htz
    let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push Y
    let φ : UnarySchema 3 := {
      body := Formula.existsMem (.bound 1) (cons_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
    obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ U
    have hD a : M.mem a D ↔ M.mem a U ∧ ∃ b, M.mem b Y ∧ Cons_d I z i a b := by
      simp only [φ, Formula.satisfies_existsMem_iff, cons_sat_l I hZF.1] at hD'
      exact hD' a
    obtain ⟨a, ha, hmin⟩ := (bsub_valid_l I hH hc).2.wf D (fun a ha => ((hD a).mp ha).1)
      ⟨s, (hD s).mpr ⟨hs, t, htY, ht⟩⟩
    obtain ⟨haU, b, hbY, hb⟩ := (hD a).mp ha
    refine ⟨b, hbY, fun v hv hr => ?_⟩
    obtain ⟨r, hrU, hrv, hra⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc haU hb v).mp hr
    exact hmin r ((hD r).mpr ⟨hrU, v, hv, hrv⟩) hra
  · obtain ⟨a, ha⟩ := hn
    refine ⟨a, ha, fun b hb hr => ?_⟩
    have eb : b = z := Classical.byContradiction (fun e => h ⟨b, hb, e⟩)
    exact tree_step_not_empty_l I hz (eb ▸ ((hG.edges.2 a b).mp hr).2.2)

/-- 根取补时只需码族非空且指标唯一；并根允许空族和任意内部可数族。 -/
theorem bgraft_valid_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hE : M.mem z E → ∃ i c, M.PairMember I i c H ∧ ∀ j d, M.PairMember I j d H → j = i) :
    Btree_d I ω A S T R N F := by
  have tree := bgraft_tree_l I hZF hω hA hz hzω hH hG
  have root := (hG.nodes z).mpr (Or.inl rfl)
  have funF : M.IsSetFunction I F := by
    refine ⟨hG.relation, fun t v w hv hw => ?_⟩
    obtain ⟨s, Q, G, hs, hv⟩ := (hG.labels t v).mp hv
    have hw := (bgraft_labels_l I hZF hω hA hz hH hG hs w).mp hw
    obtain ⟨i, U, V, hc, _, _⟩ := hs
    exact (bsub_valid_l I hH hc).2.leaf_fn.2 s v w hv hw
  refine ⟨tree, hG.edges, bgraft_wf_l I hZF hω hA hz hH hG, ⟨z, hz, root⟩, ?_, funF, ?_, ?_⟩
  · intro t ht
    exact (hG.nodes t).mpr (((hG.negs t).mp ht).elim (fun h => Or.inl h.1)
      (fun ⟨s, Q, G, h, _⟩ => Or.inr ⟨s, Q, G, h⟩))
  · intro t v hv
    obtain ⟨s, Q, G, hs, hv⟩ := (hG.labels t v).mp hv
    have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, hs⟩)
    have hneg := bgraft_negs_l I hZF hω hA hz hH hG hs
    obtain ⟨i, U, V, hc, hs, ht⟩ := hs
    obtain ⟨_, hvS, hn, he⟩ := (bsub_valid_l I hH hc).2.leaf s v hv
    refine ⟨htT, hvS, fun h => hn (hneg.mp h), fun b _ hb => ?_⟩
    obtain ⟨r, hr, _, hrs⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mp hb
    exact he r hr hrs
  · intro t htN
    rcases (hG.negs t).mp htN with ⟨e, he⟩ | ⟨s, Q, G, hs, hsQ⟩
    · subst t
      obtain ⟨i, c, hic, hi⟩ := hE he
      obtain ⟨hiω, U, V, Q, G, hp, _⟩ := hH.2 i c hic
      have hc : Bsub_d I H i U V Q G := ⟨c, hic, hp⟩
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hiω hzω (ds_empty_fun_l I hz)
      have hbR := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mpr ⟨i, U, V, Q, G, hc, hb⟩
      refine ⟨b, ((hG.edges.2 z b).mp hbR).2.1, hbR, fun v _ hv => ?_⟩
      obtain ⟨j, U', V', Q', G', ⟨d, hj, _⟩, hv⟩ :=
        (bgraft_root_child_l I hZF hω hA hz hzω hH hG v).mp hv
      exact cons_unique_l I hZF.1 (hi j d hj ▸ hv) hb
    · obtain ⟨i, U, V, hc, hsU, ht⟩ := hs
      obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
      obtain ⟨r, hr, hrs, huniq⟩ := hU.neg s hsQ
      obtain ⟨n, hn, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hn hrf
      have hbR := (bgraft_child_l I hZF hω hA hz hH hG hc hsU ht b).mpr ⟨r, hr, hb, hrs⟩
      refine ⟨b, ((hG.edges.2 t b).mp hbR).2.1, hbR, fun v _ hv => ?_⟩
      obtain ⟨r', hr', hv, hr's⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hsU ht v).mp hv
      exact cons_unique_l I hZF.1 (huniq r' hr' hr's ▸ hv) hb

end YesMetaZFC.SetTheory.Descriptive
