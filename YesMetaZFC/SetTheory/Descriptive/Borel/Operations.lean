import YesMetaZFC.SetTheory.Descriptive.Borel.GraftEvaluation

/-! # Borel 码的补与内部可数并

拼接关系有实际原公式且输出唯一，可直接用于替代、函数图构造与相对化。
补通过一棵子树及一个补根构造；可数并接受任意内部自然数部分指标族，允许空族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def bgraft_m {d} (ω z H E T R N F : Term d) : Formula 1 d := .conj
  (.forallE (.iff (.mem .newest T.weaken) (gnode_m (𝒞 := 𝒞) z.weaken H.weaken .newest))) (.conj
  (edge_m (𝒞 := 𝒞) ω T R) (.conj
  (.forallE (.iff (.mem .newest N.weaken) (gneg_m (𝒞 := 𝒞) z.weaken H.weaken E.weaken .newest))) (.conj
  (Formula.isRelation 𝒞 F) (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
    (glab_m (𝒞 := 𝒞) z.weaken.weaken H.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed bgraft_m
theorem bgraft_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z H E T R N F : Term d) :
    Formula.satisfies ρ (bgraft_m (𝒞 := 𝒞) ω z H E T R N F) ↔
      Bgraft_d I (ω.eval ρ) (z.eval ρ) (H.eval ρ) (E.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bgraft_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, gnode_sat_l I hE, edge_sat_l I hE,
    gneg_sat_l I hE, Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I,
    glab_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.nodes, h.edges, h.negs, h.relation, h.labels⟩⟩

def Bjoin_d (ω z H E c : M.Domain) : Prop := ∃ T R N F,
  Bgraft_d I ω z H E T R N F ∧ Bpack_d I c T R N F
def bjoin_m {d} (ω z H E c : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bgraft_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken
    H.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed bjoin_m

theorem bjoin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z H E c : Term d) :
    Formula.satisfies ρ (bjoin_m (𝒞 := 𝒞) ω z H E c) ↔
      Bjoin_d I (ω.eval ρ) (z.eval ρ) (H.eval ρ) (E.eval ρ) (c.eval ρ) := by
  simp only [bjoin_m, Bjoin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bgraft_sat_l I hE, bpack_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem bjoin_unique_l (hE : Extensional M) {ω z H E c d}
    (h : Bjoin_d I ω z H E c) (k : Bjoin_d I ω z H E d) : c = d := by
  obtain ⟨T, R, N, F, h, hp⟩ := h
  obtain ⟨U, Q, L, G, k, kp⟩ := k
  have e := hE.eq_of_same_members T U (fun t => (h.nodes t).trans (k.nodes t).symm)
  subst U
  have e := hE.eq_of_same_members N L (fun t => (h.negs t).trans (k.negs t).symm)
  subst L
  have e := h.relation.eq_of_pairMember_iff hE k.relation (fun t v => (h.labels t v).trans (k.labels t v).symm)
  subst G
  have e := tree_edges_unique_l I hE h.edges k.edges
  subst Q
  exact bpack_ext_l I hp kp

theorem bjoin_exists_l (hZF : M.Models ZF) {ω A S z H E}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H)
    (hE : M.mem z E → ∃ i c, M.PairMember I i c H ∧ ∀ j d, M.PairMember I j d H → j = i) :
    ∃ c, Bjoin_d I ω z H E c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔
        (M.mem z E ∧ ¬ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) ∨
        (¬ M.mem z E ∧ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) := by
  obtain ⟨T, R, N, F, hG⟩ := bgraft_exists_l I hZF hω hA hz hzω hH E
  have hc := bgraft_valid_l I hZF hω hA hz hzω hH hG hE
  obtain ⟨c, hp⟩ := bpack_exists_l I T R N F
  refine ⟨c, ⟨T, R, N, F, hG, hp⟩, ⟨T, R, N, F, hp, hc⟩, fun x => ?_⟩
  obtain ⟨D, hD, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  exact (bsat_root_l I hZF hp hc hD hz).trans (bgraft_value_l I hZF hω hA hz hzω hH hG hD)

/-- 内部部分可数码族的并；码族为空时得到空集码。 -/
theorem bcode_union_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨c, _, hc, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH (E := z) (fun h => (hz z h).elim)
  exact ⟨c, hc, fun x => by simpa only [hz z, false_and, not_false_eq_true, true_and, false_or] using hv x⟩

theorem bcode_empty_l (hZF : M.Models ZF) {ω A S} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) : ∃ c, Bcode_d I ω A S c ∧ ∀ x, ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hf : Bfam_d I ω A S z := ⟨(ds_empty_fun_l I (X := ω) hz).1,
    fun _ _ ⟨p, _, hp⟩ => (hz p hp).elim⟩
  obtain ⟨c, hc, hv⟩ := bcode_union_l I hZF hω hA hf
  exact ⟨c, hc, fun x hx => ((hv x).mp hx).elim fun _ h => h.elim fun _ h =>
    h.1.elim fun p hp => hz p hp.2⟩

/-- 一元补码；集合解释时自动成为所选空间中的相对补。 -/
theorem bcode_compl_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) :
    ∃ d, Bcode_d I ω A S d ∧ ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨J, hJ⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨C, hC⟩ := KP.exists_singleton (ZF.modelsKP hZF) c
  obtain ⟨H, hH, he⟩ := ZF.exists_constantFunction hZF I (source := J) ((hC c).mpr rfl)
  have hH' : Bfam_d I ω A S H := ⟨hH.1, fun i d hd => by
    obtain ⟨hi, ed⟩ := (he i d).mp hd
    exact ⟨(hJ i).mp hi ▸ hzω, ed.symm ▸ hc⟩⟩
  have hsingle : M.mem z J → ∃ i d, M.PairMember I i d H ∧ ∀ j q, M.PairMember I j q H → j = i :=
    fun _ => ⟨z, c, (he z c).mpr ⟨(hJ z).mpr rfl, rfl⟩, fun j q h => (hJ j).mp ((he j q).mp h).1⟩
  obtain ⟨d, _, hd, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH' hsingle
  refine ⟨d, hd, fun x => ?_⟩
  have ex : (∃ i q, M.PairMember I i q H ∧ Bsat_d I ω A S q x) ↔ Bsat_d I ω A S c x :=
    ⟨fun ⟨i, q, hiq, hx⟩ => ((he i q).mp hiq).2 ▸ hx,
      fun hx => ⟨z, c, (he z c).mpr ⟨(hJ z).mpr rfl, rfl⟩, hx⟩⟩
  simpa only [ex, (hJ z).mpr rfl, true_and, not_true, false_and, or_false] using hv x

end YesMetaZFC.SetTheory.Descriptive
