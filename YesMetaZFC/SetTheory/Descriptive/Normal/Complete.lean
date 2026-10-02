import YesMetaZFC.SetTheory.Descriptive.Normal.Witness

/-! # 真值产生无违规的闭证书 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem nb_complete_l (hZF : M.Models ZF) {ω A c T R N F E z x} (hω : M.IsOmega ω)
    (hc : Btree_d I ω A A T R N F) (hpack : Bpack_d I c T R N F)
    (he : M.IsSetInjectionFromTo I E T ω) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (h : Bsat_d I ω A A c x) :
    ∃ w, M.IsSetFunctionFromTo I w ω ω ∧ ¬ Nb_d I T R N F E z x w := by
  classical
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have root := (bsat_root_l I hZF hpack hc hv hz).mp h
  obtain ⟨w, hw, val, sel⟩ := nw_real_l I hZF hω he hz hzω hv
  have node {a v} (h : Nv_d I E w a v) := h.elim fun _ h => he.1.input_mem_of_pairMember h.1
  refine ⟨w, hw, fun h => ?_⟩
  rcases h with h | h | h | ⟨a, v, hu, hav, h⟩
  · exact (val z z (node h) h).mp root rfl
  · obtain ⟨a, s, v, hs, hav, hsx | ⟨hne, j, b, d, hjs, hjx, hbd⟩⟩ := h
    · have ha := (bsem_leaf_l I hv hc.leaf_fn (node hav) (hc.leaf a s hs).2.2.1 hs).mpr hsx.2
      exact (val a v (node hav) hav).mp ha hsx.1
    · have ha := (val a v (node hav) hav).mpr hne
      have hsub := (bsem_leaf_l I hv hc.leaf_fn (node hav) (hc.leaf a s hs).2.2.1 hs).mp ha
      exact hbd (hx.1.2 j b d (hjs.elim fun p hp => ⟨p, hp.1, hsub p hp.2⟩) hjx)
  · obtain ⟨a, b, v, u, haN, hba, hav, hbu, wrong⟩ := h
    obtain ⟨d, _, _, uniq⟩ := hc.neg a haN
    have hbT := ((hc.edges.2 a b).mp hba).2.1
    have hneg := bsem_neg_l I hv (node hav) haN
      (fun ⟨s, hs⟩ => (hc.leaf a s hs).2.2.1 haN) hbT hba
      (fun e heT hea => (uniq e heT hea).trans (uniq b hbT hba).symm)
    have eqv : M.mem a V ↔ M.mem b V := (val a v (node hav) hav).trans
      ((not_congr wrong).trans (val b u hbT hbu).symm)
    by_cases haV : M.mem a V
    · exact hneg.mp haV (eqv.mp haV)
    · exact haV (hneg.mpr (fun hbV => haV (eqv.mpr hbV)))
  · rcases h with ⟨e, b, u, hb, hba, hbu, hne⟩ | ⟨hne, hn⟩ | ⟨b, j, hb, hba, hbj, hj, hbz⟩
    · have haV := (bsem_union_l I hv (node hav) hu.1 hu.2).mpr ⟨b, hb, hba, (val b u hb hbu).mpr hne⟩
      exact (val a v (node hav) hav).mp haV e
    · obtain ⟨b, j, hb, hba, _, hbj, hj⟩ := sel a v (node hav) hav ((val a v (node hav) hav).mpr hne) hu
      exact hn ⟨b, j, hb, hba, hbj, hj⟩
    · have hne : v ≠ z := fun e => hz j (e ▸ hj.predecessor_mem)
      obtain ⟨d, k, _, _, hdV, hdk, hk⟩ := sel a v (node hav) hav ((val a v (node hav) hav).mpr hne) hu
      have ejk := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem (he.1.output_mem_of_pairMember hbj)) hj hk
      have edb := he.2 d b j (ejk.symm ▸ hdk) hbj
      exact (val b z hb hbz).mp (edb ▸ hdV) rfl

end YesMetaZFC.SetTheory.Descriptive
