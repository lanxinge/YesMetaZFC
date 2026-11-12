import YesMetaZFC.Model.SetTheory.Internal.Extensionality
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 任意良基外延结构的完整内部坍塌同构 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem wc_smaps_l (hZF : M.Models ZF) {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hw : Wf_rel_d X R) (he : Wc_ext_d X R) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ B F j d S, M.TransitiveSet B ∧ Wc_graph_d X R F ∧ M.IsSetBijectionFromTo I F X B ∧
      Smem_d I d B S ∧ Smap_d I ω c d X B F ∧ M.IsSetBijectionFromTo I j B X ∧
      (∀ x y, Rd_entry_d y x j ↔ Rd_entry_d x y F) ∧ Smap_d I ω d c B X j := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, F, ht, hg, hf, rel⟩ := wc_iso_l hZF hw he
  obtain ⟨x, hx⟩ := hm.2.1
  obtain ⟨y, hy, _⟩ := hf.1.1.2.2 x hx
  obtain ⟨d, S, hd, hs⟩ := smdl_membership_l I hZF ⟨y, hy⟩
  have atom a b x y (ha : Rd_entry_d a x F) (hb : Rd_entry_d b y F) :
      Rd_entry_d a b R ↔ Rd_entry_d x y S := (rel a b x y ha hb).trans
        ⟨fun h => (hs x y).mpr ⟨hf.1.1.output_mem_of_pairMember ha, hf.1.1.output_mem_of_pairMember hb, h⟩,
          fun h => ((hs x y).mp h).2.2⟩
  obtain ⟨j, hj, js⟩ := ZF.exists_inverseBijectionWithPairs hZF I hf
  refine ⟨B, F, j, d, S, ht, hg, hf, ⟨hd, hs⟩, smap_of_iso_l I hZF hω hm hd hf atom, hj,
    fun x y => js y x, smap_of_iso_l I hZF hω hd hm hj ?_⟩
  intro x y a b ha hb
  exact (atom a b x y ((js x a).mp ha) ((js y b).mp hb)).symm

end YesMetaZFC.SetTheory.Internal
