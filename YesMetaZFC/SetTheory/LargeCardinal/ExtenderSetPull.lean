import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSetRestriction
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed

/-! # 拥有的模型码及完整源沿外层初等图回拉

先恢复原结构码的两个坐标，再用实际隶属关系的唯一性恢复同一关系图。
两端载体上的限制给出全内部初等图，原源的全部性质由此自动回拉。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_model_pull_l {ω κ K V R μ K' W S c d π a b B Q : M.Domain}
    (source : Ep_source_d hZF ω κ K V R) (target : Ep_source_d hZF ω μ K' W S)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W π)
    (hab : Rd_entry_d a b π) (mb : Smem_d I b B Q) :
    ∃ A P, Smem_d I a A P ∧ Rd_entry_d A B π ∧ Rd_entry_d P Q π := by
  obtain ⟨A, P, hA, _, pair, hAB, hPQ⟩ := hj.kpair_preimage_l hZF source.omega source.transitive target.transitive mv mw hab mb.1.1
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive mv mw hj
    (Formula.existsMem (Term.newest : Term 1) .truth) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.existsMem _ .truth)
    ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => B, fun _ => B⟩ (fun _ => hAB)
  simp only [Formula.satisfies_existsMem_iff, Formula.satisfies_truth_iff, and_true] at tr
  obtain ⟨a₀, P₀, ma⟩ := smdl_membership_l I hZF (tr.mpr mb.1.2.1)
  have image := ep_set_membership_l hZF source target mv mw hj ma mb hAB
  have eq := hj.1.2 P P₀ Q hPQ image
  subst P₀
  exact ⟨A, P, ⟨⟨pair, ma.1.2⟩, ma.2⟩, hAB, hPQ⟩

theorem ep_set_source_pull_l {ω κ K V R μ K' W S c d π a b B Q J : M.Domain}
    (source : Ep_source_d hZF ω κ K V R) (target : Ep_source_d hZF ω μ K' W S)
    (mv : Smem_d I c V R) (mw : Smem_d I d W S) (hj : Smap_d I ω c d V W π)
    (hab : Rd_entry_d a b π) (mb : Smem_d I b B Q) (child : Ep_source_d hZF ω ω J B Q) :
    ∃ A P H p, Smem_d I a A P ∧ Ep_source_d hZF ω ω H A P ∧ Rd_entry_d A B π ∧
      M.IsRestrictionOf I p π A ∧ Smap_d I ω a b A B p := by
  obtain ⟨A, P, ma, hAB, _⟩ := ep_set_model_pull_l hZF source target mv mw hj hab mb
  have hωπ := hj.omega_l I hZF source.omega source.transitive target.transitive mv mw source.omega_mem
  have hωA := (hj.member_l I hZF source.omega mv mw hωπ hAB).mpr child.omega_mem
  let φ : Formula 1 1 := Formula.forallMem .newest (Formula.subset .newest (.bound 1))
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive mv mw hj φ
    (by simp -implicitDefEqProofs [φ]) (.forallMem _ (.atom ..))
    ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => B, fun _ => B⟩ (fun _ => hAB)
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_subset_iff] at tr
  have ht : M.TransitiveSet A := tr.mpr child.transitive
  obtain ⟨p, restriction, hp⟩ := ep_set_restriction_l hZF source target mv mw hj ma mb hAB
  obtain ⟨H, hs⟩ := child.pull_l hZF ht hωA ma mb hp hωA (source.omega.isOrdinal hZF) (fun _ h => h)
  exact ⟨A, P, H, p, ma, hs, hAB, restriction, hp⟩

end YesMetaZFC.SetTheory.LargeCardinal
