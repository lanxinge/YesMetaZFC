import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLevelTransfer
import YesMetaZFC.Model.SetTheory.Internal.SourceRankSize
import YesMetaZFC.Model.SetTheory.Internal.SourceRankStage
import YesMetaZFC.SetTheory.CumulativeRelativeComparison

/-! # 支撑以下的子集一致性恢复同一实际秩段

每个低秩对象进入一个有严格小枚举的传递层。关系码及其塌缩将该层和
原枚举同时搬到另一源；逆枚举继而搬运其任意子集，原秩历史逐层相同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem er_joint_l {L a b : M.Domain} (ho : M.IsOrdinal L) (ha : M.mem a L) (hb : M.mem b L) :
    ∃ ν, M.mem ν L ∧ M.MemberSubset a ν ∧ M.MemberSubset b ν := by
  rcases ho.wellOrder.linear.compare a ha b hb with eq | lt | gt
  · exact ⟨b, hb, fun x hx => (eq x).mp hx, fun _ h => h⟩
  · exact ⟨b, hb, (ho.mem hb).transitive a lt, fun _ h => h⟩
  · exact ⟨a, ha, fun _ h => h, (ho.mem ha).transitive b gt⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ea_rank_cover_l {ω L K X R K' Y S V : M.Domain}
    (source : Ep_source_d hZF ω L K X R) (target : Ep_source_d hZF ω L K' Y S)
    (limit : M.IsLimitOrdinal L) (hωL : M.mem ω L) (sizes : Sc_rank_size_d I X L)
    (forward : ∀ ν, M.mem ν L → Ea_subset_d ω ν X Y) (hV : M.mem V X) (rank : Vr_d X L V) :
    ∀ x, M.mem x V → ∃ μ W f, M.mem μ L ∧ M.mem W X ∧ M.mem W Y ∧ M.mem f X ∧ M.mem f Y ∧
      M.TransitiveSet W ∧ M.mem x W ∧ M.IsSetBijectionFromTo I f μ W := by
  obtain ⟨c, hc⟩ := source.code
  intro x hx
  obtain ⟨β, W, hβ, hW, hw, hxW⟩ := sc_rank_limit_l hZF source.omega source.transitive hc source.theory hV rank limit hx
  obtain ⟨W₀, μ, f, hW₀, hw₀, hμ, hf, bf⟩ := sizes.lower β hβ
  have eq := hw.unique_l hZF source.transitive hW hW₀ hw₀
  subst W₀
  have ht := hw.transitive_l hZF source.transitive hW
  obtain ⟨T, hT, bound, iso⟩ := ep_transitive_code_l hZF source ht hf bf
  obtain ⟨ν, hν, μν, ων⟩ := er_joint_l limit.1 hμ hωL
  have νL := limit.1.transitive ν hν
  obtain ⟨K₀, sx⟩ := source.rebase_l hZF (source.transitive L source.cardinal_mem ν hν) ων (source.cardinal_small.mono_l νL)
  obtain ⟨K₁, sy⟩ := target.rebase_l hZF (target.transitive L target.cardinal_mem ν hν) ων (target.cardinal_small.mono_l νL)
  obtain ⟨hWY, hfY⟩ := (forward ν hν).collapse_l hZF sx sy (target.transitive L target.cardinal_mem μ hμ)
    (sy.cardinal_small.mono_l μν) hT (fun p hp => by
      obtain ⟨a, ha, b, hb, pair⟩ := bound p hp
      exact ⟨a, μν a ha, b, μν b hb, pair⟩) iso
  exact ⟨μ, W, f, hμ, hW, hWY, hf, hfY, ht, hxW, bf⟩

/-- 只需一个源的实际小秩层枚举，两侧逐层有限幂一致性便识别整个支撑秩段。 -/
theorem ea_rank_agree_l {ω L K X R K' Y S V W : M.Domain}
    (source : Ep_source_d hZF ω L K X R) (target : Ep_source_d hZF ω L K' Y S)
    (limit : M.IsLimitOrdinal L) (hωL : M.mem ω L) (sizes : Sc_rank_size_d I X L)
    (agree : ∀ ν, M.mem ν L → Ea_agree_d ω ν X Y)
    (hV : M.mem V X) (rank : Vr_d X L V) (hW : M.mem W Y) (rank' : Vr_d Y L W) : V = W := by
  have cover := ea_rank_cover_l hZF source target limit hωL sizes (fun ν hν => (agree ν hν).subset_l) hV rank
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  have inside : M.MemberSubset V Y := by
    intro x hx
    obtain ⟨_, B, _, _, _, hB, _, _, _, hxB, _⟩ := cover x hx
    exact target.transitive B hB x hxB
  apply vr_cross_l hZF source.transitive target.transitive hV hW rank rank' inside
  intro A hA t ht sub
  obtain ⟨μ, B, f, hμ, hB, hBY, hf, hfY, trans, hAB, bf⟩ := cover A hA
  obtain ⟨g, bg, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bf
  have gf := fn0_of_function_l (ZF.modelsKP hZF) bg.1.1
  have hg := sc_inverse_mem_l hZF source.omega source.transitive hc source.theory
    (source.transitive L source.cardinal_mem μ hμ) hB hf gf inverse
  have hgY := sc_inverse_mem_l hZF target.omega target.transitive hd target.theory
    (target.transitive L target.cardinal_mem μ hμ) hBY hfY gf inverse
  obtain ⟨ν, hν, μν, ων⟩ := er_joint_l limit.1 hμ hωL
  have νL := limit.1.transitive ν hν
  obtain ⟨K₀, sx⟩ := source.rebase_l hZF (source.transitive L source.cardinal_mem ν hν) ων (source.cardinal_small.mono_l νL)
  obtain ⟨K₁, sy⟩ := target.rebase_l hZF (target.transitive L target.cardinal_mem ν hν) ων (target.cardinal_small.mono_l νL)
  have back : Ea_subset_d ω ν Y X := fun n D A hn hd sub => (agree ν hν n D A hn hd sub).mpr
  exact back.indexed_subset_l hZF sy sx hB hgY hg ⟨bg.1.1.mono_target_l I μν, bg.1.2⟩ ht
    (fun x hx => trans A hAB x (sub x hx))

end YesMetaZFC.SetTheory.LargeCardinal
