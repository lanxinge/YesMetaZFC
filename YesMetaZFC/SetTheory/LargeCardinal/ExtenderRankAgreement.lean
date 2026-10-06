import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankImage
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessorUnique
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteSyntax

/-! # 共同正则秩段上的超幂一致性

两源共有包含 κ 的正则 Vα 时，它们的有限 κ 幂子集相同。因此同一扩展器
可施于两侧，而两个 j(Vα) 都是同一个 Vα 的实际超幂。唯一性给出共同像、
共同高度及完全相同的限制嵌入；共同像以下的有限幂子集一致性随之成立。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_rank_agree_l {ω κ K K' L X R Y S F c c' d d' j j' N T N' T' α V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (source' : Ep_source_d hZF ω κ K' Y S)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F) (hωL : M.MemberSubset ω L)
    (hm : Smem_d I c X R) (hm' : Smem_d I c' Y S) (hn : Smem_d I d N T) (hn' : Smem_d I d' N' T')
    (ultra : It_ultra_d hZF ω κ L F c d j) (ultra' : It_ultra_d hZF ω κ L F c' d' j')
    (hV : M.mem V X) (rank : Vr_d X α V) (regular : Sc_regular_d X α)
    (hV' : M.mem V Y) (rank' : Vr_d Y α V) (regular' : Sc_regular_d Y α)
    (hκV : M.mem κ V) (hκ : M.IsOrdinal κ) :
    ∃ β B r, M.mem β N ∧ M.mem β N' ∧ Rd_entry_d α β j ∧ Rd_entry_d α β j' ∧
      M.mem B N ∧ M.mem B N' ∧ Vr_d N β B ∧ Vr_d N' β B ∧ Sc_regular_d N β ∧ Sc_regular_d N' β ∧
      M.IsRestrictionOf I r j V ∧ M.IsRestrictionOf I r j' V ∧
      ∀ μ, M.mem μ β → Ea_agree_d ω μ N N' := by
  obtain ⟨hα, K₀, b, R₀, β, B, e, S₀, r, cut, code, hβ, hαβ, hB, image, reg, target, edge, res, K₁, next⟩ :=
    it_ultra_rank_l hZFC source family coherent hωL hm hn ultra hV rank regular hκV hκ
  have agree : Ea_agree_d ω κ X Y := fun n D A hn hd sub =>
    ((source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm).trans
      (source'.rank_agree_l hZF hV' rank' hα hκV n D A hn hd sub)
  obtain ⟨_, K₀', b', R₀', β', B', e', S₀', r', _, code', hβ', hαβ', hB', image', reg', target', edge', res', _⟩ :=
    it_ultra_rank_l hZFC source' (family.transfer_l agree) (coherent.transfer_l hZF agree) hωL
      hm' hn' ultra' hV' rank' regular' hκV hκ
  obtain ⟨eb, er⟩ := smem_unique_l I hZF.1 code code'
  subst b' R₀'
  have family₀ := family.transfer_l (fun n D A hn hd sub => (source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm)
  obtain ⟨eB, _, ej⟩ := it_ultra_unique_l hZF cut family₀ code target target' edge edge'
  subst B' r'
  have hN := ultra.transitive_l hZF hn.1
  have hN' := ultra'.transitive_l hZF hn'.1
  have eβ := image.height_unique_l hZF hN hN' hB hB' image'
  subst β'
  refine ⟨β, B, r, hβ, hβ', hαβ, hαβ', hB, hB', image, image', reg, reg', res, res', ?_⟩
  intro μ hμ n D A hn hd sub
  obtain ⟨E, hE, space⟩ := next.finite_space_l hZF (image.ordinal_subset_l hZF hN hB μ hμ) hn
  have eD := hZF.1.eq_of_same_members E D (fun s => (space s).trans
    ⟨fun hf => (hd s).mpr (fn0_of_function_l (ZF.modelsKP hZF) hf),
      fun hs => fn0_function_l (ZF.modelsKP hZF) ((hd s).mp hs)⟩)
  subst E
  exact ⟨fun hA => hN' B hB' A (image.subset_mem_l hN hB hE hA sub),
    fun hA => hN B hB A (image'.subset_mem_l hN' hB' hE hA sub)⟩

end YesMetaZFC.SetTheory.LargeCardinal
