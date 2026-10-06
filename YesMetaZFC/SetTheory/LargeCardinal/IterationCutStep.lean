import YesMetaZFC.SetTheory.LargeCardinal.IterationDescentStep
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankImage
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankLocal
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthRank
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleRank

/-! # 原树的严格秩段自动接入下降复制

前驱临界点的位置由旧缺失子集推出。原边的秩限制提供指定的实际超幂，
原强度与不可达性随截断保留；递归行自身提供复制所需的全部目标性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_cut_step_l
    {ω κ K K₀ K₁ L F X R N S P T c o j α A β B δ D γ a b d Q Q₀ Q₁ Y Z π σ ι η : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N S)
    (next : Ep_source_d hZF ω ω K₁ P T) (mx : Smem_d I c X R)
    (mp : Smem_d I o P T) (agree : Ea_agree_d ω κ X N) (ultra : It_ultra_d hZF ω κ L F c o j)
    (hA : M.mem A X) (ra : Vr_d X α A) (ga : Sc_regular_d X α) (hωA : M.mem ω A)
    (hB : M.mem B N) (rb : Vr_d N β B) (gb : Sc_regular_d N β) (hLB : M.mem L B) (hFB : M.mem F B)
    (hD : M.mem D P) (rd : Vr_d P δ D) (gd : Sc_regular_d P δ) (hLD : M.mem L D)
    (ma : Smem_d I a A Q) (mb : Smem_d I b B Q₀) (md : Smem_d I d D Q₁)
    (image : Rd_entry_d α γ j) (decrease : M.mem δ γ)
    (loc : It_local_d ω N κ L F) (strength : Ex_strength_d hZF ω κ L N F)
    (inaccessible : Sc_inaccessible_d ω N L)
    (left : Pn_row_d hZF ω a A Y π ι) (right : Pn_row_d hZF ω b B Z σ η)
    (inside : M.MemberSubset Z Y)
    (prior : (A = B ∧ Y = Z ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d A Y π B Z σ ρ φ ∧ Es_strength_d A ρ B) :
    ∃ C τ ξ L', M.mem C Z ∧ Pn_row_d hZF ω d D C τ ξ ∧ Es_strength_d B L D ∧
      Pn_agree_d B Z σ D C τ L L' := by
  obtain ⟨ta, R₂, S₂, e, μ, J, ma₀, my, sy, hp, hi, ep, ip⟩ := left
  obtain ⟨bt, R₃, S₃, f, ν, J', mb₀, mz, sz, hs, he, es, is⟩ := right
  obtain ⟨_, rfl⟩ := smdl_unique_l I ma₀.1 ma.1
  obtain ⟨_, rfl⟩ := smdl_unique_l I mb₀.1 mb.1
  have copy := loc
  obtain ⟨_, _, _, _, pre⟩ := copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hκL : M.mem κ L := pre.1.2.2.2.2.1
  have hκB := bt L hLB κ hκL
  have hωB := rb.subset_mem_l owner.transitive hB hκB owner.omega_mem owner.below
  have limit := (owner.rank_height_l hZF hB rb gb hωB).2
  have ko := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive).1
  have hκA : M.mem κ A := by
    rcases prior with ⟨eq, _, _⟩ | ⟨ρ, φ, common, exactness⟩
    · exact eq.symm ▸ hκB
    · obtain ⟨x, hx, sub, missing⟩ := exactness.2
      have bound := ea_critical_bound_l hZF source owner agree ko common.source_limit.1
        ⟨x, source.transitive A hA x hx, sub, fun hxN => missing
          (rb.subset_mem_l owner.transitive hB (es.1.1.input_mem_of_pairMember common.right_end) hxN sub)⟩
      obtain ⟨W, hw, _, rank, _⟩ := common.source_rank
      exact ta W hw κ (rank.ordinal_subset_l hZF ta hw κ bound)
  obtain ⟨KB, sb⟩ := owner.rank_l hZF hB rb limit gb hωB mb hκB ko owner.below
  have localB := loc.rank_l hZF owner hB rb limit hκB hLB hFB
  have inaccessibleB := inaccessible.rank_l hZF owner.transitive owner.theory.algebra.pair hB rb limit hLB
  obtain ⟨κ', hκZ, ek⟩ := es.1.1.2.2 κ hκB
  obtain ⟨L', _, el⟩ := es.1.1.2.2 L hLB
  obtain ⟨F', _, ef⟩ := es.1.1.2.2 F hFB
  have sizes := (es.rank_size_l hZF owner.omega bt sz.source.transitive mb mz el).mpr
    (sz.inaccessible L' (inaccessibleB.map_l hZF owner.omega bt sz.source.transitive mb mz es el)).2
  obtain ⟨W, q, hw, wr, hq, bij⟩ := sizes.level
  obtain ⟨U, hu, _, iso⟩ := ep_transitive_code_l hZF sb (wr.transitive_l hZF bt hw) hq bij
  have level : Er_level_d B L W := ⟨hw, wr, U, q, hu, hq, iso⟩
  have ll := inaccessibleB.limit_l (ZF.modelsKP hZF) bt sb.theory.algebra.pair
  have exactB := strength.rank_l hZF sb owner.transitive hB rb limit hLB hFB ll hκL level
  have powerB := (sc_power_iff_l hZF owner.omega bt sz.source.transitive mb mz es).mpr sz.power
  obtain ⟨V, hv, powers⟩ := powerB KB sb.finite_mem
  have ab := owner.rank_agree_l hZF hB rb limit hκB
  have full : Ea_agree_d ω κ B X := fun n D A hn hd sub =>
    (ab n D A hn hd sub).trans (agree n D A hn hd sub).symm
  have family := (localB.measures_l hZF sb hv powers).transfer_l full
  have coherent := (localB.coherent_l hZF sb).transfer_l hZF full
  have lo := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive).2
  obtain ⟨la, KA, a', R', γ', V', v, S', j', sa, code, _, eαγ, hV, rv, gv, mv, edge, _, _⟩ :=
    it_ultra_rank_l hZFC source family coherent (fun x hx => lo.transitive κ hκL x (source.below x hx))
      mx mp ultra hA ra ga hκA ko
  have eq := (ultra.elementary_l hZF mx.1 mp.1).1.1.1.2 α γ' γ eαγ image
  subst γ'
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 code ma
  have aa := source.rank_agree_l hZF hA ra la hκA
  have cut_agree : Ea_agree_d ω κ A B := fun n D A hn hd sub =>
    (aa n D A hn hd sub).trans ((agree n D A hn hd sub).trans (ab n D A hn hd sub).symm)
  have ek' : Rd_entry_d κ κ' π := by
    rcases prior with ⟨_, _, eq⟩ | ⟨ρ, φ, common, exactness⟩
    · exact eq.symm ▸ ek
    · have bound := ea_critical_bound_l hZF sa sb cut_agree ko common.source_limit.1 exactness.2
      obtain ⟨W, hw, _, rank, _, points⟩ := common.source_rank
      exact (points κ κ' (rank.ordinal_subset_l hZF ta hw κ bound)).mpr ek
  have above := fun x hx => (es.ordinal_le_l hZF owner.omega bt sz.source.transitive mb mz ek ko) x (owner.below x hx)
  have ko' := es.ordinal_l hZF owner.omega bt sz.source.transitive mb mz ek ko
  obtain ⟨KZ, sz'⟩ := sz.source.rebase_l hZF hκZ above
    (sc_ordinal_small_l hZF owner.omega sz.source.transitive mz sz.source.theory hκZ ko')
  have hκY := ep.1.1.output_mem_of_pairMember ek'
  obtain ⟨KY, sy'⟩ := sy.rebase_l hZF hκY above
    (sc_ordinal_small_l hZF owner.omega sy.source.transitive my sy.source.theory hκY ko')
  have hωV : M.mem ω V' := by
    have emb := edge.elementary_l hZF ma.1 mv.1
    exact emb.1.1.output_mem_of_pairMember
      (emb.omega_l I hZF owner.omega ta (edge.transitive_l hZF mv.1) ma mv hωA)
  have lv := (next.rank_height_l hZF hV rv gv hωV).2
  obtain ⟨hdV, rankD⟩ := rv.rank_l hZF next.transitive hV lv
    (rv.ordinal_subset_l hZF next.transitive hV δ decrease) hD rd
  have regularD : Sc_regular_d V' δ := fun μ hm q hq => gd μ hm q (next.transitive V' hV q hq)
  obtain ⟨C, τ, ξ, hc, row, exactness, common⟩ := pn_copy_step_l hZFC sa sy' sb sz' cut_agree inside
    sz.branches sz.power sz.cover sz.inaccessible ma my ep mb mz es ek el ef prior localB exactB inaccessibleB
    hp hi ip hs he is mv edge hdV rankD regularD md hLD
  exact ⟨C, τ, ξ, L', hc, row, exactness, common⟩

end YesMetaZFC.SetTheory.LargeCardinal
