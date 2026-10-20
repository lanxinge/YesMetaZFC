import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSubsets
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderUltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankEnumeration
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment

/-! # 指定跨源超幂与所属模型的共同强度秩段

所属模型自身超幂读取原强度证书。两次施加在支撑上的一致性与源内迹回收
将该覆盖送到指定后继，再由实际小秩层枚举识别整个共同秩段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.strength_agree_l {ω κ K X R K' Y S Kₙ L F N V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (target : Ep_source_d hZF ω L Kₙ N V)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (loc : It_local_d ω Y κ L F) (next : Ep_successor_d hZF ω κ L X R F N V)
    (strength : Ex_strength_d hZF ω κ L Y F) :
    Es_strength_d Y L N ∧ ∃ K₀, Ep_source_d hZF ω L K₀ Y S ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  obtain ⟨_, b, d, N', V', j, K₀, hm, hn, ultra, base, hLN, hLN', common, back⟩ :=
    loc.return_l hZFC source owner agree branches power cover next
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have copy := loc
  obtain ⟨_, _, hLY, _, pre⟩ := copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := ord.2.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := ord.2.transitive ω hωL
  obtain ⟨P, hP, ps⟩ := power K' owner.finite_mem
  have family := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hP ps)
  have hj := ultra.elementary_l hZF hm.1 hn.1
  obtain ⟨Γ, _, hκΓ⟩ := hj.1.1.2.2 κ owner.cardinal_mem
  have bound := ultra.support_l hZF owner family (loc.coherent_l hZF (owner.read_source_l hZF)) (loc.atoms_l hZF (owner.read_source_l hZF))
    (loc.normal_l hZF (owner.read_source_l hZF)) ord.1 ord.2 below hm hn hκΓ
  have value := strength.realize_l hZF owner family hm hn ultra ord.1.transitive hκΓ bound
  obtain ⟨KY, sy⟩ := owner.rebase_l hZF hLY below
    (sc_ordinal_small_l hZF owner.omega owner.transitive hm owner.theory hLY ord.2)
  obtain ⟨KN, sn⟩ := base.rebase_l hZF hLN' below
    (sc_ordinal_small_l hZF base.omega base.transitive hn base.theory hLN' ord.2)
  have same := value.agree_l hZF sy sn ord.2 hωL back
  have strength : Es_strength_d Y L N := by
    refine ⟨fun α hα x hx sub => ?_, ?_⟩
    · have reverse : Ea_subset_d ω L N' N := fun n D A hn hd sub => (common n D A hn hd sub).mpr
      exact reverse.set_l hZF sn target (value.1 α hα x hx sub) (fun y hy => ord.2.transitive α hα y (sub y hy))
    · obtain ⟨x, hx, sub, missing⟩ := value.2
      exact ⟨x, hx, sub, fun hxN => missing (common.subset_l.set_l hZF target sn hxN sub)⟩
  exact ⟨strength, KY, sy, fun μ hμ n D A hn hd sub =>
    (same μ hμ n D A hn hd sub).trans
      ((common.mono_l hZF (ord.2.transitive μ hμ)) n D A hn hd sub).symm⟩

theorem It_local_d.rank_agree_l {ω κ K X R K' Y S Kₙ N V L F : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (target : Ep_source_d hZF ω L Kₙ N V)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (hierarchy : Sc_hierarchy_d N) (np : Sc_power_d N)
    (sizes : Sc_rank_size_d I Y L) (limit : M.IsLimitOrdinal L)
    (loc : It_local_d ω Y κ L F) (next : Ep_successor_d hZF ω κ L X R F N V)
    (strength : Ex_strength_d hZF ω κ L Y F) : ∃ W,
      M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧ Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧
      ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  obtain ⟨es, K₀, ready, same⟩ := loc.strength_agree_l hZFC source owner target agree branches power cover next strength
  have copy := loc
  obtain ⟨_, _, _, _, pre⟩ := copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := limit.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  obtain ⟨W, f, hW, rank, _, _⟩ := sizes.level
  obtain ⟨W', hW', rank'⟩ := hierarchy L target.cardinal_mem limit.1
  have eq := ea_rank_agree_l hZF ready target limit hωL sizes same hW rank hW' rank'
  subst W'
  have sizes' := ea_rank_size_l hZF target np hierarchy owner.transitive limit hW' hW rank' rank sizes
  obtain ⟨B, f, hB, hb, hf, bij⟩ := sizes'.level
  have eq := hb.unique_l hZF target.transitive hB hW' rank'
  subst B
  obtain ⟨Q, hQ, _, iso⟩ := ep_transitive_code_l hZF target (rank'.transitive_l hZF target.transitive hW') hf bij
  exact ⟨W, hW, rank, ⟨hW', rank', Q, f, hQ, hf, iso⟩, sizes', es, same⟩

end YesMetaZFC.SetTheory.LargeCardinal
