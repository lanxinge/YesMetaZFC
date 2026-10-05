import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemCollapse
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment
import YesMetaZFC.Model.SetTheory.Internal.SourceEnumeration
import YesMetaZFC.Model.SetTheory.Internal.CollapseCountable
import YesMetaZFC.Model.SetTheory.Internal.RelativeCountable
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingCountable
import YesMetaZFC.Model.SetTheory.Internal.SourceBranchPull
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemRank

/-! # 指定秩层种子的小壳调整

实际构造 Vκ∪{κ,σ} 的源内 κ 枚举，再取壳和传递塌缩。
输出模型属于一致的另一源；嵌入图及其可数性见证属于输出模型自身，
并保持所有值在 Vκ∪{κ} 中的原图条目。内部正则秩段的调整还保留
完整源证书、枝反射、相对层级和小壳闭包，可继续下一步构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_skolem_adjust_l {ω κ K Z W L Y V a c D A R T σ ι : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (target : Ep_source_d hZF ω κ L Y V)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Z) (agree : Ea_agree_d ω κ Z Y)
    (level : Er_level_d Z κ T) (hA : M.mem A Z) (hAt : M.TransitiveSet A) (hm : Smem_d I c A R)
    (hTA : M.MemberSubset T A) (hκA : M.mem κ A) (hσA : M.mem σ A) (hιA : M.mem ι A)
    (hD : M.TransitiveSet D) (hσ : Smap_d I ω a c D A σ) (countable : M.IsSetInjectionFromTo I ι σ ω) :
    ∃ B e S j k η, M.mem B Y ∧ M.mem B Z ∧ M.TransitiveSet B ∧ Smem_d I e B S ∧
      M.mem ω B ∧ Smap_d I ω e c B A j ∧
      M.MemberSubset T B ∧ M.mem κ B ∧ M.MemberSubset D B ∧
      M.mem k B ∧ M.mem η B ∧ Smap_d I ω a e D B k ∧ M.IsSetInjectionFromTo I η k ω ∧
      ∀ x y, Rd_entry_d x y σ → (M.mem y T ∨ y = κ) → Rd_entry_d x y k := by
  have ht := level.hierarchy.transitive_l hZF source.transitive level.member
  have ords := level.hierarchy.ordinal_subset_l hZF source.transitive level.member
  have hκ : M.IsOrdinal κ := by
    obtain ⟨_, _, _, _, cert⟩ := level.hierarchy
    exact (cert T level.member).1
  obtain ⟨Q, f, _, hf, code⟩ := level.code
  obtain ⟨b, hb⟩ := source.code
  obtain ⟨U, g, hU, hg, us, ug⟩ := sc_insert_enumeration_l hZF source.omega source.transitive hb source.theory
    source.omega_mem source.cardinal_mem source.below level.member hf source.cardinal_mem (code.bijection_l (ZF.modelsKP hZF))
  obtain ⟨C, q, hC, hq, cs, cq⟩ := sc_insert_enumeration_l hZF source.omega source.transitive hb source.theory
    source.omega_mem source.cardinal_mem source.below hU hg (source.transitive A hA σ hσA) ug
  have hUt : M.TransitiveSet U := by
    intro x hx y hy
    exact (us y).mpr (Or.inl (((us x).mp hx).elim (fun hx => ht x hx y hy) (fun eq => ords y (eq ▸ hy))))
  have hωU : M.mem ω U := by
    rcases (source.omega.isOrdinal hZF).trichotomy hZF.1 hκ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
    · exact (us ω).mpr (Or.inr (hZF.1.eq_of_same_members ω κ eq))
    · exact (us ω).mpr (Or.inl (ords ω lt))
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ (source.below κ gt)).elim
  have hCA : M.MemberSubset C A := fun x hx => ((cs x).mp hx).elim
    (fun hx => ((us x).mp hx).elim (hTA x) (fun eq => eq ▸ hκA)) (fun eq => eq ▸ hσA)
  obtain ⟨H, B, F, j, e, S, g, _, hB, _, hg, seed, _, hBt, _, bij, _, model, emb, gb⟩ :=
    ep_skolem_collapse_l hZF source small hA hC hq hm hAt hκ hCA cq
  have hBY := agree.transitive_l hZF source target hBt hg gb
  obtain ⟨k, _, hk⟩ := bij.2 σ (seed σ ((cs σ).mpr (Or.inr rfl)))
  obtain ⟨hkB, hDB, hUB, elem, ⟨η, hη, hi⟩, fixed⟩ := emb.countable_factor_l hZF source.omega hBt hAt model hm
    hD hσ hk hιA countable hUt hωU (fun x hx =>
      (bij.2 x (seed x ((cs x).mpr (Or.inl hx)))).imp fun _ h => h.2)
  exact ⟨B, e, S, j, k, η, hBY, hB, hBt, model, hUB ω hωU, emb, fun x hx => hUB x ((us x).mpr (Or.inl hx)),
    hUB κ ((us κ).mpr (Or.inr rfl)), hDB, hkB, hη, elem, hi, fun x y hxy hy => fixed x y hxy ((us y).mpr hy)⟩

/-- 尝试树回收、严格秩界和小壳调整的直接入口；不预设新嵌入属于秩初段。 -/
theorem ep_skolem_rank_step_l {ω κ K Z W L Y V α a c D Q A R T τ ι σ : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (target : Ep_source_d hZF ω κ L Y V)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Z) (agree : Ea_agree_d ω κ Z Y)
    (branches : Sc_branch_d ω Z) (hierarchy : Sc_hierarchy_d Z) (level : Er_level_d Z κ T)
    (hA : M.mem A Z) (rank : Vr_d Z α A) (regular : Sc_regular_d Z α)
    (hTA : M.MemberSubset T A) (hκA : M.mem κ A)
    (hD : M.mem D Z) (hDt : M.TransitiveSet D) (hm : Smem_d I a D Q) (hn : Smem_d I c A R)
    (hτ : M.mem τ Z) (hι : M.mem ι Z) (countable : M.IsSetInjectionFromTo I ι D ω)
    (hσ : Smap_d I ω a c D A σ) (prescribed : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y σ) :
    ∃ B e S j k η L, M.mem B Y ∧ M.mem B Z ∧ M.TransitiveSet B ∧ Smem_d I e B S ∧
      M.mem ω B ∧ Smap_d I ω e c B A j ∧ Ep_source_d hZF ω κ L B S ∧
      Sc_branch_d ω B ∧ Sc_hierarchy_d B ∧ Sh_source_d (ZF.modelsKP hZF) ω B ∧
      M.MemberSubset T B ∧ M.mem κ B ∧ M.MemberSubset D B ∧
      M.mem k B ∧ M.mem η B ∧ Smap_d I ω a e D B k ∧ M.IsSetInjectionFromTo I η k ω ∧
      ∀ x y, Rd_entry_d x y τ → (M.mem y T ∨ y = κ) → Rd_entry_d x y k := by
  obtain ⟨b, hb⟩ := source.code
  obtain ⟨B, F, hB, hF, cert⟩ := rank
  have fn := (cert A hA).2.1
  have hα := sc_function_domain_mem_l hZF source.omega source.transitive hb source.theory hF fn
  have hne : ∃ β, M.mem β α := by
    obtain ⟨β, hβ, _⟩ := ((cert κ (source.transitive A hA κ hκA)).2.2.2).mp hκA
    exact ⟨β, hβ⟩
  have rank : Vr_d Z α A := ⟨B, F, hB, hF, cert⟩
  have hAt := rank.transitive_l hZF source.transitive hA
  have hωA := rank.subset_mem_l source.transitive hA hκA source.omega_mem source.below
  have hωα := rank.ordinal_height_l hZF source.transitive hA (source.omega.isOrdinal hZF) hωA
  have bound := regular ω hωα
  have hl := sc_omega_bound_limit_l hZF source.omega source.transitive hb source.theory source.omega_mem hα
    (cert A hA).1 hne bound
  have ba := branches.rank_l hZF source.transitive hA rank hl hωA
  have ha := hierarchy.rank_l hZF source.transitive hA rank hl
  have sa := source.skolem_rank_l hZF small hA rank hl hωA
  have hκ : M.IsOrdinal κ := by
    obtain ⟨_, _, _, _, cert⟩ := level.hierarchy
    exact (cert T level.member).1
  obtain ⟨L, cut⟩ := source.rank_l hZF hA rank hl regular hωA hn hκA hκ source.below
  obtain ⟨j, η, hjZ, hηZ, hj, hη, res⟩ := source.countable_membership_l hZF branches hD hA hτ hι hm hn countable hσ prescribed
  obtain ⟨hjA, hηA⟩ := sc_countable_function_rank_l hZF source.omega source.transitive hb source.theory
    source.omega_mem hα hne hA rank bound (hAt ω hωA) hDt hjZ hηZ (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1) hη
  obtain ⟨C, e, S, q, k, ξ, hCY, hCZ, hCt, model, hωC, back, hTC, hκC, hDC, hk, hξ, elem, hi, fixed⟩ :=
    ep_skolem_adjust_l hZF source target small agree level hA hAt
      hn hTA hκA hjA hηA hDt hj hη
  obtain ⟨L', next⟩ := cut.pull_l hZF hCt hωC model hn back hκC hκ source.below
  exact ⟨C, e, S, q, k, ξ, L', hCY, hCZ, hCt, model, hωC, back, next,
    ba.pull_l hZF source.omega hCt hAt hωC model hn back,
    (sc_hierarchy_iff_l hZF source.omega hCt hAt model hn back).mpr ha,
    (sh_source_iff_l hZF next cut model hn back).mpr sa, hTC, hκC, hDC, hk, hξ, elem, hi,
    fun x y hxy hy => fixed x y (res x y hxy) hy⟩

end YesMetaZFC.SetTheory.LargeCardinal
