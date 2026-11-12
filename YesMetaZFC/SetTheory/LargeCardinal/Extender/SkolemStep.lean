import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.Extender.EmbeddingCountable
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Internal.Collapse
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.Internal.CollapseCountable
import YesMetaZFC.Model.SetTheory.Reflection.RelativeCountable
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 小壳闭包在严格相对秩段中的保持

代码、参数列、选择图及壳都给出已有集合上的有限秩界。
最小性仍是对秩段中的全部候选壳成立的原最小性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.codes_rank_l {ω κ K Z S α V C : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) (hC : M.mem C Z) (codes : Scode_d I ω C) : M.mem C V := by
  have algebra := (source.algebra_l (ZF.modelsKP hZF)).rank_l hZF source.transitive hV rank hα
  obtain ⟨Q, hQ, qs⟩ := algebra.product ω ω hω hω
  obtain ⟨P, hP, ps⟩ := algebra.product ω Q hω hQ
  obtain ⟨J, hJ, js⟩ := source.rank_sequence_l (ZF.modelsKP hZF) hV rank hα hω hP
  obtain ⟨B, hB, bs⟩ := algebra.product J ω hJ hω
  apply rank.subset_mem_l source.transitive hV hB hC
  intro a ha
  obtain ⟨n, F, r, pair, program, hr⟩ := (codes a).mp ha
  have row {k c i j} (hc : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c P := by
    obtain ⟨p, o, ho, hp, hc⟩ := hc
    exact (ps c).mpr ⟨o, num_mem_l hZF.1 source.omega ho, p, (qs p).mpr ⟨i, hi, j, hj, hp⟩, hc⟩
  have fn : M.IsSetFunctionFromTo I F n P := by
    refine ⟨program.2.1.2.1, program.2.1.2.2, fun t ht => ?_⟩
    obtain ⟨c, hc⟩ := (program.2.1.2.2 t).mp ht
    have tw := source.omega.transitive (ZF.modelsKP hZF) n program.1 t ht
    refine ⟨c, ?_, hc⟩
    rcases program.2.2 t c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact row hs hi hj
    · exact row hs hi hj
    · exact row hs (source.omega.transitive (ZF.modelsKP hZF) t tw i hi) (source.omega.transitive (ZF.modelsKP hZF) t tw j hj)
    · exact row hs hi (source.omega.transitive (ZF.modelsKP hZF) t tw j hj)
  exact (bs a).mpr ⟨F, (js F).mpr ⟨n, program.1, fn⟩, r, source.omega.transitive (ZF.modelsKP hZF) n program.1 r hr, pair⟩

theorem Ep_source_d.skolem_rank_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (small : Sh_source_d (ZF.modelsKP hZF) ω Z)
    (hV : M.mem V Z) (rank : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) :
    Sh_source_d (ZF.modelsKP hZF) ω V := by
  intro c A R U μ f hA hR hU hμ hf hm ho hw sub bij
  have vz := source.transitive V hV
  have vt := rank.transitive_l source.transitive hV
  obtain ⟨u, C, J, T, D, G, N, g, _, hC, hJ, hT, hD, hG, hN, hg, skolem, hull, gb⟩ :=
    small c A R U μ f (vz A hA) (vz R hR) (vz U hU) (vz μ hμ) (vz f hf) hm ho hw sub bij
  have hCV := source.codes_rank_l hZF hV rank hα hω hC skolem.codes
  obtain ⟨J', hJ', seq⟩ := source.rank_sequence_l (ZF.modelsKP hZF) hV rank hα hω hA
  have hJV : M.mem J V := hZF.1.eq_of_same_members J' J (fun s => (seq s).trans (skolem.params s).symm) ▸ hJ'
  have hTV := rank.relation_mem_l source.transitive hV hα hCV hω hT (fun p hp => (skolem.labels p).mp hp)
  have hDV := rank.relation_mem_l source.transitive hV hα hTV hJV hD (fun p hp => (skolem.domain p).mp hp)
  have hGV := rank.relation_mem_l source.transitive hV hα hDV hA hG (fn0_of_function_l (ZF.modelsKP hZF) skolem.graph).1
  have hNV := rank.subset_mem_l source.transitive hV hA hN hull.2.1
  have hgV := rank.relation_mem_l source.transitive hV hα hμ hNV hg (fn0_of_function_l (ZF.modelsKP hZF) gb.1.1).1
  exact ⟨u, C, J, T, D, G, N, g, vt A hA u skolem.point, hCV, hJV, hTV, hDV, hGV, hNV, hgV,
    skolem, ⟨hull.1, hull.2.1, hull.2.2.1, fun B hB => hull.2.2.2 B (vz B hB)⟩, gb⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 小 Skolem 壳的源内塌缩及跨源隶属

从种子的实际枚举出发构造壳、塌缩和塌缩的枚举。有限幂一致性随后自动
搬运关系码并还原传递模型，给出下降装配所需的一步隶属结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_skolem_collapse_l {ω κ K Z W c A R U f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (small : Sh_source_d (ZF.modelsKP hZF) ω Z)
    (hA : M.mem A Z) (hU : M.mem U Z) (hf : M.mem f Z) (hm : Smem_d I c A R)
    (hAt : M.TransitiveSet A) (hκ : M.IsOrdinal κ) (hUA : M.MemberSubset U A)
    (bij : M.IsSetBijectionFromTo I f κ U) :
    ∃ N B F j e S g, M.mem N Z ∧ M.mem B Z ∧ M.mem F Z ∧ M.mem g Z ∧
      M.MemberSubset U N ∧ M.MemberSubset N A ∧ M.TransitiveSet B ∧ Mc_iso_d N B F ∧
      M.IsSetBijectionFromTo I j B N ∧ (∀ x y, Rd_entry_d y x j ↔ Rd_entry_d x y F) ∧
      Smem_d I e B S ∧ Smap_d I ω e c B A j ∧ M.IsSetBijectionFromTo I g κ B := by
  have hR := source.membership_relation_l hZF hA hm
  obtain ⟨u, C, J, T, D, H, N, q, _, _, _, _, _, _, hN, hq, skolem, hull, hqbij⟩ :=
    small c A R U κ f hA hR hU source.cardinal_mem hf hm.1 hκ source.below hUA bij
  obtain ⟨d, Q, sub, elem⟩ := selem_of_skolem_l I hZF source.omega hm.1 skolem.codes hull.2.1
    (skolem.point_mem_l I hZF source.omega hm.1 hull.2.2.1) (skolem.closed_l I hull.2.1 hull.2.2.1)
  obtain ⟨B, F, j, e, S, ht, collapse, hj, inverse, model, embedding⟩ :=
    selem_collapse_l hZF source.omega hAt hm sub elem
  have member := smem_sub_l I hm sub
  have iso : Wc_iso_d N Q B F := ⟨ht, collapse.function, (collapse.bijection_l (ZF.modelsKP hZF)).2,
    fun a _ b _ x _ => collapse.injective a b x, fun a ha b hb x _ y _ hax hby =>
      (member.2 a b).trans ((and_iff_right ha).trans ((and_iff_right hb).trans (collapse.member a b x y hax hby)))⟩
  obtain ⟨z, hz⟩ := source.code
  have qf := fn0_of_function_l (ZF.modelsKP hZF) hqbij.1.1
  have size := sc_small_image_l hZF source.omega source.transitive hz source.theory
    source.cardinal_mem hN hq (source.cardinal_small_l (ZF.modelsKP hZF)) qf hqbij.2
  obtain ⟨B', F', hB', hF', iso'⟩ := source.collapse.collapse_l I (ZF.modelsKP hZF) source.transitive hz hN
    (source.membership_relation_l hZF hN member) size (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have hB := iso'.unique_l hZF iso ▸ hB'
  have hF := iso'.graph_unique_l hZF iso ▸ hF'
  obtain ⟨g, hg, comp⟩ := sc_compose_l hZF source.omega source.transitive hz source.theory
    source.cardinal_mem hN hq hF qf (collapse.function.mono_target_l (source.transitive B hB))
  have comp := comp.retarget_l collapse.function
  have gb : M.IsSetBijectionFromTo I g κ B := by
    refine ⟨⟨fn0_function_l (ZF.modelsKP hZF) comp.1, ?_⟩, ?_⟩
    · intro a b x ha hb
      obtain ⟨v, _, hav⟩ := qf.2.1 a (comp.1.bound_l ha).1
      obtain ⟨w, _, hbw⟩ := qf.2.1 b (comp.1.bound_l hb).1
      exact hqbij.1.2 a b v hav ((collapse.injective v w x
        ((comp.value_l qf collapse.function hav).mp ha) ((comp.value_l qf collapse.function hbw).mp hb)).symm ▸ hbw)
    · intro x hx
      obtain ⟨a, ha⟩ := collapse.onto x hx
      obtain ⟨v, hv, hva⟩ := hqbij.2 a (collapse.function.bound_l ha).1
      exact ⟨v, hv, (comp.value_l qf collapse.function hva).mpr ha⟩
  exact ⟨N, B, F, j, e, S, g, hN, hB, hF, hg.1, hull.1, hull.2.1, ht, collapse, hj, inverse, model, embedding, gb⟩

/-- 只需编码的单向搬运，壳与塌缩即自动属于目标源。 -/
theorem ep_skolem_step_l {ω κ K Z W L Y V c A R U f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y V)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Z) (subsets : Ea_subset_d ω κ Z Y)
    (hA : M.mem A Z) (hU : M.mem U Z) (hf : M.mem f Z) (hm : Smem_d I c A R)
    (hAt : M.TransitiveSet A) (hκ : M.IsOrdinal κ) (hUA : M.MemberSubset U A)
    (bij : M.IsSetBijectionFromTo I f κ U) :
    ∃ N B F j e S, M.mem B Y ∧ M.mem B Z ∧ M.mem F Z ∧ M.MemberSubset U N ∧ M.MemberSubset N A ∧
      M.TransitiveSet B ∧ Mc_iso_d N B F ∧ M.IsSetBijectionFromTo I j B N ∧
      (∀ x y, Rd_entry_d y x j ↔ Rd_entry_d x y F) ∧ Smem_d I e B S ∧ Smap_d I ω e c B A j := by
  obtain ⟨N, B, F, j, e, S, g, _, hB, hF, hg, hUN, hNA, ht, collapse, hj, inverse, model, embedding, gb⟩ :=
    ep_skolem_collapse_l hZF source small hA hU hf hm hAt hκ hUA bij
  exact ⟨N, B, F, j, e, S, subsets.transitive_l hZF source target ht hg gb,
    hB, hF, hUN, hNA, ht, collapse, hj, inverse, model, embedding⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定秩层种子的小壳调整

实际构造 Vκ∪{κ,σ} 的源内 κ 枚举，再取壳和传递塌缩。
输出模型属于一致的另一源；嵌入图及其可数性见证属于输出模型自身，
并保持所有值在 Vκ∪{κ} 中的原图条目。内部正则秩段的调整还保留
完整源证书、枝反射、相对层级、相对幂集和小壳闭包，可继续下一步构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_skolem_adjust_l {ω κ K Z W L Y V a c D A R T σ ι : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y V)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Z) (subsets : Ea_subset_d ω κ Z Y)
    (level : Er_level_d Z κ T) (hA : M.mem A Z) (hAt : M.TransitiveSet A) (hm : Smem_d I c A R)
    (hTA : M.MemberSubset T A) (hκA : M.mem κ A) (hσA : M.mem σ A) (hιA : M.mem ι A)
    (hD : M.TransitiveSet D) (hσ : Smap_d I ω a c D A σ) (countable : M.IsSetInjectionFromTo I ι σ ω) :
    ∃ B e S j k η, M.mem B Y ∧ M.mem B Z ∧ M.TransitiveSet B ∧ Smem_d I e B S ∧
      M.mem ω B ∧ Smap_d I ω e c B A j ∧
      M.MemberSubset T B ∧ M.mem κ B ∧ M.MemberSubset D B ∧
      M.mem k B ∧ M.mem η B ∧ Smap_d I ω a e D B k ∧ M.IsSetInjectionFromTo I η k ω ∧
      ∀ x y, Rd_entry_d x y σ → (M.mem y T ∨ y = κ) → Rd_entry_d x y k := by
  have ht := level.hierarchy.transitive_l source.transitive level.member
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
    rcases (source.omega.isOrdinal (ZF.modelsKP hZF)).trichotomy hZF.1 hκ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
    · exact (us ω).mpr (Or.inr (hZF.1.eq_of_same_members ω κ eq))
    · exact (us ω).mpr (Or.inl (ords ω lt))
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ (source.below κ gt)).elim
  have hCA : M.MemberSubset C A := fun x hx => ((cs x).mp hx).elim
    (fun hx => ((us x).mp hx).elim (hTA x) (fun eq => eq ▸ hκA)) (fun eq => eq ▸ hσA)
  obtain ⟨H, B, F, j, e, S, g, _, hB, _, hg, seed, _, hBt, _, bij, _, model, emb, gb⟩ :=
    ep_skolem_collapse_l hZF source small hA hC hq hm hAt hκ hCA cq
  have hBY := subsets.transitive_l hZF source target hBt hg gb
  obtain ⟨k, _, hk⟩ := bij.2 σ (seed σ ((cs σ).mpr (Or.inr rfl)))
  obtain ⟨hkB, hDB, hUB, elem, ⟨η, hη, hi⟩, fixed⟩ := emb.countable_factor_l hZF source.omega hBt hAt model hm
    hD hσ hk hιA countable hUt hωU (fun x hx =>
      (bij.2 x (seed x ((cs x).mpr (Or.inl hx)))).imp fun _ h => h.2)
  exact ⟨B, e, S, j, k, η, hBY, hB, hBt, model, hUB ω hωU, emb, fun x hx => hUB x ((us x).mpr (Or.inl hx)),
    hUB κ ((us κ).mpr (Or.inr rfl)), hDB, hkB, hη, elem, hi, fun x y hxy hy => fixed x y hxy ((us y).mpr hy)⟩

/-- 尝试树回收、严格秩界和小壳调整的直接入口；不预设新嵌入属于秩初段。 -/
theorem ep_skolem_rank_step_l {ω κ K Z W L Y V α a c D Q A R T τ ι σ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y V)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Z) (subsets : Ea_subset_d ω κ Z Y)
    (branches : Sc_branch_d ω Z) (hierarchy : Sc_hierarchy_d Z) (power : Sc_power_d Z) (level : Er_level_d Z κ T)
    (hA : M.mem A Z) (rank : Vr_d Z α A) (regular : Sc_regular_d Z α)
    (hTA : M.MemberSubset T A) (hκA : M.mem κ A)
    (hD : M.mem D Z) (hDt : M.TransitiveSet D) (hm : Smem_d I a D Q) (hn : Smem_d I c A R)
    (hτ : M.mem τ Z) (hι : M.mem ι Z) (countable : M.IsSetInjectionFromTo I ι D ω)
    (hσ : Smap_d I ω a c D A σ) (prescribed : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y σ) :
    ∃ B e S j k η L, M.mem B Y ∧ M.mem B Z ∧ M.TransitiveSet B ∧ Smem_d I e B S ∧
      M.mem ω B ∧ Smap_d I ω e c B A j ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L B S ∧
      Sc_branch_d ω B ∧ Sc_hierarchy_d B ∧ Sc_power_d B ∧ Sc_cover_d B ∧ Sh_source_d (ZF.modelsKP hZF) ω B ∧
      (Sc_inaccessible_closure_d I ω Z → Sc_inaccessible_closure_d I ω B) ∧
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
  have hAt := rank.transitive_l source.transitive hA
  have hωA := rank.subset_mem_l source.transitive hA hκA source.omega_mem source.below
  have hωα := rank.ordinal_height_l hZF source.transitive hA (source.omega.isOrdinal (ZF.modelsKP hZF)) hωA
  have bound := regular ω hωα
  have hl := sc_omega_bound_limit_l hZF source.omega source.transitive hb source.theory source.omega_mem hα
    (cert A hA).1 hne bound
  have ba := branches.rank_l source.transitive hA rank hl hωA
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
    ep_skolem_adjust_l hZF source target small subsets level hA hAt
      hn hTA hκA hjA hηA hDt hj hη
  obtain ⟨L', next⟩ := cut.pull_l hZF hCt hωC model hn back hκC hκ source.below
  exact ⟨C, e, S, q, k, ξ, L', hCY, hCZ, hCt, model, hωC, back, next,
    ba.pull_l hZF source.omega hCt hAt hωC model hn back,
    (sc_hierarchy_iff_l hZF source.omega hCt hAt model hn back).mpr ha,
    (sc_power_iff_l hZF source.omega hCt hAt model hn back).mpr (power.rank_l source.transitive hA rank hl),
    (sc_cover_iff_l hZF source.omega hCt hAt model hn back).mpr (sc_rank_cover_l source.transitive hA rank),
    (sh_source_iff_l hZF next cut model hn back).mpr sa,
    fun closure => (sc_inaccessible_closure_iff_l hZF source.omega hCt hAt
      (next.algebra_l (ZF.modelsKP hZF)).pair (cut.algebra_l (ZF.modelsKP hZF)).pair model hn back hωC).mpr
        (closure.rank_l hZF source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair hA rank hl),
    hTC, hκC, hDC, hk, hξ, elem, hi,
    fun x y hxy hy => fixed x y (res x y hxy) hy⟩

end YesMetaZFC.SetTheory.LargeCardinal
