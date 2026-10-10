import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemInitial
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingCountable
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.Model.SetTheory.Internal.Collapse

/-! # 小 Skolem 壳的源内塌缩及跨源隶属

从种子的实际枚举出发构造壳、塌缩和塌缩的枚举。有限幂一致性随后自动
搬运关系码并还原传递模型，给出下降装配所需的一步隶属结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_skolem_collapse_l {ω κ K Z W c A R U f : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (small : Sh_source_d (ZF.modelsKP hZF) ω Z)
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
    source.cardinal_mem hN hq source.cardinal_small qf hqbij.2
  obtain ⟨B', F', hB', hF', iso'⟩ := source.collapse.collapse_l hN
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
    (source : Ep_source_d hZF ω κ K Z W) (target : Ep_source_d hZF ω κ L Y V)
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
