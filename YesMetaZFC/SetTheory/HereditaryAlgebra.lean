import YesMetaZFC.SetTheory.HereditaryClosure
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction

/-! # 正则 H(χ) 的配对与乘积封闭

Kuratowski 配对和笛卡尔积保持遗传小性，供内部模型与力迫共同使用。
原小集合封闭和实际基数计数给出这些集合，不增加强极限前提。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
include hω hχ hωχ hH

theorem h_pair_l {p a b} (hp : Pair_d M p a b) (ha : M.mem a H) (hb : M.mem b H) : M.mem p H := by
  obtain ⟨E, hE⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have he : M.CardinalLessOrEqual I E ω := ZF.exists_inclusionInjection hZF I (fun x hx => (hE x hx).elim)
  obtain ⟨S, hS⟩ := KP.exists_insert (ZF.modelsKP hZF) E a
  have hs := ZF.countable_insert_l I hZF hω he hS
  have hp' x : M.mem x p ↔ M.mem x S ∨ x = b := by
    rw [hS x]
    exact (hp x).trans ⟨fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr,
      fun h => h.elim (fun h => h.elim (fun h => (hE x h).elim) Or.inl) Or.inr⟩
  exact ZFC.h_small_closed_l I hZFC hω hχ hωχ hH (fun x hx =>
    ((hp x).mp hx).elim (fun he => he.symm ▸ ha) (fun he => he.symm ▸ hb)) hωχ
      (ZF.countable_insert_l I hZF hω hs hp')

theorem h_kpair_l {p a b} (hp : KPair_d M p a b) (ha : M.mem a H) (hb : M.mem b H) : M.mem p H := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  have hs' : Pair_d M s a a := fun x => (hs x).trans ⟨Or.inl, fun h => h.elim id id⟩
  exact h_pair_l hZFC hω hχ hωχ hH hp
    (h_pair_l hZFC hω hχ hωχ hH hs' ha ha) (h_pair_l hZFC hω hχ hωχ hH ht ha hb)

theorem h_product_l {A B P} (ha : M.mem A H) (hb : M.mem B H)
    (hP : M.IsCartesianProduct I P A B) : M.mem P H := by
  obtain ⟨α, hα, haα⟩ := ZF.hmem_size_l I hZF ((hH A).mp ha)
  obtain ⟨β, hβ, hbβ⟩ := ZF.hmem_size_l I hZF ((hH B).mp hb)
  obtain ⟨ν, hνχ, hν, hαν, hβν⟩ := ZF.common_cardinal_l I hZF hχ.isCardinal.1 hωχ hα hβ
  obtain ⟨F, hF⟩ := haα
  obtain ⟨G, hG⟩ := hαν
  obtain ⟨J, hJ⟩ := ZF.exists_compositionInjection hZF I hF hG
  obtain ⟨F, hF⟩ := hbβ
  obtain ⟨G, hG⟩ := hβν
  obtain ⟨K, hK⟩ := ZF.exists_compositionInjection hZF I hF hG
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ν ν
  obtain ⟨L, hL⟩ := ZF.exists_cartesianProductInjection hZF I hP hW hJ hK
  obtain ⟨F, hF⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hν.1, Structure.Equinumerous.refl hZF I ν⟩ hW
    (ZF.infiniteCardinal_selfMultiplication hZF I hω (ZF.omega_cardinal_l I hZF hω) hν)
  apply ZFC.h_small_closed_l I hZFC hω hχ hωχ hH ?_ hνχ (ZF.exists_compositionInjection hZF I hL hF)
  intro p hp
  obtain ⟨a, haA, b, hbB, hp⟩ := (hP p).mp hp
  exact h_kpair_l hZFC hω hχ hωχ hH hp
    (ZF.h_transitive_l I hZF hH A ha a haA) (ZF.h_transitive_l I hZF hH B hb b hbB)

theorem h_fibers_l {R B T} (hR : M.mem R H) (hB : M.mem B H)
    (hT : InnerModel.Rd_fun_d .fibers R B R T) : M.mem T H := by
  let φ : BinarySchema 1 := { body := InnerModel.rd_fiber_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => R, fun _ => R⟩
  have sat b t : φ.denote ρ b t ↔ InnerModel.Rd_fiber_d R b t := InnerModel.rd_fiber_sat_l hZF.1 ..
  obtain ⟨F, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := T)
    (fun b _ => (InnerModel.rd_fiber_exists_l (ZF.modelsKP hZF) R b).imp fun t ht => (sat b t).mpr ht)
    (fun b _ t u ht hu => hZF.1.eq_of_same_members t u fun x => ((sat b t).mp ht x).trans ((sat b u).mp hu x).symm)
    (fun b t hb ht => (hT t).mpr ⟨b, hb, (sat b t).mp ht⟩)
  have onto t (ht : M.mem t T) : ∃ b, M.mem b B ∧ M.PairMember I b t F := by
    obtain ⟨b, hb, hbt⟩ := (hT t).mp ht
    exact ⟨b, hb, (spec b t).mpr ⟨hb, (sat b t).mpr hbt⟩⟩
  obtain ⟨μ, hμ, size⟩ := ZF.hmem_size_l I hZF ((hH B).mp hB)
  apply h_small_closed_l I hZFC hω hχ hωχ hH ?_ hμ
    (ZF.ordinal_image_bound_l I hZF (hχ.isCardinal.1.mem hμ) size hf onto)
  intro t ht
  obtain ⟨b, _, fiber⟩ := (hT t).mp ht
  obtain ⟨S, ν, hs, hν, bound⟩ := (hH R).mp hR
  exact (hH t).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal hs.1
    (fun x hx => (InnerModel.rd_entry_transitive_l hs.1 hs.2.1 ((fiber x).mp hx)).1) hν bound)

end YesMetaZFC.SetTheory.ZFC
