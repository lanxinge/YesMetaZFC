import YesMetaZFC.SetTheory.Hereditary
import YesMetaZFC.SetTheory.Card.SmallUnion

/-! # 正则 H(χ) 的小集合闭性

对小族统一收集成员的传递闭包。正则性控制其实际并，追加原小族后得到一个
小传递容器，从而证明该小族本身属于 H(χ)。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem h_small_closed_l (hZFC : M.Models ZFC) {ω χ H A μ} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hA : M.MemberSubset A H) (hμ : M.mem μ χ) (ha : M.CardinalLessOrEqual I A μ) : M.mem A H := by
  have hZF := models_zf_l hZFC
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
  let φ : BinarySchema 0 := { body := tc_m (.bound 1) .newest }
  have hφ x T : φ.denote ρ x T ↔ Tc_d (M := M) x T := tc_sat_l _ _ _
  have total x : ∃ T, φ.denote ρ x T := (ZF.tc_exists_l I hZF x).elim fun T hT => ⟨T, (hφ x T).mpr hT⟩
  have unique x S T (hS : φ.denote ρ x S) (hT : φ.denote ρ x T) : S = T :=
    tc_unique_l hZF.1 ((hφ x S).mp hS) ((hφ x T).mp hT)
  obtain ⟨C, hC⟩ := ZF.exists_functionalImage hZF φ ρ A (fun x _ => total x) unique
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun x _ => total x) (fun x _ => unique x) (fun x T hx hT => (hC T).mpr ⟨x, hx, hT⟩)
  have hCμ := ZF.ordinal_image_bound_l I hZF (hχ.isCardinal.1.mem hμ) ha hF (fun T hT => by
    obtain ⟨x, hx, ht⟩ := (hC T).mp hT
    exact ⟨x, hx, (hf x T).mpr ⟨hx, ht⟩⟩)
  obtain ⟨U, hU⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hCt T (hT : M.mem T C) : M.TransitiveSet T := by
    obtain ⟨x, _, hx⟩ := (hC T).mp hT
    exact ((hφ x T).mp hx).1
  have hUt : M.TransitiveSet U := by
    intro x hx y hy
    obtain ⟨T, hTC, hxT⟩ := (hU x).mp hx
    exact (hU y).mpr ⟨T, hTC, hCt T hTC x hxT y hy⟩
  obtain ⟨ν, hν, hu⟩ := small_union_l I hZFC hω hχ hωχ hμ hCμ hU (fun T hTC => by
    obtain ⟨x, hxA, hxT⟩ := (hC T).mp hTC
    obtain ⟨S, ν, hS, hν, hs⟩ := (hH x).mp (hA x hxA)
    have he := tc_unique_l hZF.1 ((hφ x T).mp hxT) hS
    exact ⟨ν, hν, he.symm ▸ hs⟩)
  apply (hH A).mpr
  apply ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal hUt ?_ hν hu
  intro x hx
  obtain ⟨T, hxT⟩ := total x
  exact (hU x).mpr ⟨T, (hC T).mpr ⟨x, hx, hxT⟩, ((hφ x T).mp hxT).2.1⟩

end YesMetaZFC.SetTheory.ZFC
