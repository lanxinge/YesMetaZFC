import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceComposition

/-! # 源内部的实际坐标重排图

给定 q:m→n 及两个实际函数空间，在源中构造 t(s)=s∘q。坐标长度不必是
外部有限数；这里甚至只要求给定域、值域和函数空间。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_reindex_l {ω χ c d X R H S e m n κ q D E} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (he : Smap_d I ω c d X H e)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X) (hEX : M.mem E X)
    (hq : Fn0_d m n q) (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  let ρ : Env M 4 := ⟨Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m))), fun _ => m⟩
  let φ : BinarySchema 4 := { body := cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s r : φ.denote ρ s r ↔ Cp0_d m n κ q s r := cp0_sat_l hZF.1 ..
  obtain ⟨t, C, htX, hC, hTC, select⟩ := smap_uniform_source_l hZFC hω hχ hωχ hH hX hm hn he φ (cp0_delta_l ..) ρ
    (Fin.cases hqX (Fin.cases hκX (Fin.cases hnX (fun _ => hmX)))) hEX (fun s hs => by
      obtain ⟨r, hr, hc⟩ := smap_compose_l hZFC hω hχ hωχ hH hX hm hn he hmX hnX hqX (hX E hEX s hs)
        hq (((hE s).mp hs).mono_target_l (hX κ hκX))
      exact ⟨r, hr.1, (sat s r).mpr (hc.retarget_l ((hE s).mp hs))⟩)
  have read s r (h : Rd_entry_d s r t) := (sat s r).mp (select s r h)
  refine ⟨t, htX, hTC.retarget_l (fun s r h => (hD r).mpr (read s r h).1), fun s r => ⟨?_, ?_⟩⟩
  · exact fun h => ⟨(hTC.bound_l h).1, read s r h⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨r', _, hsr⟩ := hTC.2.1 s hs
    exact cp0_unique_l hZF.1 hq ((hE s).mp hs) (read s r' hsr) hr ▸ hsr

end YesMetaZFC.SetTheory.Internal
