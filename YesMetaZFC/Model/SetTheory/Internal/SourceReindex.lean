import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceComposition
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily

/-! # 源内部的实际坐标重排图

给定 q:m→n 及两个实际函数空间，在源中构造 t(s)=s∘q。坐标长度不必是
外部有限数；这里甚至只要求给定域、值域和函数空间。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_reindex_l {ω c X R m n κ q D E} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X) (hEX : M.mem E X)
    (hq : Fn0_d m n q) (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  let ρ : Env M 4 := ⟨Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m))), fun _ => m⟩
  let φ : BinarySchema 4 := {
    body := Formula.existsMem (.bound 5) (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 6)
      (.conj (kpair0_m (.bound 3) (.bound 2) (.bound 1))
        (.conj (rd_entry0_m (.bound 2) .newest (.bound 5)) (rd_entry0_m .newest (.bound 1) (.bound 4)))))) }
  have sat s p : φ.denote ρ s p ↔ ∃ i, M.mem i m ∧ ∃ x, M.mem x κ ∧ ∃ j, M.mem j n ∧
      KPair_d M p i x ∧ Rd_entry_d i j q ∧ Rd_entry_d j x s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨P, hPX, product⟩ := theory.algebra.product m κ hmX hκX
  obtain ⟨t, C, htX, _, hTC, row⟩ := sc_separation_function_l hZF hω hX hm theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    ρ (Fin.cases hqX (Fin.cases hκX (Fin.cases hnX (fun _ => hmX)))) hEX hPX
  have read s u (hsu : Rd_entry_d s u t) : Cp0_d m n κ q s u := by
    have hs := (hE s).mp (hTC.bound_l hsu).1
    obtain ⟨r, hr⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hs
    have eq : u = r := hZF.1.eq_of_same_members u r fun p => by
      rw [row s u hsu p, sat s p]
      constructor
      · rintro ⟨_, i, _, x, _, j, _, code, hij, hjx⟩
        obtain ⟨v, hv, hvR⟩ := (hr.value_l hq hs hij).mpr hjx
        exact kpair_unique_l M hZF.1 hv code ▸ hvR
      · intro hp
        obtain ⟨i, hi, x, hx, code⟩ := hr.1.1 p hp
        obtain ⟨j, hj, hij⟩ := hq.2.1 i hi
        exact ⟨(product p).mpr ⟨i, hi, x, hx, code⟩, i, hi, x, hx, j, hj, code, hij,
          (hr.value_l hq hs hij).mp ⟨p, code, hp⟩⟩
    exact eq.symm ▸ hr
  refine ⟨t, htX, hTC.retarget_l (fun s r h => (hD r).mpr (read s r h).1), fun s r => ⟨?_, ?_⟩⟩
  · exact fun h => ⟨(hTC.bound_l h).1, read s r h⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨r', _, hsr⟩ := hTC.2.1 s hs
    exact cp0_unique_l hZF.1 hq ((hE s).mp hs) (read s r' hsr) hr ▸ hsr

end YesMetaZFC.SetTheory.Internal
