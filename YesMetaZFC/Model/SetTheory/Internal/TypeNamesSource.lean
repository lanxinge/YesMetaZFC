import YesMetaZFC.Model.SetTheory.Internal.TypePoolBounded
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 源中实际构造完整名字域

在 n∪{n} 与 U×U 的并中作原名字谓词的有界分离。
因此名字域属于源，无须源满足 KP 或把背景幂集放入源。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tn_names_source_l {ω c X R n U : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (model : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : M.mem n X) (hU : M.mem U X) : ∃ N, M.mem N X ∧ Tn_names_d n U N := by
  obtain ⟨m, hm, succ⟩ := theory.algebra.insert_l hn hn
  obtain ⟨P, hP, prod⟩ := theory.algebra.product U U hU hU
  obtain ⟨B, hB, pair⟩ := theory.algebra.pair m P hm hP
  obtain ⟨D, hD, un⟩ := theory.algebra.union B hB
  have cover a (name : Tn_name_d n U a) : M.mem a D := by
    apply (un a).mpr
    rcases name with hi | rfl | ⟨x, hx, cp⟩
    · exact ⟨m, (pair m).mpr (Or.inl rfl), (succ a).mpr (Or.inl hi)⟩
    · exact ⟨m, (pair m).mpr (Or.inl rfl), (succ a).mpr (Or.inr rfl)⟩
    · exact ⟨P, (pair P).mpr (Or.inr rfl), (prod a).mpr ⟨x, hx, x, hx, cp⟩⟩
  let φ : UnarySchema 2 := { body := tn_name_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 2 := ⟨Fin.cases n (fun _ => U), fun _ => n⟩
  obtain ⟨N, hN, sep⟩ := sc_separate_source_l I hZF hω hX model theory φ (tn_name_delta_l ..)
    ρ (Fin.cases hn (fun _ => hU)) hD
  refine ⟨N, hN, fun a => (sep a).trans ?_⟩
  have read : φ.denote ρ a ↔ Tn_name_d n U a := tn_name_sat_l hZF.1 ..
  exact ⟨fun h => read.mp h.2, fun h => ⟨cover a h, read.mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal
