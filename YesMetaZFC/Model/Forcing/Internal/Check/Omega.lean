import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 内部 ω 的规范名称力迫

规范嵌入保留内部 ω，有限参数反射将该语义对应转成每个适用正条件上的原公式证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_omega_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b ω w p}
    (hω : M.IsOmega ω) (hb : M.mem b B) (hw : Check_d M b ω w) (hp : Below_d M B R z p b) :
    Forces_d M B R z (Formula.isOmega .newest) (⟨fun _ => w, fun _ => w⟩ : Env M 1) p := by
  let ρ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push ω).push w).push p
  let α : Formula 1 7 := .conj (Formula.isOmega (.bound 2)) (.conj (.mem (.bound 3) (.bound 6))
    (.conj (check_m (.bound 3) (.bound 2) (.bound 1)) (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 3))))
  have raw (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 7) : Formula.satisfies η α ↔
      N.IsOmega (η.bound 2) ∧ N.mem (η.bound 3) (η.bound 6) ∧ Check_d N (η.bound 3) (η.bound 2) (η.bound 1) ∧
      Below_d N (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 0) (η.bound 3) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff,
      check_sat_l N hE, below_sat_l N hE]
    rfl
  have hh := forces_of_generics_l (Formula.isOmega .newest) (Formula.isOmega_freeClosed _ rfl) α
    (by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]) (fun _ : Fin 1 => (.bound 1 : Term 7))
    (.bound 6) (.bound 5) (.bound 4) .newest (fun _ => rfl) rfl rfl rfl rfl
    (fun N hN η L _ _ _ ha U hU hpU ξ hξ => ?_) hZF ρ O
      (fun _ => check_name_l M (check_range_l M hZF) hb hw) hp.1 hp.2.1 ((raw M hZF.1 ρ).mpr ⟨hω, hb, hw, hp⟩)
  · exact (forces_env_l hZF.1 (Formula.isOmega .newest) (Formula.isOmega_freeClosed _ rfl)
      (⟨fun _ => (Term.bound 1 : Term 7).eval ρ, ρ.free⟩ : Env M 1)
      (⟨fun _ => w, fun _ => w⟩ : Env M 1) (fun _ => rfl) p).mp hh
  · obtain ⟨hω', hb', hw', hp'⟩ := (raw N hN.1 η).mp ha
    obtain ⟨e, hv, he, hi⟩ := check_map_l L hN hU (hU.upward _ _ hpU hb' hp'.2.2)
    have hE := preserves_zf_l L hN hU
    have hwE := image_omega_l (hEN := hE.1) e hi he hN (internal_foundation_l L hN hU) hω'
      (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (e (η.bound 2)))
    have ht := qval_unique_l (hv _ _ hw') (hξ 0)
    rw [ht] at hwE
    exact (Formula.satisfies_isOmega_iff ξ .newest).mpr hwE

end YesMetaZFC.Model.Forcing.Internal
