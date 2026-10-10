import YesMetaZFC.Model.Forcing.Closed.Proper
import YesMetaZFC.Model.Forcing.Closed.Syntax
import YesMetaZFC.Model.Forcing.Internal.Check.Omega

/-! # 可数闭名称的实际 properness 力迫证书

原模型中的可数闭预序定理经原公式有效性传输，在同一条件上给出 properness。
这里只接收真实预序与闭性证书，内部 ω 由其规范名称自动取得。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem closed_name_proper_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {b p ω w A T}
    (hω : M.IsOmega ω) (hb : M.mem b B) (hw : Check_d M b ω w) (hp : Below_d M B R z p b)
    (hA : Name_d M B A) (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p)
    (hc : Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p) :
    Forces_d M B R z (proper_exists_m .newest (.bound 1)) (ord_env_l M A T) p := by
  have hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T
  let j : Fin 2 → Term 3 := Fin.cases (.bound 1) (fun _ => .newest)
  let k : Fin 1 → Term 3 := fun _ => .bound 2
  let α := (preord_m .newest (.bound 1) : Formula 1 2).bind j
  let β := (Formula.isOmega .newest : Formula 1 1).bind k
  let γ : Formula 1 3 := closed_m (.bound 1) .newest (.bound 1) (.bound 2)
  let φ : Formula 1 3 := .conj α (.conj β γ)
  let ψ := (proper_exists_m .newest (.bound 1) : Formula 1 2).bind j
  have hj : ∀ i, (j i).freeSupport = [] := Fin.cases rfl (fun _ => rfl)
  have hk : ∀ i, (k i).freeSupport = [] := fun _ => rfl
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, α, β, γ, Definitional.Formula.FreeClosed, hj, hk]
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, hj]
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZFC) (η : Env N 3) :
      Formula.satisfies η (.imp φ ψ) := by
    let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hN)))
    apply (Formula.satisfies_imp_iff _ _ _).mpr
    intro hh
    have hh : Preord_d N (η.bound 1) (η.bound 0) ∧ N.IsOmega (η.bound 2) ∧
        Closed_d I (η.bound 1) (η.bound 0) (η.bound 1) (η.bound 2) := by
      simpa only [φ, α, β, γ, Formula.satisfies_conj_iff, Formula.satisfies_bind,
        preord_sat_l hN.1, Formula.satisfies_isOmega_iff, closed_sat_l I hN.1] using! hh
    apply (Formula.satisfies_bind η j _).mpr
    exact (proper_exists_sat_l I hN.1 _ _ _).mpr ⟨η.bound 2, hh.2.1, closed_proper_l hh.1 hN hh.2.1 hh.2.2⟩
  have hn : ∀ t : Term 3, Name_d M B (t.eval ρ) := by
    intro t
    cases t with
    | free _ => exact check_name_l M (check_range_l M hZF) hb hw
    | bound i => exact Fin.cases hT (Fin.cases hA (fun _ => check_name_l M (check_range_l M hZF) hb hw)) i
  have hα : Forces_d M B R z α ρ p := (forces_bind_l hZF.1 _ j ρ p).mpr
    ((forces_env_l hZF.1 _ (preord_m_freeClosed _ _ rfl rfl) _ _ (Fin.cases rfl (fun _ => rfl)) p).mp hP)
  have hβ : Forces_d M B R z β ρ p := (forces_bind_l hZF.1 _ k ρ p).mpr
    ((forces_env_l hZF.1 _ (Formula.isOmega_freeClosed _ rfl) _ _ (fun _ => rfl) p).mp
      (check_omega_force_l O hZF hω hb hw hp))
  have hφp : Forces_d M B R z φ ρ p := (forces_conj_l _ _ _ p).mpr ⟨hα, (forces_conj_l _ _ _ p).mpr ⟨hβ, hc⟩⟩
  have hψp := forces_mp_l hZF.1 (forces_regular_l O hZF φ ρ hn).1 (forces_regular_l O hZF ψ ρ hn)
    hp.1 hp.2.1 (forces_valid_l O hZFC (.imp φ ψ)
      (by simpa only [Definitional.Formula.FreeClosed] using And.intro hφ hψ)
      valid ρ (fun i => hn (.bound i)) hp.1 hp.2.1) hφp
  exact (forces_env_l hZF.1 _ (proper_exists_m_freeClosed _ _ rfl rfl) _ _
    (Fin.cases rfl (fun _ => rfl)) p).mp ((forces_bind_l hZF.1 _ j ρ p).mp hψp)

end YesMetaZFC.Model.Forcing.Internal
