import YesMetaZFC.Model.Forcing.Proper.Basic
import YesMetaZFC.Model.Forcing.Applications.Cohen.FiniteSupport

/-! # 任意添加量名称的实际 properness 力迫证书

原 ZFC 中已构造的 Cohen 偏序满足 CCC，其内部可数主条件 club 也实际存在。
通过原公式有效性转为全部正条件上的 properness 证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem cohen_names_proper_l {B R z κ A T t} (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    (hκ : Name_d M B κ)
    (h : Cohen_names_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z κ A T t)
    {p} (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z (proper_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) p := by
  let hZF := ZFC.models_zf_l hZFC
  let χ : Formula 1 3 := cohen_m (.bound 2) (.bound 0) (.bound 1)
  let ψ : Formula 1 2 := proper_exists_m (.bound 0) (.bound 1)
  let j : Fin 2 → Term 3 := fun i => .bound i.castSucc
  let φ : Formula 1 3 := .imp χ (ψ.bind j)
  have hχ : χ.FreeClosed := cohen_m_freeClosed _ _ _ rfl rfl rfl
  have hψ : ψ.FreeClosed := proper_exists_m_freeClosed _ _ rfl rfl
  have hφ : φ.FreeClosed := by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨hχ, (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr hψ⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZFC) (η : Env N 3) : Formula.satisfies η φ := by
    apply (Formula.satisfies_imp_iff _ _ _).mpr
    intro hcohen
    let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hN)))
    obtain ⟨ν, hν, L, _, hc, _⟩ := cohen_spec_forcing_l N hN ((cohen_sat_l J hN.1 η _ _ _).mp hcohen)
    apply (Formula.satisfies_bind _ _ _).mpr
    exact (proper_exists_sat_l J hN.1 _ _ _).mpr ⟨ν, hν, ccc_proper_l L hN hν hc⟩
  let ρ := cohen_env_l κ A T
  have hn : ∀ v : Term 3, Name_d M B (v.eval ρ) := by
    intro v
    cases v with
    | free _ => exact hκ
    | bound i => exact Fin.cases h.1.1 (Fin.cases h.1.2.1 (fun _ => hκ)) i
  have hc := forces_mp_l hZF.1 (forces_regular_l O hZF χ ρ hn).1
    (forces_regular_l O hZF (ψ.bind j) ρ hn) hp hz
    (forces_valid_l O hZFC φ hφ valid ρ (fun i => hn (.bound i)) hp hz) (h.2.2.1 p hp hz)
  exact (forces_env_l hZF.1 ψ hψ _ (ord_env_l M A T)
    (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) p).mp ((forces_bind_l hZF.1 ψ j ρ p).mp hc)

end YesMetaZFC.Model.Forcing.Internal
