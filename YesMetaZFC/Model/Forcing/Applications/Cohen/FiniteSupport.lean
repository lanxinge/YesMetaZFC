import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.RecursionCCC
import YesMetaZFC.Model.Forcing.Applications.Cohen.Add

/-! # 参数化 Cohen 有限支撑迭代的一键 CCC 实例

先由原 ZFC 中 Cohen 偏序的实际 CCC 定理取得名称层的全局力迫证书，再验证
现有原公式后继规则。给定内部长度与添加量，即返回整个迭代及全部阶段 CCC。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 任意添加量名称产生的规范 Cohen 偏序，在每个正条件上被迫 CCC。 -/
theorem cohen_names_ccc_l {B R z κ A T t} (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    (hκ : Name_d M B κ)
    (h : Cohen_names_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z κ A T t)
    {p} (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z (ccc_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) p := by
  let hZF := ZFC.models_zf_l hZFC
  let χ : Formula 1 3 := cohen_m (.bound 2) (.bound 0) (.bound 1)
  let ψ : Formula 1 2 := ccc_exists_m (.bound 0) (.bound 1)
  let j : Fin 2 → Term 3 := fun i => .bound i.castSucc
  let φ : Formula 1 3 := .imp χ (ψ.bind j)
  have hχ : χ.FreeClosed := cohen_m_freeClosed _ _ _ rfl rfl rfl
  have hψ : ψ.FreeClosed := ccc_exists_m_freeClosed _ _ rfl rfl
  have hφ : φ.FreeClosed := by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨hχ, (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr hψ⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZFC) (η : Env N 3) : Formula.satisfies η φ := by
    apply (Formula.satisfies_imp_iff _ _ _).mpr
    intro hcohen
    let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hN)))
    obtain ⟨ν, hν, _, _, hc, _⟩ := cohen_spec_forcing_l N hN ((cohen_sat_l J hN.1 η _ _ _).mp hcohen)
    apply (Formula.satisfies_bind _ _ _).mpr
    exact (ccc_exists_sat_l J hN.1 _ _ _).mpr ⟨ν, hν, hc⟩
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

/-- 现有 Cohen 原公式规则满足真实 CCC 名称后继规格。 -/
theorem cohen_rule_ccc_l (hZFC : M.Models ZFC) (ρ : Env M 1) :
    Row_ccc_rule_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) cohen_rule_s ρ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro δ F H e D V hs _ hc
  obtain ⟨α, B, R, k, hδ, hB, hR, hk, A, T, t, hn, hNext⟩ := (cohen_rule_denote_l I hZF.1 ρ δ F H e D V).mp hc
  have hStage := hs.stages α B R hB hR
  obtain ⟨k', _, hkn, hu⟩ := zf_check_l M hZF hStage.base (ρ.bound 0)
  have he := hu k hk
  have hkn : Name_d M B k := he.symm ▸ hkn
  have hne : e ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hStage.base)
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, hn.1.2.1, hn.2.2.2.1 e hStage.base hne,
    cohen_names_ccc_l hStage.order hZFC hkn hn hStage.base hne, hNext⟩

/-- 只给内部序数长度与添加量，自动构造有限支撑 Cohen 迭代及每个阶段的 CCC。 -/
theorem cohen_iteration_ccc_l (hZFC : M.Models ZFC) (κ : M.Domain) {α} (hα : M.IsOrdinal α) :
    ∃ ω e F H, M.IsOmega ω ∧ Row_iteration_d
      (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω e cohen_rule_s
      (⟨fun _ => κ, fun _ => κ⟩ : Env M 1) α F H ∧
      ∀ δ D V, Entry_d M δ D F → Entry_d M δ V H → Ccc_d M
        (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨F, H, h, hc⟩ := row_iteration_ccc_exists_l hZFC hω he hα
    (cohen_rule_l hZF hω false ρ) (cohen_rule_ccc_l hZFC ρ)
  exact ⟨ω, e, F, H, hω, h, hc⟩

end YesMetaZFC.Model.Forcing.Internal
