import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.SystemCCC
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Basic

/-! # 原公式后继规则的有限支撑 CCC 装配

规则须返回实际名称及二步编码。一般后继保持已在 `two_step_ccc_l` 证明；这里
仅将已构造递归的精确前缀方程接到模型内 CCC 超限归纳。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_ccc_rule_d (I : kpair_convention_l.Interpretation M) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) : Prop :=
  ∀ δ F H e D V, Row_system_d I δ F H e → (∃ α, M.SuccessorOf δ α) →
    φ.denote (row_rule_env_l ρ δ F H e) D V →
    ∃ α B R, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R H ∧ Row_ccc_next_d α B R e D V

theorem row_iteration_ccc_l (hZFC : M.Models ZFC) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {γ ω e F H}
    (hω : M.IsOmega ω)
    (hRule : Row_rule_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω φ ρ)
    (hC : Row_ccc_rule_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) φ ρ)
    (h : Row_iteration_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω e φ ρ γ F H) :
    ∀ δ D V, Entry_d M δ D F → Entry_d M δ V H → Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  let hZF := ZFC.models_zf_l hZFC
  apply row_system_ccc_l hZFC h.1 hω h.2.1
  intro α β D V hβ hD hV
  obtain ⟨A, C, hA, hH, hi, ha⟩ := row_iteration_step_l hZF hω hRule h hD hV
  have hα := hi.1.conditions.1.mem hβ.predecessor_mem
  rcases ha with ⟨hs, ha⟩ | hl
  · obtain ⟨α', B, R, hβ', hB, hR, hn⟩ := hC β A C e D V hi.1 hs ha
    have he := Structure.SuccessorOf.predecessor_eq hZF.1 hα hβ hβ'
    subst α'
    exact ⟨B, R, ((hA.2 α B).mp hB).2, ((hH.2 α R).mp hR).2, hn⟩
  · exact False.elim (successor_not_union_l hα hβ hl.sup)

/-- 给定已实现的原公式 CCC 后继规则，一次构造整个有限支撑迭代及全部阶段 CCC。 -/
theorem row_iteration_ccc_exists_l (hZFC : M.Models ZFC) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {γ ω e}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hγ : M.IsOrdinal γ)
    (hRule : Row_rule_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω φ ρ)
    (hC : Row_ccc_rule_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) φ ρ) : ∃ F H,
    Row_iteration_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω e φ ρ γ F H ∧
    ∀ δ D V, Entry_d M δ D F → Entry_d M δ V H → Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  obtain ⟨F, H, h⟩ := row_iteration_l (ZFC.models_zf_l hZFC) hω he hRule hγ
  exact ⟨F, H, h, row_iteration_ccc_l hZFC hω hRule hC h⟩

end YesMetaZFC.Model.Forcing.Internal
