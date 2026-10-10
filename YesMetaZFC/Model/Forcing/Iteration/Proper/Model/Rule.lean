import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Basic
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Basic
import YesMetaZFC.Model.Forcing.Applications.Cohen.Proper

/-! # 原公式 proper 后继规则的共同模型装配

沿已构造递归读取真实后继名称，再一次生成全部辅助图与共同 N。
Cohen 原公式规则提供任意添加量的实际实例；本层不宣称极限阶段的 properness。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pr_rule_d (I : kpair_convention_l.Interpretation M) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) : Prop :=
  ∀ δ F G b D V, Row_system_d I δ F G b → (∃ α, M.SuccessorOf δ α) →
    φ.denote (row_rule_env_l ρ δ F G b) D V →
      ∃ α B R, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Row_pr_next_d (M := M) α B R b D V

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 从实际递归的后继记录构造统一 proper 辅助图。 -/
theorem row_iteration_pr_family_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I k ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I k ω b φ ρ δ F G) : ∃ U, Row_pr_family_d I δ F G b U := by
  apply row_pr_family_l hZFC h.1
  intro α β D V hβ hD hV
  obtain ⟨F', G', hF, hG, hi, ha⟩ := row_iteration_step_l hZF hω hRule h hD hV
  have hα := hi.1.conditions.1.mem hβ.predecessor_mem
  rcases ha with ⟨hs, ha⟩ | hl
  · obtain ⟨α', B, R, hβ', hB, hR, hn⟩ := hPr β F' G' b D V hi.1 hs ha
    have he := Structure.SuccessorOf.predecessor_eq hZF.1 hα hβ hβ'
    subst α'
    exact ⟨B, R, ((hF.2 α B).mp hB).2, ((hG.2 α R).mp hR).2, hn⟩
  · exact (successor_not_union_l hα hβ hl.sup).elim

/-- 给定原公式 proper 规则与迭代，自动构造共同模型、相邻区间和全部内部有限区间。 -/
theorem row_iteration_pr_prepare_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω δ F G b A}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I k ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I k ω b φ ρ δ F G) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ U χ H N w v J, Row_pr_family_d I δ F G b U ∧ Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧
      M.mem ω N ∧ M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧ M.mem U N ∧ M.mem J N ∧
      Hlift_d M ω δ F G b χ H N w v ∧ Check_graph_d M b J ∧
      (∀ i P, Entry_d M i P F → ∃ t, Entry_d M P t J) ∧
      (∀ α β B R D V, M.mem α N → M.SuccessorOf β α → Entry_d M α B F → Entry_d M α R G →
        Entry_d M β D F → Entry_d M β V G → Row_pil_d I α B R b D V N) ∧
      ∀ i, M.mem i ω → Row_pil_stage_d I F G b N i := by
  obtain ⟨U, hU⟩ := row_iteration_pr_family_l hZFC hω hRule hPr h
  exact row_pr_prepare_l hZFC hω h.1 hU ha

/-- 现有 Cohen 规则满足 proper 名称后继规格，有限及可数支撑共同使用此实例。 -/
theorem cohen_rule_pr_l (ρ : Env M 1) : Row_pr_rule_d I cohen_rule_s ρ := by
  intro δ F G b D V h _ hc
  obtain ⟨α, B, R, k, hδ, hB, hR, hk, A, T, t, hn, hNext⟩ := (cohen_rule_denote_l I hZF.1 ρ δ F G b D V).mp hc
  have hs := h.stages α B R hB hR
  obtain ⟨k', _, hkn, hu⟩ := zf_check_l M hZF hs.base (ρ.bound 0)
  have he := hu k hk
  have hkn : Name_d M B k := he.symm ▸ hkn
  have hne : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, hn.1.2.1, cohen_names_proper_l hs.order hZFC hkn hn hs.base hne, hNext⟩

end YesMetaZFC.Model.Forcing.Internal
