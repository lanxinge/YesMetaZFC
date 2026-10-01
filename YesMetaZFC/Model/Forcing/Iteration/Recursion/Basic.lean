import YesMetaZFC.Model.Forcing.Iteration.Recursion.Invariant

/-! # 任意内部序数长度的支撑迭代

给定已实现的原公式后继规则，一次构造完整阶段系统。递归、存在唯一性与
前缀方程均在原 ZF 内证明，两种支撑共用同一接口，不要求地模型外部良基。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_iteration_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω e : M.Domain) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (α F H : M.Domain) : Prop :=
  Row_system_d I α F H e ∧ Row_system_supp_d I k ω F ∧
  ∃ S, Row_history_d S F H ∧ M.IsRecursiveSequence I (Row_op_d I k ω e φ ρ) S α

/-- 完整迭代本身也由原公式表示，供后续保持定理在模型内量化与归纳。 -/
def row_iteration_s {n} (φ : BinarySchema (n+4)) (k : Bool) : BinarySchema (n+3) := {
  body := .conj (row_system_m (.bound 2) (.bound 1) .newest (.bound 3))
    (.conj (row_system_supp_m k (.bound 4) (.bound 1))
      (.existsE (.conj (row_history_m .newest (.bound 2) (.bound 1))
        (Formula.isRecursiveSequence kpair_convention_l (row_op_s φ k)
          (Definitional.TermVector.boundParameters (n+2) 4) .newest (.bound 3)))))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨row_system_m_freeClosed _ _ _ _ rfl rfl rfl rfl,
      row_system_supp_m_freeClosed _ _ _ rfl rfl, row_history_m_freeClosed _ _ _ rfl rfl rfl,
      Formula.isRecursiveSequence_freeClosed _ _ _ _ _ (Definitional.TermVector.boundParameters_freeClosed _ _) rfl rfl⟩ }

theorem row_iteration_denote_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (k : Bool) (ω e α F H) :
    (row_iteration_s φ k).denote ((row_op_env_l ρ ω e).push α) F H ↔ Row_iteration_d I k ω e φ ρ α F H := by
  have ho : (row_op_s φ k).denote (row_op_env_l ρ ω e) = Row_op_d I k ω e φ ρ :=
    funext fun S => funext fun c => propext (row_op_denote_l I hE φ ρ k ω e S c)
  simp only [row_iteration_s, BinarySchema.denote, Row_iteration_d, Formula.satisfies_conj_iff,
    row_system_sat_l I hE, row_system_supp_sat_l I hE, Formula.satisfies_exists_iff,
    row_history_sat_l hE, Formula.satisfies_isRecursiveSequence_iff I hE,
    Definitional.TermVector.evalEnv_boundParameters_four, ho]
  rfl

theorem row_op_class_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e}
    (hω : M.IsOmega ω)
    (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ) :
    M.IsClassFunctionOnTransfiniteSequences (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))
      ((row_op_s φ k).denote (row_op_env_l ρ ω e)) := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro S _
  obtain ⟨c, hc, hu⟩ := row_op_total_l hZF (e := e) hω hRule S
  exact ⟨c, (row_op_denote_l I hZF.1 φ ρ k ω e S c).mpr hc,
    fun c' h' => hu c' ((row_op_denote_l I hZF.1 φ ρ k ω e S c').mp h')⟩

/-- 整个阶段系统实际存在；输入是后继规则及内部长度，无需预先给出阶段族。 -/
theorem row_iteration_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e α}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (hα : M.IsOrdinal α) :
    ∃ F H, Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ α F H := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have ho : (row_op_s φ k).denote (row_op_env_l ρ ω e) = Row_op_d I k ω e φ ρ :=
    funext fun S => funext fun c => propext (row_op_denote_l I hZF.1 φ ρ k ω e S c)
  obtain ⟨S, hS⟩ := ZF.recursiveSequence_exists hZF I (row_op_env_l ρ ω e) (row_op_s φ k)
    (row_op_class_l hZF hω hRule) hα
  rw [ho] at hS
  obtain ⟨F, H, hg⟩ := row_recursive_good_l hZF hω he hRule hS
  exact ⟨F, H, hg.2.2.1, hg.2.2.2, S, hg.2.1, hS⟩

/-- 相同原公式规则、参数与内部长度决定字面相同的两张阶段序列。 -/
theorem row_iteration_unique_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e α F H F' H'}
    (hω : M.IsOmega ω)
    (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (h : Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ α F H)
    (h' : Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ α F' H') :
    F = F' ∧ H = H' := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨S, hHist, hS⟩ := h.2.2
  obtain ⟨S', hHist', hS'⟩ := h'.2.2
  have ho : (row_op_s φ k).denote (row_op_env_l ρ ω e) = Row_op_d I k ω e φ ρ :=
    funext fun S => funext fun c => propext (row_op_denote_l I hZF.1 φ ρ k ω e S c)
  have he := ZF.recursiveSequence_unique hZF I (row_op_env_l ρ ω e) (row_op_s φ k) (row_op_class_l hZF hω hRule)
    (by simpa only [ho] using hS) (by simpa only [ho] using hS')
  subst S'
  exact row_history_unique_l hZF.1 hHist hHist'

/-- 任一实际阶段都由同一递归的较短前缀产生，并满足真实后继或支撑极限方程。 -/
theorem row_iteration_step_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e α F H}
    (hω : M.IsOmega ω)
    (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (h : Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ α F H)
    {δ B R} (hB : Entry_d M δ B F) (hR : Entry_d M δ R H) : ∃ A C,
    M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) A F δ ∧
    M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) C H δ ∧
    Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ δ A C ∧
    Row_action_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ δ A C e B R := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨S, hh, hS⟩ := h.2.2
  obtain ⟨c, hδc, hbr⟩ := (row_history_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hS.1 hh δ B R).mp ⟨hB, hR⟩
  have hδ := (hS.1.2.2 δ).mpr ⟨c, hδc⟩
  obtain ⟨T, ht, hc⟩ := hS.2 δ hδ c hδc
  have hT := hS.restriction hδ ht
  obtain ⟨A, C, hg⟩ := row_recursive_good_l hZF hω h.1.empty hRule hT
  obtain ⟨D, V, hdv, ha, _⟩ := row_op_extend_l hZF hω hRule hg hc
  obtain ⟨hb, hr⟩ := kpair_injective_l M hbr hdv
  subst D; subst V
  exact ⟨A, C, row_part_restrict_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ht hh.1 hg.2.1.1,
    row_part_restrict_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ht hh.2 hg.2.1.2,
    ⟨hg.2.2.1, hg.2.2.2, T, hg.2.1, hT⟩, ha⟩

/-- 在实际非零极限阶段，自动提取准确前缀及支撑极限规格。 -/
theorem row_iteration_limit_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω b δ F G γ D V}
    (hω : M.IsOmega ω) (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (h : Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω b φ ρ δ F G)
    (hγ : M.IsLimitOrdinal γ) (hD : Entry_d M γ D F) (hV : Entry_d M γ V G) :
    ∃ F' G', M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F' F γ ∧
      M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) G' G γ ∧
      Row_iteration_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω b φ ρ γ F' G' ∧
      Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω γ F' G' γ D V := by
  obtain ⟨F', G', hF, hG, hp, ha⟩ := row_iteration_step_l hZF hω hRule h hD hV
  rcases ha with ⟨⟨α, hα⟩, _⟩ | hl
  · have hu : M.IsUnionOf γ γ := fun x => ⟨hγ.2.2 x, fun ⟨y, hy, hxy⟩ => hγ.1.transitive y hy x hxy⟩
    exact (successor_not_union_l (hγ.1.mem hα.predecessor_mem) hα hu).elim
  · exact ⟨F', G', hF, hG, hp, hl⟩

/-- 指定支撑模式、地模型添加量和内部长度，自动构造完整 Cohen 迭代。 -/
theorem cohen_iteration_l (hZF : M.Models ZF) (k : Bool) (κ : M.Domain) {α} (hα : M.IsOrdinal α) :
    ∃ ω e F H, M.IsOmega ω ∧ Row_iteration_d
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e cohen_rule_s
      (⟨fun _ => κ, fun _ => κ⟩ : Env M 1) α F H := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨F, H, h⟩ := row_iteration_l hZF hω he (cohen_rule_l hZF hω k ⟨fun _ => κ, fun _ => κ⟩) hα
  exact ⟨ω, e, F, H, hω, h⟩

end YesMetaZFC.Model.Forcing.Internal
