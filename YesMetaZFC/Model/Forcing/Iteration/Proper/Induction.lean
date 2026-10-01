import YesMetaZFC.Model.Forcing.Iteration.Proper.Limit
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Rule

/-! # 任意内部序数上的完整 proper 区间迭代引理

以实际 Row_pil_stage 原公式作内部序数归纳。后继使用 N 对前驱的封闭与真实
相邻区间，极限使用已构造的内部序列和主融合；不对外部序数作良基递归。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_induction_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b U χ H N w v}
    (hRule : Row_rule_d I true ω φ ρ) (h : Row_iteration_d I true ω b φ ρ δ F G)
    (hU : Row_pr_family_d I δ F G b U) (hN : Hsub_d I ω χ H N) (hLift : Hlift_d M ω δ F G b χ H N w v)
    (hFN : M.mem F N) (hGN : M.mem G N) (hUN : M.mem U N) (hωN : M.mem ω N) :
    ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  have next := row_pr_family_pil_l hZFC h.1 hU hN hLift hFN hGN hUN
  have hN' := hN
  obtain ⟨hω, hχ, _, hH, _, c, J, d, S, hM, hSub, hElem⟩ := hN'
  have same {α β B R D V} (he : α = β) (hB : Entry_d M α B F) (hR : Entry_d M α R G)
      (hD : Entry_d M β D F) (hV : Entry_d M β V G) : Row_pil_d I α B R b D V N := by
    subst β
    have heB := h.1.conditions.2.1.2 α B D hB hD
    have heR := h.1.relations.2.1.2 α R V hR hV
    subst D; subst V
    exact row_pil_id_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.1.stages α B R hB hR)
  let η : Env M 4 := (((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push b).push N
  let ψ : UnarySchema 4 := {
    body := .imp (.mem .newest (.bound 1)) (row_pil_stage_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hψ β : ψ.denote η β ↔ M.mem β N → Row_pil_stage_d I F G b N β := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, row_pil_stage_sat_l I hZFC.1]
    rfl
  intro β hβN α B R D V hαN hαβ hB hR hD hV
  apply (hψ β).mp ?_ hβN α B R D V hαN hαβ hB hR hD hV
  -- 反例集合由实际原公式分离，故这里使用的是模型自身的序数归纳。
  apply (h.1.conditions.1.mem ((h.1.conditions.2.2 β).mpr ⟨D, hD⟩)).induction (fun ξ => ψ.denote η ξ)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ.neg η β
    exact ⟨C, fun ξ => by simpa only [UnarySchema.denote, UnarySchema.neg, Formula.satisfies_neg_iff] using hC ξ⟩
  · intro ξ hξ ih
    apply (hψ ξ).mpr
    intro hξN
    rcases Structure.IsOrdinal.classify hZFC.1 hξ with hz | hs | hl
    · intro α B R D V _ hαξ hB hR hD hV
      exact same (hZFC.1.eq_of_same_members α ξ (fun z => iff_of_false (fun ha => hz z (hαξ z ha)) (hz z))) hB hR hD hV
    · obtain ⟨γ, hγ, hξγ⟩ := hs
      have hγN := selem_predecessor_l I hM.2 (ZF.h_transitive_l I hZF hH) hZF hω hSub hElem hξN hγ hξγ
      have prev := (hψ γ).mp (ih γ hξγ.predecessor_mem) hγN
      intro α B R D V hαN hαξ hB hR hD hV
      have hαδ := (h.1.conditions.2.2 α).mpr ⟨B, hB⟩
      have hξδ := (h.1.conditions.2.2 ξ).mpr ⟨D, hD⟩
      have hγδ := h.1.conditions.1.transitive ξ hξδ γ hξγ.predecessor_mem
      rcases h.1.conditions.1.wellOrder.linear.compare α hαδ ξ hξδ with he | ha | hξα
      · exact same (hZFC.1.eq_of_same_members α ξ he) hB hR hD hV
      · have hαγ : M.MemberSubset α γ := by
          rcases (hξγ α).mp ha with ha | he
          · exact hγ.transitive.memberSubset ha
          · exact fun z hz => (he z).mp hz
        obtain ⟨C, hC⟩ := (h.1.conditions.2.2 γ).mp hγδ
        obtain ⟨T, hT⟩ := (h.1.relations.2.2 γ).mp hγδ
        exact row_pil_comp_l hZF hω hχ.isLimitOrdinal hH hM.2 hSub hElem hγN hαγ
          (h.1.stages α B R hB hR) (h.1.stages γ C T hC hT).order
          (h.1.links α γ B R C T hB hR hC hT hαγ)
          (h.1.links γ ξ C T D V hC hT hD hV (fun z hz => (hξγ z).mpr (Or.inl hz)))
          (prev α B R C T hαN hαγ hB hR hC hT) (next γ ξ C T D V hγN hξγ hC hT hD hV)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ (hαξ ξ hξα)).elim
    · exact row_pr_limit_l hZFC hRule h hN hFN hGN hωN hl hξN
        (fun γ hγN hγξ => (hψ γ).mp (ih γ hγξ) hγN)

/-- 原公式 proper 规则与实际可数支撑迭代，一次返回共同 N 上全部内部区间。 -/
theorem row_iteration_pr_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b A}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ χ H N, Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ M.mem δ N ∧
      ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  obtain ⟨U, χ, H, N, w, v, J, hU, hN, hAN, hωN, hFN, hGN, hδN, _, hUN, _, hLift, _⟩ :=
    row_iteration_pr_prepare_l hZFC hω hRule hPr h ha
  exact ⟨χ, H, N, hN, hAN, hδN, row_pr_induction_l hZFC hRule h hU hN hLift hFN hGN hUN hωN⟩

/-- 同时构造指定内部长度的迭代，并对任意内部可数种子提供完整区间装配。 -/
theorem row_iteration_pr_exists_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ}
    (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ) :
    ∃ b F G, Row_iteration_d I true ω b φ ρ δ F G ∧
      ∀ A, M.CardinalLessOrEqual I A ω → ∃ χ H N,
        Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ M.mem δ N ∧
          ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  obtain ⟨b, hb⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨F, G, h⟩ := row_iteration_l hZF hω hb hRule hδ
  exact ⟨b, F, G, h, fun _ ha => row_iteration_pr_l hZFC hω hRule hPr h ha⟩

end YesMetaZFC.Model.Forcing.Internal
