import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Omega
import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Master
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Rule

/-! # 首个内部极限的完整 proper 区间迭代引理

实际 proper 后继与共同 N 给出全部内部有限区间；模型内递归、共尾融合和主性
证明随即完成 ω 终点的全部区间。自动规则入口只消费已构造的可数支撑迭代。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_omega_l {ω δ F G b U χ H N w v D V F' G'}
    (h : Row_system_d I δ F G b) (hU : Row_pr_family_d I δ F G b U)
    (hN : Hsub_d I ω χ H N) (hLift : Hlift_d M ω δ F G b χ H N w v)
    (hFN : M.mem F N) (hGN : M.mem G N) (hUN : M.mem U N) (hωN : M.mem ω N)
    (hD : Entry_d M ω D F) (hV : Entry_d M ω V G)
    (hF : M.IsRestrictionOf I F' F ω) (hG : M.IsRestrictionOf I G' G ω)
    (hS : Row_system_supp_d I true ω F) (hl : Row_limit_d I true ω ω F' G' ω D V) :
    Row_pil_stage_d I F G b N ω := by
  have hω := hN.1
  intro α B R D' V' _ hαω hB hR hD' hV'
  have heD := h.conditions.2.1.2 ω D' D hD' hD
  have heV := h.relations.2.1.2 ω V' V hV' hV
  subst D'; subst V'
  have hαδ := (h.conditions.2.2 α).mpr ⟨B, hB⟩
  have hωδ := (h.conditions.2.2 ω).mpr ⟨D, hD⟩
  rcases h.conditions.1.wellOrder.linear.compare α hαδ ω hωδ with he | hα | hωα
  · have he := hZFC.1.eq_of_same_members α ω he
    subst α
    have heB := h.conditions.2.1.2 ω B D hB hD
    have heR := h.relations.2.1.2 ω R V hR hV
    subst B; subst R
    exact row_pil_id_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.stages ω D V hD hV)
  · intro τ p K hK hτ hτK hp
    obtain ⟨A, E, X, Q, x, p₀, α₀, B₀, R₀, hA, hc, ha, hE, _, he, hQ, hx, hα₀, _, hR₀, hxp₀, hpp₀, hLow, hv, hs, _⟩ :=
      row_pr_omega_thread_l hZFC h hU hN hLift hFN hGN hUN hωN hD hV hα hB hR hK hτ hτK hp
    have bound r (hr : M.mem r D) (_ : M.mem r N) : Row_d M ω r := (h.stages ω D V hD hV).rows r hr
    obtain ⟨q, hq, hqm, hpre⟩ := row_pr_master_fusion_l hZFC hω h hD hV hD hV (fun _ h => h)
      hF hG hS hl hc hQ hv hs hE.1 he bound
    have hαα₀ := ((hω.isOrdinal hZF).mem (hA.output_mem_of_pairMember hα₀)).transitive.memberSubset (ha b α₀ hα₀)
    obtain ⟨hpq, lower⟩ := row_pr_total_l hZF hω h hD hV hD hV (fun _ h => h)
      hF hG hl hc hQ hv hs hq hpre bound hα hB hR hτ hx hα₀ hR₀ hxp₀ hαα₀ hpp₀ hLow
    exact ⟨q, hq, hpq, hqm, lower⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (hαω ω hωα)).elim

/-- 从原公式 proper 规则、实际可数支撑迭代与种子，自动取得 ω 终点的完整区间结论。 -/
theorem row_iteration_pr_omega_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b A}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) (hωδ : M.mem ω δ) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ χ H N, Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ Row_pil_stage_d I F G b N ω := by
  obtain ⟨D, hD⟩ := (h.1.conditions.2.2 ω).mp hωδ
  obtain ⟨V, hV⟩ := (h.1.relations.2.2 ω).mp hωδ
  obtain ⟨U, χ, H, N, w, v, J, hU, hN, hAN, hωN, hFN, hGN, _, _, hUN, _, hLift, _⟩ :=
    row_iteration_pr_prepare_l hZFC hω hRule hPr h ha
  obtain ⟨F', G', hF, hG, _, hl⟩ := row_iteration_limit_l hZF hω hRule h (hω.isLimitOrdinal hZF) hD hV
  exact ⟨χ, H, N, hN, hAN, row_pr_omega_l hZFC h.1 hU hN hLift hFN hGN hUN hωN hD hV hF hG h.2.1 hl⟩

end YesMetaZFC.Model.Forcing.Internal
