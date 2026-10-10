import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Limit
import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Master
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Basic

/-! # 任意内部极限的完整 proper 区间步骤

在 γ=sup(N∩β) 处读取原迭代的真实支撑极限，融合实际递归序列，再利用 N 中
旧条件的支撑界恢复 β 阶段的主性与完整尾部加强。较短区间由内部归纳假设供给。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_limit_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b β χ H N}
    (hRule : Row_rule_d I true ω φ ρ) (h : Row_iteration_d I true ω b φ ρ δ F G)
    (hN : Hsub_d I ω χ H N) (hFN : M.mem F N) (hGN : M.mem G N) (hωN : M.mem ω N)
    (hβ : M.IsLimitOrdinal β) (hβN : M.mem β N)
    (hPast : ∀ ξ, M.mem ξ N → M.mem ξ β → Row_pil_stage_d I F G b N ξ) :
    Row_pil_stage_d I F G b N β := by
  classical
  have hω := hN.1
  intro α B R D V hαN hαβ hB hR hD hV
  have hαδ := (h.1.conditions.2.2 α).mpr ⟨B, hB⟩
  have hβδ := (h.1.conditions.2.2 β).mpr ⟨D, hD⟩
  rcases h.1.conditions.1.wellOrder.linear.compare α hαδ β hβδ with he | hα | hβα
  · have he := hZFC.1.eq_of_same_members α β he
    subst α
    have heB := h.1.conditions.2.1.2 β B D hB hD
    have heR := h.1.relations.2.1.2 β R V hR hV
    subst B; subst R
    exact row_pil_id_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.1.stages β D V hD hV)
  · intro τ p K hK hτ hτK hp
    obtain ⟨γ, A, E, X, Q, x, p₀, α₀, B₀, R₀, hγβ, hNγ, hA, hc, ha, hE, _, he, hQ, hx,
      hα₀, _, hR₀, hxp₀, hpp₀, hLow, hv, hs, _, _, _, hbound⟩ :=
      row_pr_limit_thread_l hZFC h.1 hN hFN hGN hωN hβ hβN hPast hD hV hα hαN hB hR hK hτ hτK hp
    have hγδ : M.mem γ δ := by
      by_cases he : γ = β
      · exact he.symm ▸ hβδ
      · have hγβ' := Structure.IsOrdinal.mem_of_properSubset hZFC.1 hc.1.1 hβ.1
          ⟨hγβ, fun hh => he (hZFC.1.eq_of_same_members γ β hh)⟩ (KP.difference_exists_d (ZF.modelsKP hZF) γ β)
        exact h.1.conditions.1.transitive β hβδ γ hγβ'
    obtain ⟨P, hP⟩ := (h.1.conditions.2.2 γ).mp hγδ
    obtain ⟨T, hT⟩ := (h.1.relations.2.2 γ).mp hγδ
    obtain ⟨F', G', hF, hG, _, hl⟩ := row_iteration_limit_l hZF hω hRule h hc.1 hP hT
    have bound r (hr : M.mem r D) (hrN : M.mem r N) : Row_d M γ r :=
      hbound r hrN ((h.1.stages β D V hD hV).rows r hr) (h.2.1 β D hD r hr)
    obtain ⟨q, hq, hqm, hpre⟩ := row_pr_master_fusion_l hZFC hω h.1 hD hV hP hT hγβ
      hF hG h.2.1 hl hc hQ hv hs hE.1 he bound
    have hαα₀ := (hc.1.1.mem (hA.output_mem_of_pairMember hα₀)).transitive.memberSubset (ha b α₀ hα₀)
    obtain ⟨hpq, lower⟩ := row_pr_total_l hZF hω h.1 hD hV hP hT hγβ hF hG hl hc hQ hv hs hq hpre bound
      (hNγ α hαN hα) hB hR hτ hx hα₀ hR₀ hxp₀ hαα₀ hpp₀ hLow
    exact ⟨q, hqm.1, hpq, hqm, lower⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) β (hαβ β hβα)).elim

end YesMetaZFC.Model.Forcing.Internal
