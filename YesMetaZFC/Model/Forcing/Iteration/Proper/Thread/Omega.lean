import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Limit
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Basic
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Sequence

/-! # 首个内部极限的自动主前缀序列

共同模型及实际 proper 后继图自动给出全部内部有限区间。对任意原主前缀与
商名称，构造共尾指标、稠密枚举及变动前缀序列；初值也由实际投影构造。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 完全消费现有 proper 后继实例，不要求调用者预给有限区间或递归状态。 -/
theorem row_pr_omega_thread_l {ω δ F G b U χ H N w v α B R D V p τ K}
    (h : Row_system_d I δ F G b) (hU : Row_pr_family_d I δ F G b U)
    (hN : Hsub_d I ω χ H N) (hLift : Hlift_d M ω δ F G b χ H N w v)
    (hFN : M.mem F N) (hGN : M.mem G N) (hUN : M.mem U N) (hωN : M.mem ω N)
    (hD : Entry_d M ω D F) (hV : Entry_d M ω V G)
    (hαω : M.mem α ω) (hB : Entry_d M α B F) (hR : Entry_d M α R G)
    (hK : Row_quot_d I α B b D N K) (hτ : Name_d M B τ)
    (hτK : Mem_force_d M B R B p τ K) (hp : Mstr_d M B R B N p) :
    ∃ A E X Q x p₀ α₀ B₀ R₀,
      M.IsSetFunctionFromTo I A ω ω ∧ M.IsCofinalNondecreasingOrdinalSequence I A ω ω ∧
      (∀ i ξ, Entry_d M i ξ A → M.mem α ξ) ∧ M.IsSetFunctionFromTo I E ω N ∧
      (∀ i T, Entry_d M i T E → Dense_set_d M D V D T) ∧
      (∀ T, M.mem T N → Dense_set_d M D V D T → ∃ i, M.mem i ω ∧ Entry_d M i T E) ∧
      M.IsSetFunctionFromTo I Q ω X ∧ Entry_d M b x Q ∧
      Entry_d M b α₀ A ∧ Entry_d M α₀ B₀ F ∧ Entry_d M α₀ R₀ G ∧ KPair_d M x p₀ τ ∧
      M.IsRestrictionOf I p p₀ α ∧ Row_cut_lower_d I α B R b D N τ p α₀ R₀ p₀ ∧
      (∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y) ∧
      (∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
        Row_pr_advance_d I F G b D V N A E i y z) ∧
      (∀ i j x y ξ ζ r η s θ, Entry_d M i x Q → Entry_d M j y Q →
        Entry_d M i ξ A → Entry_d M j ζ A → KPair_d M x r η → KPair_d M y s θ →
        M.MemberSubset ξ ζ → M.IsRestrictionOf I r s ξ) ∧ Row_pr_bounds_d I F G b D N A Q ∧
      ∀ i y γ C T q σ, Entry_d M i y Q → Entry_d M i γ A →
        Entry_d M γ C F → Entry_d M γ T G → KPair_d M y q σ → Row_cut_lower_d I α B R b D N τ p γ T q := by
  have hStep := row_pr_family_pil_l hZFC h hU hN hLift hFN hGN hUN
  have hN' := hN
  obtain ⟨hω, hχ, _, hH, _, c, J, d, S, hM, hSub, hElem⟩ := hN'
  have hNat := row_pil_nat_l hZF hω hχ.isLimitOrdinal hH hM.2 hSub hElem hωN h hStep
  have hωsub := selem_omega_subset_l I hM.2 (ZF.h_transitive_l I hZF hH) hZF hω hSub hElem hωN
  obtain ⟨γ, A, E, X, Q, x, p₀, α₀, B₀, R₀, hγω, hNγ, hA, hc, ha, hE, hd, he, hQ,
    hx, hα₀, hB₀, hR₀, hxp₀, hpp₀, hLow, hv, hs, hcoh, hbs, hOrig, _⟩ :=
      row_pr_limit_thread_l hZFC h hN hFN hGN hωN (hω.isLimitOrdinal hZF) hωN
        (fun ξ _ hξ => hNat ξ hξ) hD hV hαω (hωsub α hαω) hB hR hK hτ hτK hp
  have heγ := hZFC.1.eq_of_same_members γ ω (fun ξ => ⟨hγω ξ, fun hξ => hNγ ξ (hωsub ξ hξ) hξ⟩)
  subst γ
  exact ⟨A, E, X, Q, x, p₀, α₀, B₀, R₀, hA, hc, ha, hE, hd, he, hQ, hx, hα₀, hB₀, hR₀, hxp₀, hpp₀,
    hLow, hv, hs, hcoh, hbs, hOrig⟩

end YesMetaZFC.Model.Forcing.Internal
