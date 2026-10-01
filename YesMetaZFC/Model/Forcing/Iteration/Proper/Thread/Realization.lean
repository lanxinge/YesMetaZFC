import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Fusion
import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Limit

/-! # 实际融合对任意早期名称的完整尾部加强

截取该名称出现之后的真实共尾尾段，应用已证明的整列比较，再把极限限制比较
恢复为旧偏序中的字面加强。旧 N 条件的支撑界由内部模型序列装配提供。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_total_l {k ω δ F G b β D V γ P T F' G' N A E X Q q α B R τ p j x₀ γ₀ R₀ p₀}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G) (hP : Entry_d M γ P F) (hT : Entry_d M γ T G)
    (hγβ : M.MemberSubset γ β) (hF : M.IsRestrictionOf I F' F γ) (hG : M.IsRestrictionOf I G' G γ)
    (hl : Row_limit_d I k ω γ F' G' γ P T)
    (hc : M.IsCofinalNondecreasingOrdinalSequence I A ω γ) (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i k x y, M.SuccessorOf k i → Entry_d M i x Q → Entry_d M k y Q →
      Row_pr_advance_d I F G b D V N A E i x y)
    (hq : M.mem q P)
    (hpre : ∀ i x ξ r σ, Entry_d M i x Q → Entry_d M i ξ A → KPair_d M x r σ → M.IsRestrictionOf I r q ξ)
    (hbound : ∀ r, M.mem r D → M.mem r N → Row_d M γ r)
    (hα : M.mem α γ) (hB : Entry_d M α B F) (hR : Entry_d M α R G) (hτ : Name_d M B τ)
    (hx₀ : Entry_d M j x₀ Q) (hγ₀ : Entry_d M j γ₀ A) (hR₀ : Entry_d M γ₀ R₀ G) (hxτ : KPair_d M x₀ p₀ τ)
    (hαγ : M.MemberSubset α γ₀) (hpp₀ : M.IsRestrictionOf I p p₀ α)
    (h₀ : Row_cut_lower_d I α B R b D N τ p γ₀ R₀ p₀) :
    M.IsRestrictionOf I p q α ∧ Row_quot_lower_d I α B R b D V N τ p q := by
  have hA := hc.isSetFunctionFromTo
  have inc : Cc_increasing_d I A := by
    intro i k ξ ζ hik hi hk
    rcases hc.isNondecreasing.2 i (hA.input_mem_of_pairMember hi) k (hA.input_mem_of_pairMember hk) hik ξ ζ hi hk with he | hlt
    · exact he ▸ (fun _ h => h)
    · exact (hc.1.1.mem (hA.output_mem_of_pairMember hk)).transitive.memberSubset hlt
  have idx i ξ (hi : Entry_d M i ξ A) : M.MemberSubset ξ β :=
    fun z hz => hγβ z (hc.1.1.transitive ξ (hA.output_mem_of_pairMember hi) z hz)
  have low := row_pr_bound_l hZF hω h hD hV hA inc idx hQ hv hs hB hR hτ hx₀ hγ₀ hR₀ hxτ hαγ hpp₀ h₀
  have hγδ := h.conditions.1.transitive.memberSubset ((h.conditions.2.2 γ).mpr ⟨P, hP⟩)
  have part := row_system_restrict_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) h hc.1.1 hγδ hF hG
  have l := h.links α γ B R P T hB hR hP hT (hc.1.1.transitive.memberSubset hα)
  have v := h.links γ β P T D V hP hT hD hV hγβ
  have hpq := hpp₀.comp_l (hpre j x₀ γ₀ p₀ τ hx₀ hγ₀ hxτ) hαγ
  obtain ⟨J, W, _, hw, edge⟩ := row_pr_tail_l hZF hω h hc hQ (hQ.input_mem_of_pairMember hx₀) hv hs
  have hw' : Row_fusion_d I γ F' J W := ⟨hw.function, hw.domain, hw.subset, hw.cofinal, fun ξ r hr => by
    obtain ⟨B, hB, hrB⟩ := hw.conditions ξ r hr
    exact ⟨B, (hF.2 ξ B).mpr ⟨hw.subset ξ ((hw.domain ξ).mpr ⟨r, hr⟩), hB⟩, hrB⟩, hw.coherent⟩
  have final := row_cut_fusion_l hZF part hl v l hα hw' hq hpq (fun ξ r hr => by
    obtain ⟨i, x, σ, _, hi, hx, hr⟩ := (edge ξ r).mp hr
    exact hpre i x ξ r σ hx hi hr) (by
      intro ξ r S hr hSS
      obtain ⟨i, x, σ, hji, hi, hx, hxr⟩ := (edge ξ r).mp hr
      obtain ⟨B, hB, _⟩ := hw.conditions ξ r hr
      exact low i x ξ B S r σ hji hx hi hB ((hG.2 ξ S).mp hSS).2 hxr)
  exact ⟨hpq, row_cut_total_l hZF l v hq hpq final hbound⟩

end YesMetaZFC.Model.Forcing.Internal
