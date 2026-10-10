import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Tail
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Basic

/-! # 实际递归序列的融合条件

把零指标之后的全部状态按阶段重编号，在同步截取的实际阶段系统上融合。
返回的条件精确保留原内部序列的每个主前缀，重复阶段不会改变结果。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_fuse_l {ω δ F G b γ F' G' P T D V N A E X Q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b) (hγδ : M.MemberSubset γ δ)
    (hF : M.IsRestrictionOf I F' F γ) (hG : M.IsRestrictionOf I G' G γ)
    (hS : Row_system_supp_d I true ω F)
    (hl : Row_limit_d I true ω γ F' G' γ P T)
    (hc : M.IsCofinalNondecreasingOrdinalSequence I A ω γ)
    (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i j x y, M.SuccessorOf j i → Entry_d M i x Q → Entry_d M j y Q →
      Row_pr_advance_d I F G b D V N A E i x y) :
    ∃ q, M.mem q P ∧ ∀ i x α p τ, Entry_d M i x Q → Entry_d M i α A → KPair_d M x p τ →
      M.IsRestrictionOf I p q α := by
  have part := row_system_restrict_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) h hc.1.1 hγδ hF hG
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  obtain ⟨J, W, hJ, hw, edge⟩ := row_pr_tail_l hZF hω h hc hQ hoω hv hs
  have hw' : Row_fusion_d I γ F' J W := {
    function := hw.function
    domain := hw.domain
    subset := hw.subset
    cofinal := hw.cofinal
    conditions := fun α p hp => by
      obtain ⟨B, hB, hpB⟩ := hw.conditions α p hp
      exact ⟨B, (hF.2 α B).mpr ⟨hw.subset α ((hw.domain α).mpr ⟨p, hp⟩), hB⟩, hpB⟩
    coherent := hw.coherent }
  obtain ⟨q, hq, _, hpre, _⟩ := row_fusion_l hZFC part hω (fun α B hB => hS α B ((hF.2 α B).mp hB).2) hl hw' hJ
  refine ⟨q, hq, fun i x α p τ hx hα hxp => ?_⟩
  have hi := hQ.input_mem_of_pairMember hx
  have he : M.mem o i ∨ o = i := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare o hoω i hi with he | hoi | hio
    · exact Or.inr (hZFC.1.eq_of_same_members o i he)
    · exact Or.inl hoi
    · exact (ho i hio).elim
  exact (hpre α p ((edge α p).mpr ⟨i, x, τ, he, hα, hx, hxp⟩)).1

end YesMetaZFC.Model.Forcing.Internal
