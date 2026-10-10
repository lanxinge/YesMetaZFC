import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Realization

/-! # 实际融合条件的主性

任意 N 内稠密集出现在内部枚举中。决定相应选择名称后，完整尾部比较给出
与该稠密集内 N 条件的共同加强；规范拼接的最大下界性质保持任意给定加强。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

section
variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_master_l {k ω δ F G b β D V γ P T F' G' N A E X Q q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G) (hP : Entry_d M γ P F) (hT : Entry_d M γ T G)
    (hγβ : M.MemberSubset γ β) (hF : M.IsRestrictionOf I F' F γ) (hG : M.IsRestrictionOf I G' G γ)
    (hl : Row_limit_d I k ω γ F' G' γ P T)
    (hc : M.IsCofinalNondecreasingOrdinalSequence I A ω γ) (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i j x y, M.SuccessorOf j i → Entry_d M i x Q → Entry_d M j y Q →
      Row_pr_advance_d I F G b D V N A E i x y)
    (hE : M.IsSetFunction I E)
    (he : ∀ U, M.mem U N → Dense_set_d M D V D U → ∃ i, M.mem i ω ∧ Entry_d M i U E)
    (hbound : ∀ r, M.mem r D → M.mem r N → Row_d M γ r)
    (hq : M.mem q P)
    (hpre : ∀ i x ξ r σ, Entry_d M i x Q → Entry_d M i ξ A → KPair_d M x r σ → M.IsRestrictionOf I r q ξ) :
    Mstr_d M D V D N q := by
  have s := h.stages β D V hD hV
  have link := h.links γ β P T D V hP hT hD hV hγβ
  have hqD := link.mem q hq
  have nz {r} (hr : M.mem r D) : r ≠ D := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hr)
  refine ⟨hqD, nz hqD, fun U hUN hUD r hr => ?_⟩
  obtain ⟨i, hi, hiU⟩ := he U hUN hUD
  obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
  obtain ⟨x, _, hx⟩ := hQ.2.2 i hi
  obtain ⟨y, _, hy⟩ := hQ.2.2 j hjω
  obtain ⟨j', α, B, R, ξ, C, S, U', hj', hiα, hjξ, hB, hR, hC, hSS, hiU', hmove⟩ := hs i j x y hj hx hy
  have hej := hZF.1.eq_of_same_members j' j (fun z => (hj' z).trans (hj z).symm)
  subst j'
  have heU := hE.2 i U' U hiU' hiU
  subst U'
  obtain ⟨p, τ, p', σ, K, ν, ζ, _, hyσ, hpp', hσ, hK, _, hζ, hσK, hσζ, _, hLow⟩ := hmove
  have hα := hc.value_mem hi hiα
  have hαξ : M.MemberSubset α ξ := by
    rcases hc.isNondecreasing.2 i hi j hjω hj.predecessor_mem α ξ hiα hjξ with he | hlt
    · exact he ▸ (fun _ h => h)
    · exact (hc.1.1.mem (hc.value_mem hjω hjξ)).transitive.memberSubset hlt
  obtain ⟨hpq, lower⟩ := row_pr_total_l hZF hω h hD hV hP hT hγβ hF hG hl hc hQ hv hs hq hpre hbound
    hα hB hR hσ hy hjξ hSS hyσ hαξ hpp' hLow
  have a := h.stages α B R hB hR
  have k := h.links α β B R D V hB hR hD hV (fun z hz => hγβ z (hc.1.1.transitive α hα z hz))
  -- 在给定加强的原前缀之下决定稠密名称，反射得到同一个 N 中的真实稠密条件。
  obtain ⟨v, hvB, hvr⟩ := k.restrict r hr.1
  have hvp : Below_d M B R B v p := ⟨hvB,
    (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hvB)), k.mono r q v p hr.1 hqD hvr hpq hr.2.2⟩
  obtain ⟨c, hcv, u, v', ρ, hDec⟩ := row_quot_decide_l hK hσK v hvp
  have hcp := below_trans_l a.order hσK.1 hcv hvp
  have hDec' := hDec
  obtain ⟨huD, huN, _, _, huρ, _, hσρ⟩ := hDec'
  have hρn := check_name_l M (check_range_l M hZF) a.base huρ
  have hζn := check_name_l M (check_range_l M hZF) a.base hζ
  have hρζ := mem_force_left_l a.order hZF hσ hρn hζn hσρ
    ((regular_mem_l a.order σ ζ).1 p c hσK.1 hcp hσζ)
  have huU := check_mem_reflect_l a.order hZF a.base huρ hζ ⟨hcp.1, hcp.2.1, a.top c hcp.1⟩ hρζ
  -- 同一决定前缀分别拼入原加强与融合；最大下界性质把后者的尾部比较传给前者。
  obtain ⟨w, hw⟩ := row_splice_exists_l M hZF α c r
  obtain ⟨w', hw'⟩ := row_splice_exists_l M hZF α c q
  obtain ⟨hwD, hwr, hwc⟩ := k.splice r v c w hr.1 hvr hcv.1 hcv.2.2 hw
  have hw'D := (k.splice q p c w' hqD hpq hcp.1 hcp.2.2 hw').1
  have hww' := k.splice_glb q p c w' w hqD hpq hcp.1 hcp.2.2 hw' hwD
    (s.order.trans w r q hwD hr.1 hqD hwr hr.2.2) hwc
  exact ⟨u, huU, huN, w, ⟨hwD, nz hwD, hwr⟩,
    s.order.trans w w' u hwD hw'D huD hww' (lower u v' ρ c hDec hcp w' hw')⟩

end

section
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 从实际递归图直接构造主融合；精确保留每个内部阶段的前缀。 -/
theorem row_pr_master_fusion_l {ω δ F G b β D V γ P T F' G' N A E X Q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G) (hP : Entry_d M γ P F) (hT : Entry_d M γ T G)
    (hγβ : M.MemberSubset γ β) (hF : M.IsRestrictionOf I F' F γ) (hG : M.IsRestrictionOf I G' G γ)
    (hS : Row_system_supp_d I true ω F) (hl : Row_limit_d I true ω γ F' G' γ P T)
    (hc : M.IsCofinalNondecreasingOrdinalSequence I A ω γ) (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i j x y, M.SuccessorOf j i → Entry_d M i x Q → Entry_d M j y Q →
      Row_pr_advance_d I F G b D V N A E i x y)
    (hE : M.IsSetFunction I E)
    (he : ∀ U, M.mem U N → Dense_set_d M D V D U → ∃ i, M.mem i ω ∧ Entry_d M i U E)
    (hbound : ∀ r, M.mem r D → M.mem r N → Row_d M γ r) :
    ∃ q, M.mem q P ∧ Mstr_d M D V D N q ∧
      ∀ i x ξ r σ, Entry_d M i x Q → Entry_d M i ξ A → KPair_d M x r σ → M.IsRestrictionOf I r q ξ := by
  have hγδ := h.conditions.1.transitive.memberSubset ((h.conditions.2.2 γ).mpr ⟨P, hP⟩)
  obtain ⟨q, hq, hpre⟩ := row_pr_fuse_l hZFC hω h hγδ hF hG hS hl hc hQ hv hs
  exact ⟨q, hq, row_pr_master_l hZF hω h hD hV hP hT hγβ hF hG hl hc hQ hv hs hE he hbound hq hpre, hpre⟩

end
end YesMetaZFC.Model.Forcing.Internal
