import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Comparison
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Syntax

/-! # 共尾前缀比较在极限处的还原

每个较短限制由一个更长的共尾前缀控制，故逐前缀比较传给实际融合条件。
若 N 中旧条件的支撑均位于该极限以下，再由原样阶段包含恢复完整旧序比较。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 共尾族的实际融合保留对原商名称的全部限制比较；此保持步骤只需 ZF。 -/
theorem row_cut_fusion_l {δ F H b k ω E T D V α B R N τ p J Q q}
    (h : Row_system_d I δ F H b) (hLim : Row_limit_d I k ω δ F H δ E T)
    (j : Row_link_d I δ E T D V) (l : Row_link_d I α B R E T) (hα : M.mem α δ)
    (hf : Row_fusion_d I δ F J Q) (hq : M.mem q E) (hpq : M.IsRestrictionOf I p q α)
    (hpre : ∀ β t, Entry_d M β t Q → M.IsRestrictionOf I t q β)
    (hc : ∀ β t S, Entry_d M β t Q → Entry_d M β S H → Row_cut_lower_d I α B R b D N τ p β S t) :
    Row_cut_lower_d I α B R b D N τ p δ T q := by
  have bound γ (hγ : M.mem γ δ) : ∃ β, M.mem β J ∧ M.MemberSubset α β ∧ M.MemberSubset γ β := by
    have cmp : M.MemberSubset α γ ∨ M.MemberSubset γ α := by
      rcases h.conditions.1.wellOrder.linear.compare α hα γ hγ with he | he | he
      · exact Or.inl (fun i hi => (he i).mp hi)
      · exact Or.inl ((h.conditions.1.mem hγ).transitive.memberSubset he)
      · exact Or.inr ((h.conditions.1.mem hα).transitive.memberSubset he)
    rcases cmp with hαγ | hγα
    · obtain ⟨β, hβ, hγβ⟩ := hf.cofinal γ hγ
      have hγβ' := (h.conditions.1.mem (hf.subset β hβ)).transitive.memberSubset hγβ
      exact ⟨β, hβ, fun i hi => hγβ' i (hαγ i hi), hγβ'⟩
    · obtain ⟨β, hβ, hαβ⟩ := hf.cofinal α hα
      have hαβ' := (h.conditions.1.mem (hf.subset β hβ)).transitive.memberSubset hαβ
      exact ⟨β, hβ, hαβ', fun i hi => hαβ' i (hγα i hi)⟩
  intro r a v c hr hcp w t hw htr
  have hwE := (l.splice q p c w hq hpq hcp.1 hcp.2.2 hw).1
  obtain ⟨t', ht', ht'r⟩ := j.restrict r hr.1
  have htE : M.mem t E := (htr.eq hZF.1 ht'r).symm ▸ ht'
  have hw' := (hLim.conditions w).mp hwE
  have ht' := (hLim.conditions t).mp htE
  refine (hLim.relation w t).mpr ⟨hwE, htE, fun γ S hS x y hx hy => ?_⟩
  have hγ := (h.relations.2.2 γ).mpr ⟨S, hS⟩
  obtain ⟨β, hβ, hαβ, hγβ⟩ := bound γ hγ
  obtain ⟨q', hq'⟩ := (hf.domain β).mp hβ
  obtain ⟨C, hC, _⟩ := hf.conditions β q' hq'
  obtain ⟨U, hU⟩ := (h.relations.2.2 β).mp (hf.subset β hβ)
  obtain ⟨w', hww⟩ := ZF.exists_restriction hZF I w β
  obtain ⟨r', hr'C, hr't⟩ := ht'.2.2 β C hC
  have hw'C := row_lim_prefix_l I hZF.1 hw' hC hww
  have hcRow := l.rows c hcp.1
  have hsp := row_splice_cut_l hZF.1 hαβ hcRow.graph hcRow.domain hww.1 (hpre β q' hq').2 hww.2 hw
  have hβδ' : M.MemberSubset β δ := h.conditions.1.transitive.memberSubset (hf.subset β hβ)
  have hcmp := hc β q' U hq' hU r a v c hr hcp w' r' hsp (hr't.comp_l htr hβδ')
  obtain ⟨A, hA⟩ := (h.conditions.2.2 γ).mp hγ
  exact (h.links γ β A S C U hA hS hC hU hγβ).mono w' r' x y hw'C hr'C
    (hww.trans hx hγβ) (hr't.trans hy hγβ) hcmp

/-- 旧条件的支撑已受极限所界时，限制比较自动恢复完整实际尾部加强。 -/
theorem row_cut_total_l {α B R b δ E T D V N τ p q}
    (l : Row_link_d I α B R E T) (j : Row_link_d I δ E T D V)
    (hq : M.mem q E) (hpq : M.IsRestrictionOf I p q α)
    (hcut : Row_cut_lower_d I α B R b D N τ p δ T q)
    (hbound : ∀ r, M.mem r D → M.mem r N → Row_d M δ r) :
    Row_quot_lower_d I α B R b D V N τ p q := by
  intro r a v c hr hcp w hw
  have hrow := hbound r hr.1 hr.2.1
  have hrr : M.IsRestrictionOf I r r δ :=
    ⟨hrow.graph, fun i s => ⟨fun his => ⟨hrow.domain i s his, his⟩, And.right⟩⟩
  obtain ⟨r', hr'E, hr'r⟩ := j.restrict r hr.1
  have hrE : M.mem r E := (hr'r.eq hZF.1 hrr) ▸ hr'E
  have hwE := (l.splice q p c w hq hpq hcp.1 hcp.2.2 hw).1
  exact (j.order w r hwE hrE).mpr (hcut r a v c hr hcp w r hw hrr)

end YesMetaZFC.Model.Forcing.Internal
