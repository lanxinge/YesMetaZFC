import YesMetaZFC.Model.Forcing.Iteration.Closed.Limit
import YesMetaZFC.Model.Forcing.Iteration.Closed.Rule

/-! # 可数支撑闭迭代的内部超限归纳

实际原公式分离反例集。恒等、后继复合和任意极限的整链下界构造给出全部闭区间，
再从零前缀取得各阶段的可数闭性；不要求地模型外部良基或 ω 标准。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_cl_induction_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hCl : Row_cl_rule_d I ω φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) : ∀ β, Row_cl_stage_d I ω F G β := by
  have same {α β B R D V} (he : α = β) (hB : Entry_d M α B F) (hR : Entry_d M α R G)
      (hD : Entry_d M β D F) (hV : Entry_d M β V G) : Row_cl_d I ω α B R D V := by
    subst β
    have heB := h.1.conditions.2.1.2 α B D hB hD
    have heR := h.1.relations.2.1.2 α R V hR hV
    subst D V
    exact row_cl_id_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) (h.1.stages α B R hB hR)
  let η : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push F).push G
  let ψ : UnarySchema 3 := { body := row_cl_stage_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ β : ψ.denote η β ↔ Row_cl_stage_d I ω F G β := row_cl_stage_sat_l I hZFC.1 _ _ _ _ _
  intro β α B R D V hαβ hB hR hD hV
  apply (hψ β).mp ?_ α B R D V hαβ hB hR hD hV
  apply (h.1.conditions.1.mem ((h.1.conditions.2.2 β).mpr ⟨D, hD⟩)).induction (fun ξ => ψ.denote η ξ)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ.neg η β
    exact ⟨C, fun ξ => by simpa only [UnarySchema.denote, UnarySchema.neg, Formula.satisfies_neg_iff] using hC ξ⟩
  · intro ξ hξ ih
    apply (hψ ξ).mpr
    rcases Structure.IsOrdinal.classify hZFC.1 hξ with hz | hs | hl
    · intro α B R D V hαξ hB hR hD hV
      exact same (hZFC.1.eq_of_same_members α ξ (fun x => iff_of_false (fun hx => hz x (hαξ x hx)) (hz x))) hB hR hD hV
    · obtain ⟨γ, hγ, hξγ⟩ := hs
      have prev := (hψ γ).mp (ih γ hξγ.predecessor_mem)
      intro α B R D V hαξ hB hR hD hV
      have hαδ := (h.1.conditions.2.2 α).mpr ⟨B, hB⟩
      have hξδ := (h.1.conditions.2.2 ξ).mpr ⟨D, hD⟩
      have hγδ := h.1.conditions.1.transitive ξ hξδ γ hξγ.predecessor_mem
      rcases h.1.conditions.1.wellOrder.linear.compare α hαδ ξ hξδ with he | ha | hξα
      · exact same (hZFC.1.eq_of_same_members α ξ he) hB hR hD hV
      · have hαγ : M.MemberSubset α γ := by
          rcases (hξγ α).mp ha with ha | he
          · exact hγ.transitive.memberSubset ha
          · exact fun x hx => (he x).mp hx
        obtain ⟨C, hC⟩ := (h.1.conditions.2.2 γ).mp hγδ
        obtain ⟨T, hT⟩ := (h.1.relations.2.2 γ).mp hγδ
        exact row_cl_comp_l hZF hαγ (h.1.links γ ξ C T D V hC hT hD hV (fun x hx => (hξγ x).mpr (Or.inl hx)))
          (prev α B R C T hαγ hB hR hC hT) (row_iteration_cl_next_l hZFC hω hRule hCl h hξγ hC hT hD hV)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ (hαξ ξ hξα)).elim
    · exact row_cl_limit_l hZFC hω hRule h hl (fun γ hγξ => (hψ γ).mp (ih γ hγξ))

/-- 真实可数闭名称规则的任意内部长度可数支撑迭代，全部阶段均可数闭。 -/
theorem row_iteration_closed_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hCl : Row_cl_rule_d I ω φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) :
    ∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω := by
  have all := row_cl_induction_l hZFC hω hRule hCl h
  intro β D V hD hV f hf
  have hβδ := (h.1.conditions.2.2 β).mpr ⟨D, hD⟩
  have hbδ := h.1.conditions.1.empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨β, hβδ⟩ h.1.empty
  obtain ⟨B, hB⟩ := (h.1.conditions.2.2 b).mp hbδ
  obtain ⟨R, hR⟩ := (h.1.relations.2.2 b).mp hbδ
  have stage := h.1.stages b B R hB hR
  obtain ⟨q, hq, _, hqf⟩ := all β b B R D V (fun x hx => (h.1.empty x hx).elim) hB hR hD hV f b hf stage.base (by
    intro i r a _ har
    have ha : ∀ v, ¬ M.mem v a := by
      intro v hv
      obtain ⟨x, y, hxy⟩ := har.1 v hv
      exact h.1.empty x ((har.2 x y).mp ⟨v, hxy, hv⟩).1
    have he := hZFC.1.eq_of_same_members a b (fun v => iff_of_false (ha v) (h.1.empty v))
    exact he.symm ▸ stage.order.refl b stage.base)
  exact ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hq), hqf⟩

/-- 同时构造整个可数闭迭代及全部闭区间，调用者只需给出已实现的原公式规则。 -/
theorem row_iteration_closed_exists_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ}
    (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) (hRule : Row_rule_d I true ω φ ρ) (hCl : Row_cl_rule_d I ω φ ρ) :
    ∃ b F G, Row_iteration_d I true ω b φ ρ δ F G ∧
      (∀ β, Row_cl_stage_d I ω F G β) ∧ ∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω := by
  obtain ⟨b, hb⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨F, G, h⟩ := row_iteration_l hZF hω hb hRule hδ
  exact ⟨b, F, G, h, row_cl_induction_l hZFC hω hRule hCl h, row_iteration_closed_l hZFC hω hRule hCl h⟩

end YesMetaZFC.Model.Forcing.Internal
