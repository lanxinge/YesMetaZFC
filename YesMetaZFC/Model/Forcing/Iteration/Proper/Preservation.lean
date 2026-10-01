import YesMetaZFC.Model.Forcing.Iteration.Proper.Induction
import YesMetaZFC.Model.Forcing.Iteration.Proper.Ground
import YesMetaZFC.Model.Forcing.Proper.Family.Trace
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # 任意内部长度的可数支撑 proper 保持

在任意包含条件域的 X 上，固定三张真实闭包运算，构造交集 club。
每个成员的同一初等模型见证支持完整区间迭代引理；从零前缀得到主加强，
再按交集等式回到原 club 成员。这直接证明 Proper_d 的全部量词。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_iteration_proper_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) :
    ∀ β D V, Entry_d M β D F → Entry_d M β V G → Proper_d I ω D V D := by
  obtain ⟨U, hU⟩ := row_iteration_pr_family_l hZFC hω hRule hPr h
  intro β D V hD hV X hDX
  let t : Fin 7 → M.Domain := Fin.cases F (Fin.cases G (Fin.cases U (Fin.cases ω (Fin.cases b (Fin.cases β (fun _ => X))))))
  obtain ⟨A, ha, hA⟩ := ZF.finite_params_l I hZF hω t
  have memA i : M.mem (t i) A := (hA _).mpr ⟨i, rfl⟩
  obtain ⟨χ, H, hχ, hωχ, hH, hAH⟩ := ZFC.h_cover_l I hZFC hω A
  have htr := ZF.h_transitive_l I hZF hH
  have hA' := htr A hAH
  have bounds i B (_ : M.mem i δ) (hiB : Entry_d M i B F) := (trans_entry_l htr (hA' F (memA 0)) hiB).2
  obtain ⟨C, w, v, hC, hc⟩ := ng_trace_forcing_l (δ := δ) (b := b) hZFC hω hχ hωχ hH
    h.1.conditions.2.1 h.1.relations.2.1 bounds hA' (ZF.finite_countable_l I hZF hω ha) (htr X (hA' X (memA 6)))
  refine ⟨C, hC, fun Y hY p hpY hp _ => ?_⟩
  obtain ⟨N, hN, hAN, he, hLift⟩ := hc Y hY
  have memN i : M.mem (t i) N := hAN _ (memA i)
  have pil := row_pr_induction_l hZFC hRule h hU hN hLift (memN 0) (memN 1) (memN 2) (memN 3) β (memN 5)
  have hβδ := (h.1.conditions.2.2 β).mpr ⟨D, hD⟩
  have hbδ := h.1.conditions.1.empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨β, hβδ⟩ h.1.empty
  obtain ⟨B, hB⟩ := (h.1.conditions.2.2 b).mp hbδ
  obtain ⟨R, hR⟩ := (h.1.relations.2.2 b).mp hbδ
  have hP := pil b B R D V (memN 4) (fun x hx => (h.1.empty x hx).elim) hB hR hD hV
  obtain ⟨q, hqp, hqm⟩ := row_pil_ground_l hZF h.1.empty (memN 4) (h.1.stages b B R hB hR)
    (fun q hq => (h.1.stages β D V hD hV).rows q hq |>.graph) hP hp ((he p).mp hpY).1
  exact ⟨q, hqp, mstr_trace_l hDX he hqm⟩

/-- 指定内部长度及实际 proper 原公式规则后，一次构造整个 proper 迭代。 -/
theorem row_iteration_proper_exists_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ}
    (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ) :
    ∃ b F G, Row_iteration_d I true ω b φ ρ δ F G ∧
      ∀ β D V, Entry_d M β D F → Entry_d M β V G → Proper_d I ω D V D := by
  obtain ⟨b, hb⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨F, G, h⟩ := row_iteration_l hZF hω hb hRule hδ
  exact ⟨b, F, G, h, row_iteration_proper_l hZFC hω hRule hPr h⟩

end YesMetaZFC.Model.Forcing.Internal
