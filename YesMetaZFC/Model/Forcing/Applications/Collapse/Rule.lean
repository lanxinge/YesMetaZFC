import YesMetaZFC.Model.Forcing.Applications.Collapse.RuleSyntax
import YesMetaZFC.Model.Forcing.Iteration.Closed.Rule

/-! # 参数化塌缩规则的存在、唯一性与闭性实例

三个旧参数的规范名称、后继名称三元组和坐标偏序都实际构造。
名称的字面唯一性使该原公式成为确定超限递归的真实规则。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_rule_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) (k : Bool) :
    Row_rule_d I k (ρ.bound 2) coll_rule_s ρ := by
  intro δ F G b h hSupp hSucc
  obtain ⟨α, hδ⟩ := hSucc
  obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hδ.predecessor_mem
  obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp hδ.predecessor_mem
  have hs := h.stages α B R hB hR
  obtain ⟨w, hw, hwN, huw⟩ := zf_check_l M hZF hs.base (ρ.bound 2)
  obtain ⟨x, hx, hxN, hux⟩ := zf_check_l M hZF hs.base (ρ.bound 1)
  obtain ⟨y, hy, hyN, huy⟩ := zf_check_l M hZF hs.base (ρ.bound 0)
  obtain ⟨A, T, t, hn⟩ := collapse_names_l hs.order hZFC hwN hxN hyN
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  obtain ⟨hP, ht, _⟩ := collapse_names_closed_l hs.order hZFC hω hs.base hw (below_refl_l hs.order hs.base hb) hn
  obtain ⟨μ, D, V, _, F', G', _, hNext, hd, _, _, hF, hG, hS⟩ :=
    row_system_successor_l hZF h hδ hB hR hn.1.1 hn.1.2.1 hn.1.2.2 hP ht
  have hDD := (hF δ D).mpr (Or.inr ⟨rfl, rfl⟩)
  have hVV := (hG δ V).mpr (Or.inr ⟨rfl, rfl⟩)
  refine ⟨D, V, (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mpr
    ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, hx, hy, hn, hd⟩,
    ⟨hNext.stages δ D V hDD hVV, ?_, (hS I k (ρ.bound 2) hω hSupp) δ D hDD⟩, ?_⟩
  · intro ξ C S hC hT
    exact hNext.links ξ δ C S D V ((hF ξ C).mpr (Or.inl hC)) ((hG ξ S).mpr (Or.inl hT)) hDD hVV
      (h.conditions.1.transitive.memberSubset ((h.conditions.2.2 ξ).mpr ⟨C, hC⟩))
  · intro D' V' h'
    obtain ⟨α', B', R', hδ', hB', hR', w', x', y', A', T', t', hw', hx', hy', hn', hd'⟩ :=
      (coll_rule_denote_l I hZFC.1 ρ δ F G b D' V').mp h'
    have he := Structure.SuccessorOf.predecessor_eq hZFC.1 (h.conditions.1.mem hδ.predecessor_mem) hδ hδ'
    subst α'
    have heB := h.conditions.2.1.2 α B B' hB hB'
    have heR := h.relations.2.1.2 α R R' hR hR'
    have hew := huw w' hw'
    have hex := hux x' hx'
    have hey := huy y' hy'
    subst B' R' w' x' y'
    obtain ⟨heA, heT, het⟩ := collapse_names_unique_l hs.order hZF hwN hxN hyN hn' hn
    subst A' T' t'
    exact row_next_unique_l M hZFC.1 hd' hd

/-- 同一实际塌缩规则提供闭迭代所需的完整名称证书。 -/
theorem collapse_rule_closed_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) :
    Row_cl_rule_d I (ρ.bound 2) coll_rule_s ρ := by
  intro δ F G b D V h _ hd
  obtain ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, _, _, hn, hNext⟩ :=
    (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mp hd
  have hs := h.stages α B R hB hR
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  have hc := (collapse_names_closed_l hs.order hZFC hω hs.base hw (below_refl_l hs.order hs.base hb) hn).2.2
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, w, hNext, hn.1.2.1, hw, hc⟩

end YesMetaZFC.Model.Forcing.Internal
