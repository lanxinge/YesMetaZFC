import YesMetaZFC.Model.Forcing.Iteration.Recursion.Syntax

/-! # 递归算子的全定义性与合法一步保持

后继与自身并两分支互斥；零属于后一分支。合法历史的长度及两张投影图都
唯一，因此原公式算子确为函数式，且其真实输出延长全部早期阶段链接。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
include hZF

omit hZF in
theorem successor_not_union_l {δ α} (hα : M.IsOrdinal α) (hδ : M.SuccessorOf δ α)
    (h : M.IsUnionOf δ δ) : False := by
  obtain ⟨β, hβ, hαβ⟩ := (h α).mp hδ.predecessor_mem
  rcases (hδ β).mp hβ with hβα | hβα
  · have hh := hα.transitive β hβα α hαβ
    exact hα.wellOrder.linear.irrefl α hh hh
  · have hh := (hβα α).mp hαβ
    exact hα.wellOrder.linear.irrefl α hh hh

theorem row_action_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω δ F H e}
    (hω : M.IsOmega ω) (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e) (hSupp : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω F) :
    ∃ D V, Row_action_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ δ F H e D V ∧ Row_extend_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H e D V ∧
      ∀ D' V', Row_action_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ δ F H e D' V' → D' = D ∧ V' = V := by
  classical
  by_cases hs : ∃ α, M.SuccessorOf δ α
  · obtain ⟨D, V, hd, he, hu⟩ := hRule δ F H e h hSupp hs
    refine ⟨D, V, Or.inl ⟨hs, hd⟩, he, fun D' V' h' => ?_⟩
    rcases h' with h' | h'
    · exact hu D' V' h'.2
    · exact False.elim (hs.elim fun _ hα => successor_not_union_l (h.conditions.1.mem hα.predecessor_mem) hα h'.sup)
  · have hδ : M.IsUnionOf δ δ := by
      rcases Structure.IsOrdinal.classify hZF.1 h.conditions.1 with hz | hs' | hl
      · exact fun x => ⟨fun hx => False.elim (hz x hx), fun ⟨y, hy, _⟩ => False.elim (hz y hy)⟩
      · obtain ⟨α, _, hα⟩ := hs'
        exact False.elim (hs ⟨α, hα⟩)
      · exact fun x => ⟨fun hx => hl.2.2 x hx, fun ⟨y, hy, hx⟩ => h.conditions.1.transitive y hy x hx⟩
    obtain ⟨σ, D, V, hSpec, hStage, hLinks⟩ := row_limit_l hZF h hω k hSupp
    have he := hSpec.sup.eq hZF.1 hδ
    subst σ
    refine ⟨D, V, Or.inr hSpec, ⟨hStage, fun α B R hB hR => (hLinks α B R hB hR).1,
      fun p hp => ((hSpec.conditions p).mp hp).2.1⟩, fun D' V' h' => ?_⟩
    rcases h' with h' | h'
    · exact False.elim (hs h'.1)
    · exact (row_limit_unique_l (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) hZF.1 h' hSpec).2

omit hZF in
theorem row_op_decode_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e S c δ F H}
    (h : Row_good_d (kpair_interpretation_l M hE hP) k ω e S δ F H) (hc : Row_op_d (kpair_interpretation_l M hE hP) k ω e φ ρ S c) :
    ∃ D V, Row_action_d (kpair_interpretation_l M hE hP) k ω φ ρ δ F H e D V ∧ KPair_d M c D V := by
  rcases hc with ⟨δ', F', H', D, V, h', ha, hc⟩ | ⟨hn, _⟩
  · have hd := Structure.IsSequenceOfLength.length_eq hE h.1 h'.1
    obtain ⟨hf, hh⟩ := row_history_unique_l hE h.2.1 h'.2.1
    subst δ'; subst F'; subst H'
    exact ⟨D, V, ha, hc⟩
  · exact False.elim (hn ⟨δ, F, H, h⟩)

/-- 对任意集合输入全定义；合法历史给出真正迭代阶段，无效历史只返回空集。 -/
theorem row_op_total_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e}
    (hω : M.IsOmega ω) (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ) (S : M.Domain) :
    ∃ c, Row_op_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ S c ∧ ∀ c', Row_op_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ S c' → c' = c := by
  classical
  by_cases hg : ∃ δ F H, Row_good_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e S δ F H
  · obtain ⟨δ, F, H, hg⟩ := hg
    obtain ⟨D, V, ha, _, hu⟩ := row_action_l hZF hω hRule hg.2.2.1 hg.2.2.2
    obtain ⟨c, hc⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total D V
    refine ⟨c, Or.inl ⟨δ, F, H, D, V, hg, ha, hc⟩, fun c' h' => ?_⟩
    obtain ⟨D', V', ha', hc'⟩ := row_op_decode_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hg h'
    obtain ⟨hd, hv⟩ := hu D' V' ha'
    subst D'; subst V'
    exact kpair_unique_l M hZF.1 hc' hc
  · obtain ⟨c, hc⟩ := KP.exists_empty (ZF.modelsKP hZF)
    refine ⟨c, Or.inr ⟨hg, hc⟩, fun c' h' => ?_⟩
    rcases h' with ⟨δ, F, H, _, _, hh, _⟩ | ⟨_, hc'⟩
    · exact False.elim (hg ⟨δ, F, H, hh⟩)
    · exact hZF.1.eq_of_same_members c' c (fun x => ⟨fun h => False.elim (hc' x h), fun h => False.elim (hc x h)⟩)

/-- 真实递归轨迹上的一步同时返回实际偏序对与全部阶段保持性质。 -/
theorem row_op_extend_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e S c δ F H}
    (hω : M.IsOmega ω) (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (h : Row_good_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e S δ F H) (hc : Row_op_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ S c) :
    ∃ D V, KPair_d M c D V ∧ Row_action_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ δ F H e D V ∧ Row_extend_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H e D V := by
  obtain ⟨D, V, ha, he, hu⟩ := row_action_l hZF hω hRule h.2.2.1 h.2.2.2
  obtain ⟨D', V', ha', hc'⟩ := row_op_decode_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) h hc
  obtain ⟨hd, hv⟩ := hu D' V' ha'
  subst D'; subst V'
  exact ⟨D, V, hc', ha, he⟩

end YesMetaZFC.Model.Forcing.Internal
