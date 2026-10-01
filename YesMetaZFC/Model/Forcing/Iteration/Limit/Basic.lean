import YesMetaZFC.Model.Forcing.Iteration.Limit.Projection
import YesMetaZFC.Model.Forcing.Iteration.Stage.Embedding

/-! # 支撑极限与全部阶段完全嵌入的一键入口

自动构造坐标上确界、极限条件集与关系。任一旧阶段同时取得原样完全嵌入、
实际限制投影及保留尾部的前缀加强；所有结果来自既有模型内阶段序列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 两种支撑共用一个实际极限构造；旧阶段的完全嵌入图均可自动取得。 -/
theorem row_limit_l (hZF : M.Models ZF) {δ F H e ω}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω) (k : Bool)
    (hSupp : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω F) :
    ∃ σ D V, Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H σ D V ∧
      Row_stage_d M σ D V e ∧
      ∀ α B R, Entry_d M α B F → Entry_d M α R H →
        Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V ∧
        ∃ G, (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧ Reg_embed_d M B R B D V D G := by
  obtain ⟨σ, hσ⟩ := KP.exists_union (ZF.modelsKP hZF) δ
  obtain ⟨D, V, hSpec, hs⟩ := row_lim_order_l hZF h hω hσ k
  refine ⟨σ, D, V, hSpec, hs, fun α B R hB hR => ?_⟩
  have hLink := row_lim_link_l hZF h hω hSpec hB hR (hSupp α B hB)
  exact ⟨hLink, row_link_embed_l hZF hLink⟩

/-- 在坐标域等于自身上确界处，把实际支撑极限写回内部序列，供继续作名称后继。 -/
theorem row_system_limit_l (hZF : M.Models ZF) {δ F H e ω}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hδ : M.IsUnionOf δ δ) (hω : M.IsOmega ω) (k : Bool)
    (hSupp : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω F) :
    ∃ μ D V F' H', M.SuccessorOf μ δ ∧
      Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) μ F' H' e ∧
      Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H δ D V ∧
      (∀ i p, Entry_d M i p F' ↔ Entry_d M i p F ∨ (i = δ ∧ p = D)) ∧
      (∀ i p, Entry_d M i p H' ↔ Entry_d M i p H ∨ (i = δ ∧ p = V)) ∧
      Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω F' := by
  obtain ⟨σ, D, V, hSpec, hs, hLinks⟩ := row_limit_l hZF h hω k hSupp
  have he := hSpec.sup.eq hZF.1 hδ
  subst σ
  obtain ⟨μ, hμ⟩ := KP.exists_successor (ZF.modelsKP hZF) δ
  obtain ⟨F', H', hSys, hF, hH, hS⟩ := row_system_extend_l (ZF.modelsKP hZF) h hμ hs (fun α B R hB hR => (hLinks α B R hB hR).1)
  exact ⟨μ, D, V, F', H', hμ, hSys, hSpec, hF, hH,
    hS _ k ω hSupp (fun p hp => ((hSpec.conditions p).mp hp).2.1)⟩

/-- 从空阶段序列调用统一极限构造，得到长度一的零系统，而非另设初始装配路线。 -/
theorem row_system_zero_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) : ∃ e δ F H,
    M.SuccessorOf δ e ∧ Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω → Row_system_supp_d I k ω F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨e, h⟩ := row_system_empty_l M (ZF.modelsKP hZF)
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  have hu : M.IsUnionOf e e := fun i => ⟨fun hi => False.elim (h.empty i hi),
    fun ⟨j, hj, _⟩ => False.elim (h.empty j hj)⟩
  have heS : Row_system_supp_d I false ω e := by
    intro α B hB
    exact False.elim (hB.elim fun v hv => h.empty v hv.2)
  obtain ⟨δ, D, _, F, H, hδ, hs, hSpec, hF, _, _⟩ := row_system_limit_l hZF h hu hω false heS
  have collapse p (hp : M.mem p D) : p = e := by
    have hp' := ((hSpec.conditions p).mp hp).1
    exact row_ext_l hZF.1 hp' (row_empty_l M (α := e) h.empty) (fun i s =>
      ⟨fun hh => False.elim (h.empty i (hp'.domain i s hh)),
        fun ⟨v, _, hv⟩ => False.elim (h.empty v hv)⟩)
  refine ⟨e, δ, F, H, hδ, hs, ?_⟩
  intro 𝒞 J k ν hν α B hB p hp
  rcases (hF α B).mp hB with hB | ⟨_, he⟩
  · exact False.elim (hB.elim fun v hv => h.empty v hv.2)
  · subst B
    have he := collapse p hp
    subst p
    exact row_supp_empty_l J hZF hν h.empty k

end YesMetaZFC.Model.Forcing.Internal
