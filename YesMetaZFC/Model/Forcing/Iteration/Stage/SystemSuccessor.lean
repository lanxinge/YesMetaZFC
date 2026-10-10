import YesMetaZFC.Model.Forcing.Iteration.Stage.System
import YesMetaZFC.Model.Forcing.Applications.Cohen.Successor

/-! # 阶段系统的名称后继一键装配

直接消费最后阶段的实际名称及其力迫证书，构造下一阶段并追加到两张内部序列。
所有更早阶段的限制与尾部提升自动延长，有限和可数支撑同时保持。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_system_successor_l (hZF : M.Models ZF) {α δ F H e B R A T t}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hδ : M.SuccessorOf δ α) (hB : Entry_d M α B F) (hR : Entry_d M α R H)
    (hA : Name_d M B A) (hT : Name_d M B T) (ht : Name_d M B t)
    (hP : Forces_d M B R B (preord_m .newest (.bound 1)) (ord_env_l M A T) e)
    (hTop : Forces_d M B R B (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) e) :
    ∃ μ D V G F' H', M.SuccessorOf μ δ ∧
      Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) μ F' H' e ∧
      Row_next_d M α B R e A T t D V ∧
      Reg_embed_d M B R B D V D G ∧
      (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧
      (∀ i p, Entry_d M i p F' ↔ Entry_d M i p F ∨ (i = δ ∧ p = D)) ∧
      (∀ i p, Entry_d M i p H' ↔ Entry_d M i p H ∨ (i = δ ∧ p = V)) ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
        Row_system_supp_d I k ω F → Row_system_supp_d I k ω F' := by
  obtain ⟨D, V, G, hD, hNext, hReg, hId, hLink, hSupp⟩ :=
    row_successor_l hZF (h.stages α B R hB hR) hδ hA hT ht hP hTop
  obtain ⟨μ, hμ⟩ := KP.exists_successor (ZF.modelsKP hZF) δ
  have links i P S (hi : Entry_d M i P F) (hiS : Entry_d M i S H) :
      Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) i P S D V := by
    have hiα : M.MemberSubset i α := by
      rcases (hδ i).mp ((h.conditions.2.2 i).mpr ⟨P, hi⟩) with hiα | hiα
      · exact (h.conditions.1.mem hδ.predecessor_mem).transitive.memberSubset hiα
      · exact fun x hx => (hiα x).mp hx
    exact row_link_comp_l hZF hD.order hiα (h.links i α P S B R hi hiS hB hR hiα) hLink
  obtain ⟨F', H', hs, hF, hH, hS⟩ := row_system_extend_l (ZF.modelsKP hZF) h hμ hD links
  exact ⟨μ, D, V, G, F', H', hμ, hs, hNext, hReg, hId, hF, hH,
    fun I k ω hω hOld => hS I k ω hOld (hSupp I k ω hω (hOld α B hB))⟩

/-- 添加量是最后阶段的任意名称；所有早期阶段的链接随 Cohen 后继自动延长。 -/
theorem row_system_cohen_l (hZF : M.Models ZF) {α δ F H e B R κ}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hδ : M.SuccessorOf δ α) (hB : Entry_d M α B F) (hR : Entry_d M α R H) (hκ : Name_d M B κ) :
    ∃ μ D V G F' H', M.SuccessorOf μ δ ∧
        Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) μ F' H' e ∧
        Row_cohen_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R e κ D V ∧
        Reg_embed_d M B R B D V D G ∧
        (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧
        (∀ i p, Entry_d M i p F' ↔ Entry_d M i p F ∨ (i = δ ∧ p = D)) ∧
        (∀ i p, Entry_d M i p H' ↔ Entry_d M i p H ∨ (i = δ ∧ p = V)) ∧
        ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
          Row_system_supp_d I k ω F → Row_system_supp_d I k ω F' := by
  have hs := h.stages α B R hB hR
  have nz {p} (hp : M.mem p B) : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  obtain ⟨A, T, t, hNames, _⟩ := cohen_names_l hs.order hZF hκ
  obtain ⟨μ, D, V, G, F', H', hμ, hSystem, hNext, hReg, hId, hF, hH, hS⟩ :=
    row_system_successor_l hZF h hδ hB hR hNames.1.1 hNames.1.2.1 hNames.1.2.2
      (hNames.2.2.2.1 e hs.base (nz hs.base)) (hNames.2.2.2.2 e hs.base (nz hs.base))
  exact ⟨μ, D, V, G, F', H', hμ, hSystem, ⟨A, T, t, hNames, hNext⟩, hReg, hId, hF, hH, hS⟩

end YesMetaZFC.Model.Forcing.Internal
