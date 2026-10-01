import YesMetaZFC.Model.Forcing.Proper.Family.IndexedHull
import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 整个阶段族的 H(χ) 与共同 N 一键装配

输入为实际的条件集、序关系两张函数图。H(χ)、可数子集 club、共同选择图
和内部初等 N 全部由原公理构造；同一 N 适用于其所有成员阶段及所有主条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem ng_family_hull_l {ω δ F G b A} (hω : M.IsOmega ω)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ χ X c J N d K, M.IsRegularCardinal I χ ∧ M.mem ω χ ∧ H_d I χ X ∧
      Smem_d I c X J ∧ Ssub_d I c d X J N K ∧ Selem_d I ω c d ∧
      M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧
      M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧
      ∀ i B R q, M.mem i δ → M.mem i N → Entry_d M i B F → Entry_d M i R G →
        ∀ (O : Cond_order_d M B R B), Mstr_d M B R B N q →
        ∀ U (hU : Generic_d M B R B U), U q → U b →
          let E := extension_l M hZF B R B U
          let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
          ∃ (e : M.Domain → E.Domain) (Y Z v c' T' d' S' : E.Domain),
            (∀ a t, Check_d M b a t → Qval_d M B R B U t (e a)) ∧
            (∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y) ∧ Function.Injective e ∧
            E.IsRegularCardinal J (e χ) ∧ H_d J (e χ) Y ∧
            (∀ x, x ∈ Y ↔ Ng_mem_d M B R B U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R B U N x) ∧
            E.IsOmega v ∧ E.TransitiveSet Y ∧ E.CardinalLessOrEqual J Z v ∧
            Smem_d J c' Y T' ∧ Ssub_d J c' d' Y T' Z S' ∧ Selem_d J v c' d' := by
  obtain ⟨A₁, h₁⟩ := KP.exists_insert (ZF.modelsKP hZF) A F
  obtain ⟨A₂, h₂⟩ := KP.exists_insert (ZF.modelsKP hZF) A₁ G
  obtain ⟨A₃, h₃⟩ := KP.exists_insert (ZF.modelsKP hZF) A₂ δ
  obtain ⟨A₄, h₄⟩ := KP.exists_insert (ZF.modelsKP hZF) A₃ b
  have ha₄ := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω
    (ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω ha h₁) h₂) h₃) h₄
  obtain ⟨χ, X, hχ, hωχ, hX, hA₄X⟩ := ZFC.h_cover_l I hZFC hω A₄
  have hXtr := ZF.h_transitive_l I hZF hX
  have hA₄ := hXtr A₄ hA₄X
  have hA₃ a ha := hA₄ a ((h₄ a).mpr (Or.inl ha))
  have hA₂ a ha := hA₃ a ((h₃ a).mpr (Or.inl ha))
  have hA₁ a ha := hA₂ a ((h₂ a).mpr (Or.inl ha))
  have hFX := hA₁ F ((h₁ F).mpr (Or.inr rfl))
  have hB i B (_ : M.mem i δ) (hiB : Entry_d M i B F) := (trans_entry_l hXtr hFX hiB).2
  obtain ⟨C, hC, _⟩ := ZFC.cc_all_l I hZFC hω X
  obtain ⟨c, J, N, d, K, hM, hSub, hElem, hAN, _, hn, hg⟩ :=
    ng_indexed_club_l hZFC hω hχ hωχ hX hF hG hB hC hA₄ ha₄
  have hA₃N a ha := hAN a ((h₄ a).mpr (Or.inl ha))
  have hA₂N a ha := hA₃N a ((h₃ a).mpr (Or.inl ha))
  have hA₁N a ha := hA₂N a ((h₂ a).mpr (Or.inl ha))
  exact ⟨χ, X, c, J, N, d, K, hχ, hωχ, hX, hM, hSub, hElem,
    (fun a ha => hA₁N a ((h₁ a).mpr (Or.inl ha))), hn,
    hA₁N F ((h₁ F).mpr (Or.inr rfl)), hA₂N G ((h₂ G).mpr (Or.inr rfl)),
    hA₃N δ ((h₃ δ).mpr (Or.inr rfl)), hAN b ((h₄ b).mpr (Or.inr rfl)), hg⟩

end YesMetaZFC.Model.Forcing.Internal
