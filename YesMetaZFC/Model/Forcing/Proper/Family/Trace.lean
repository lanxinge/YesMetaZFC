import YesMetaZFC.Model.Forcing.Proper.Family.ClosedSyntax
import YesMetaZFC.Model.Forcing.Proper.Family.Indexed
import YesMetaZFC.Model.Forcing.Proper.Family.ClosedForcing
import YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.FinitaryFamily

/-! # 同时支持地模型初等性与泛型闭包的交集 club

固定司寇伦图、判定图与选择图，把三者合为一张实际有限元运算图。
其最小闭包在 X 上的交集构成 club，每个成员的同一见证 N 同时满足三种闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem ng_trace_club_l {ω χ H δ F G b A X} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hB : ∀ i B, M.mem i δ → Entry_d M i B F → M.mem B H)
    (hA : M.MemberSubset A H) (ha : M.CardinalLessOrEqual I A ω) (hX : M.MemberSubset X H) :
    ∃ C w, Cc_club_d I ω X C ∧ Check_d M b ω w ∧
      ∀ Y, M.mem Y C → ∃ N, Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧
        (∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X) ∧ Ng_closed_d I ω δ F G b H N w := by
  obtain ⟨u, hu, huω⟩ := hω.1.1
  have htr := ZF.h_transitive_l I hZF hH
  have huH := htr ω (ZF.h_ordinal_l I hZF hχ.isLimitOrdinal hH hωχ) u huω
  obtain ⟨A', hA'⟩ := KP.exists_insert (ZF.modelsKP hZF) A u
  have hA'H : M.MemberSubset A' H := fun x hx => ((hA' x).mp hx).elim (hA x) (fun he => he.symm ▸ huH)
  have ha' := ZF.countable_insert_l I hZF hω ha hA'
  obtain ⟨c, J, hModel, hMem⟩ := smdl_membership_l I hZF ⟨u, huH⟩
  obtain ⟨a, V, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hModel.2.1
  obtain ⟨w, hw⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b ω
  have bounds i B hi hiB := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (hB i B hi hiB)
  obtain ⟨P, hP, hp⟩ := ng_joint_exists_l hZFC false ω δ F G b w D huH bounds
  obtain ⟨Q, hQ, hq⟩ := ng_joint_exists_l hZFC true ω δ F G b w D huH bounds
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨id, hid.1⟩ hK.labels
  -- 运算族本身是实际三元集合；标签使用 (运算图,原规则)，无需宿主选择函数。
  obtain ⟨O₀, h₀⟩ := KP.exists_insert (ZF.modelsKP hZF) u K
  obtain ⟨O₁, h₁⟩ := KP.exists_insert (ZF.modelsKP hZF) O₀ P
  obtain ⟨O₂, h₂⟩ := KP.exists_insert (ZF.modelsKP hZF) O₁ Q
  have hO : ∀ L, M.mem L O₂ ↔ L = K ∨ L = P ∨ L = Q := by
    intro L
    simp only [h₂ L, h₁ L, h₀ L, iff_false_intro (hu L), false_or, or_assoc]
  have ho := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω
    (ZF.countable_insert_l I hZF hω (ZF.finite_countable_l I hZF hω (ZF.finite_empty_l I hZF hω hu)) h₀) h₁) h₂
  obtain ⟨W, E, L, _, hE, hL, hW, hc⟩ := ZF.fc_family_l I hZF hω hK.domain ht ho (by
    intro L hL
    rcases (hO L).mp hL with rfl | rfl | rfl
    · exact hK.graph
    · exact hP
    · exact hQ)
  obtain ⟨C, hC, hTrace⟩ := ZFC.fc_trace_club_l I hZFC hω hK.params hE hL hW hA'H ha' hX
  refine ⟨C, w, hC, hw, fun Y hY => ?_⟩
  obtain ⟨N, hn, hCount, he⟩ := (hTrace Y).mp hY
  have hclosed := (hc N).mp hn.2.2.2.1
  have hkN := hclosed K ((hO K).mpr (Or.inl rfl))
  obtain ⟨d, S', hSub, hElem⟩ := selem_of_skolem_l I hZF hω hModel hK.codes hn.2.2.1
    (hK.point_mem_l I hZF hω hModel hkN) (hK.closed_l I hn.2.2.1 hkN)
  exact ⟨N, ⟨hω, hχ, hωχ, hH, hCount, c, J, d, S', ⟨hModel, hMem⟩, hSub, hElem⟩,
    (fun x hx => hn.1 x ((hA' x).mpr (Or.inl hx))), he,
    u, V, S, T, D, P, Q, ⟨hu, hK.codes, hK.params, hK.labels, hK.domain, hP, hQ, hp, hq⟩,
    hn.1 u ((hA' u).mpr (Or.inr rfl)), hclosed P ((hO P).mpr (Or.inr (Or.inl rfl))),
    hclosed Q ((hO Q).mpr (Or.inr (Or.inr rfl)))⟩

/-- 同一交集 club 的每个见证均带全阶段内部提升证书。 -/
theorem ng_trace_forcing_l {ω χ H δ F G b A X} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (hB : ∀ i B, M.mem i δ → Entry_d M i B F → M.mem B H)
    (hA : M.MemberSubset A H) (ha : M.CardinalLessOrEqual I A ω) (hX : M.MemberSubset X H) :
    ∃ C w v, Cc_club_d I ω X C ∧ ∀ Y, M.mem Y C → ∃ N,
      Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ (∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X) ∧
      Hlift_d M ω δ F G b χ H N w v := by
  obtain ⟨C, w, hC, hw, h⟩ := ng_trace_club_l (b := b) hZFC hω hχ hωχ hH hB hA ha hX
  obtain ⟨v, hv⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b χ
  refine ⟨C, w, v, hC, fun Y hY => ?_⟩
  obtain ⟨N, hN, hAN, he, hc⟩ := h Y hY
  have hN' := hN
  obtain ⟨_, _, _, _, hn, c, J, d, S, _, hSub, _⟩ := hN'
  exact ⟨N, hN, hAN, he, ng_closed_forcing_l hZFC hω hχ hωχ hH hSub.subset hn hF hG hB hw hv hc⟩

end YesMetaZFC.Model.Forcing.Internal
