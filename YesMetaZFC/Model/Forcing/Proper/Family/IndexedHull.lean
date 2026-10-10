import YesMetaZFC.Model.Forcing.Proper.Family.ClosedLift
import YesMetaZFC.Model.SetTheory.Internal.ElementaryClub

/-! # 全阶段共用的内部初等小模型

判定和选择各只构造一张实际图。一个 club 的两次闭包与地模型司寇伦闭包，
给出同一个 N；每个属于 N 的阶段都继承所需运算，不再逐阶段重新选择 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 在指定 club 内一次选取 N；其成员阶段的任何主条件都支持全内部 H(χ) 初等提升。 -/
theorem ng_indexed_club_l {ω χ X δ F G b C A} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hX : H_d I χ X)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (hB : ∀ i B, M.mem i δ → Entry_d M i B F → M.mem B X)
    (hC : Cc_club_d I ω X C) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ c J N d K, Smem_d I c X J ∧ Ssub_d I c d X J N K ∧ Selem_d I ω c d ∧
      M.MemberSubset A N ∧ M.mem N C ∧ M.CardinalLessOrEqual I N ω ∧
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
  obtain ⟨u, hu, huω⟩ := hω.1.1
  have hXtr := ZF.h_transitive_l I hZF hX
  have huX := hXtr ω (ZF.h_ordinal_l I hZF hχ.isLimitOrdinal hX hωχ) u huω
  obtain ⟨A', hA'⟩ := KP.exists_insert (ZF.modelsKP hZF) A u
  have hA'X : M.MemberSubset A' X := fun x hx => ((hA' x).mp hx).elim (hA x) (fun he => he.symm ▸ huX)
  have ha' := ZF.countable_insert_l I hZF hω ha hA'
  obtain ⟨c, J, hModel, hMem⟩ := smdl_membership_l I hZF ⟨u, huX⟩
  obtain ⟨w, hw⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b ω
  obtain ⟨V, hV⟩ := scode_exists_l I hZF hω
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I V ω
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω X
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I T S
  have bounds i B hi hiB := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hX (hB i B hi hiB)
  obtain ⟨P, hP, hp⟩ := ng_joint_exists_l hZFC false ω δ F G b w D huX bounds
  obtain ⟨Q, hQ, hq⟩ := ng_joint_exists_l hZFC true ω δ F G b w D huX bounds
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hV) ⟨id, hid.1⟩ hT
  obtain ⟨C₁, hC₁, h₁⟩ := ZFC.fc_club_refine_l I hZFC hω hS hD hP ht hC
  obtain ⟨C₂, hC₂, h₂⟩ := ZFC.fc_club_refine_l I hZFC hω hS hD hQ ht hC₁
  obtain ⟨N, d, K, hSub, hElem, hAN, hN₂⟩ := selem_club_hull_l I hZFC hω hModel hC₂ hA'X ha'
  have hN₁ := ((h₂ N).mp hN₂).1
  have hNC := ((h₁ N).mp hN₁).1
  have hNP := ((h₁ N).mp hN₁).2
  have hNQ := ((h₂ N).mp hN₂).2
  have hn := (hC.members N hNC).2
  have huN := hAN u ((hA' u).mpr (Or.inr rfl))
  refine ⟨c, J, N, d, K, ⟨hModel, hMem⟩, hSub, hElem,
    (fun a ha => hAN a ((hA' a).mpr (Or.inl ha))), hNC, hn, ?_⟩
  intro i B R q hi hiN hiB hiR O hm U hU hqU hbU
  exact ng_closed_lift_l O hZFC hU hbU hω hχ hωχ hX (hB i B hi hiB) hSub.subset hn hw hF hG
    ⟨u, V, S, T, D, P, Q, ⟨hu, hV, hS, hT, hD, hP, hQ, hp, hq⟩, huN, hNP, hNQ⟩ hi hiN hiB hiR hm hqU

end YesMetaZFC.Model.Forcing.Internal
