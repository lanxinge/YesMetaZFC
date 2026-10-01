import YesMetaZFC.Model.Forcing.Proper.Hereditary.Hull
import YesMetaZFC.Model.Forcing.Proper.Name

/-! # 同一内部模型中的后继主条件选择

先由被迫 proper 构造真实 club 名称，把它及内部 ω 名称加入可数种子，再一次
装配 N、地阶段主加强与 H(χ) 提升。每个接受该加强的泛型中，N[G] 内任意后继
条件都可加强为 N[G] 主条件；调用者不需要提供额外的 club 或模型闭包证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
include O
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 自动选取同一个 N，同时支持地阶段主条件和所有泛型中的后继主条件选择。 -/
theorem ng_next_master_l {ω A Q T p} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hA : M.CardinalLessOrEqual I A ω) (hp : M.mem p B) (hpz : p ≠ z)
    (hQ : Name_d M B Q) (hT : Name_d M B T)
    (hNext : Forces_d M B R z (proper_exists_m .newest (.bound 1)) (ord_env_l M Q T) p) :
    ∃ χ H c S N d K q, M.IsRegularCardinal I χ ∧ M.mem ω χ ∧ H_d I χ H ∧
      Smem_d I c H S ∧ Ssub_d I c d H S N K ∧ Selem_d I ω c d ∧
      M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧
      Below_d M B R z q p ∧ Mstr_d M B R z N q ∧
      ∀ U (_hU : Generic_d M B R z U), U q →
        let E := extension_l M hZF B R z U
        ∃ Z D V : E.Domain, (∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) ∧
          Qval_d M B R z U Q D ∧ Qval_d M B R z U T V ∧
          ∀ r, r ∈ Z → r ∈ D → ∃ s, Below_d E D V D s r ∧ Mstr_d E D V D Z s := by
  obtain ⟨w, X, C, hNames⟩ := pr_name_exists_l O hZFC hQ hT hp hpz hNext
  obtain ⟨A₁, hA₁⟩ := KP.exists_insert (ZF.modelsKP hZF) A w
  obtain ⟨A₂, hA₂⟩ := KP.exists_insert (ZF.modelsKP hZF) A₁ C
  have hA₂c := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω hA hA₁) hA₂
  obtain ⟨χ, H, c, S, N, d, L, q, hχ, hωχ, hH, hM, hS, hEl, ha, hn, hqp, hm, hg⟩ :=
    ng_hchi_hull_l O hZFC hω hP hA₂c hp hpz
  have hwN := ha w ((hA₂ w).mpr (Or.inl ((hA₁ w).mpr (Or.inr rfl))))
  have hCN := ha C ((hA₂ C).mpr (Or.inr rfl))
  refine ⟨χ, H, c, S, N, d, L, q, hχ, hωχ, hH, hM, hS, hEl,
    (fun a haA => ha a ((hA₂ a).mpr (Or.inl ((hA₁ a).mpr (Or.inl haA))))), hn, hqp, hm, ?_⟩
  intro U hU hqU
  let E := extension_l M hZF B R z U
  have hEZFC := preserves_zfc_l O hZFC hU
  have hE := preserves_zf_l O hZF hU
  have hpU := hU.upward q p hqU hp hqp.2.2
  obtain ⟨e, Y, Z, v, c', T', d', S', _, hmem, hi, hχE, hHE, _, hZ, hv, _, hZc, hME, hSE, hEl⟩ := hg U hU hqU
  obtain ⟨D, hD⟩ := name_value_l (R := R) (z := z) (U := U) hQ
  obtain ⟨V, hV⟩ := name_value_l (R := R) (z := z) (U := U) hT
  obtain ⟨w', hw'⟩ := name_value_l (R := R) (z := z) (U := U) hNames.2.2.1
  obtain ⟨X', hX'⟩ := name_value_l (R := R) (z := z) (U := U) hNames.2.2.2.1
  obtain ⟨C', hC'⟩ := name_value_l (R := R) (z := z) (U := U) hNames.2.2.2.2.1
  obtain ⟨hwω, hBase⟩ := pr_name_value_l O hZF hU hNames hpU hD hV hw' hX' hC'
  have hwv : w' = v := hE.1.eq_of_same_members _ _ (fun x => ⟨hwω.2 v hv.1 x, hv.2 w' hwω.1 x⟩)
  subst w'
  have heω : E.IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi hmem hZF
    (internal_foundation_l O hZF hU) hω (fun A => KP.difference_exists_d (ZF.modelsKP hE) A (e ω))
  have hve : v = e ω := hE.1.eq_of_same_members _ _ (fun x => ⟨hv.2 (e ω) heω.1 x, heω.2 v hv.1 x⟩)
  refine ⟨Z, D, V, hZ, hD, hV, fun r hrZ hrD => ?_⟩
  exact pr_base_master_l hEZFC hv hχE (hve.symm ▸ (image_member_l e hi hmem).mpr hωχ)
    hHE hME hSE hEl ((hZ v).mpr ⟨w, hwN, hw'⟩) ((hZ C').mpr ⟨C, hCN, hC'⟩) hZc hBase hrZ hrD
      (fun he => KP.mem_irrefl_d (ZF.modelsKP hE) D (he ▸ hrD))

end YesMetaZFC.Model.Forcing.Internal
