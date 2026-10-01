import YesMetaZFC.Model.Forcing.Proper.Generic.Elementary
import YesMetaZFC.Model.Forcing.Proper.Syntax
import YesMetaZFC.Model.SetTheory.Internal.ElementaryClub

/-! # 在给定传递环境中装配内部泛型初等提升

判定集属于环境 X 时，可在 proper club 中同时闭合统一选择图和地模型司寇伦图。
此装配同时服务累积层环境及实际 H(χ)，不重复主条件与全内部真值的证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 自动构造内部初等 N、主加强，以及每个泛型中的可数初等 N[G]；不交付未实现的闭包参数。 -/
theorem ng_elementary_on_l {ω A p X} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hA : M.CardinalLessOrEqual I A ω) (hp : M.mem p B) (hpz : p ≠ z)
    (hX : M.TransitiveSet X) (hBound : ∀ D, M.MemberSubset D B → M.mem D X)
    (hAX : M.MemberSubset A X) :
    ∃ c T N d S q, Smem_d I c X T ∧ Ssub_d I c d X T N S ∧
      Selem_d I ω c d ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧
      Below_d M B R z q p ∧ Mstr_d M B R z N q ∧
      ∀ U (hU : Generic_d M B R z U), U q →
        let E := extension_l M hZF B R z U
        let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
        ∃ Y Z v c' T' d' S' : E.Domain,
          (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) ∧
          E.IsOmega v ∧ E.TransitiveSet Y ∧ E.CardinalLessOrEqual J Z v ∧ Smem_d J c' Y T' ∧
          Ssub_d J c' d' Y T' Z S' ∧ Selem_d J v c' d' := by
  obtain ⟨u, hu⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hun := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B u hu
  obtain ⟨A₁, hA₁⟩ := KP.exists_insert (ZF.modelsKP hZF) A u
  obtain ⟨A₂, hA₂⟩ := KP.exists_insert (ZF.modelsKP hZF) A₁ p
  have ha := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω hA hA₁) hA₂
  have huX := hBound u (fun x hx => (hu x hx).elim)
  have hpX := hX B (hBound B (fun _ h => h)) p hp
  have hA₂X : M.MemberSubset A₂ X := fun x hx => ((hA₂ x).mp hx).elim
    (fun hx => ((hA₁ x).mp hx).elim (hAX x) (fun he => he.symm ▸ huX)) (fun he => he.symm ▸ hpX)
  have huA := (hA₂ u).mpr (Or.inl ((hA₁ u).mpr (Or.inr rfl)))
  have hpA := (hA₂ p).mpr (Or.inr rfl)
  obtain ⟨c, T₀, hModel, hMem⟩ := smdl_membership_l I hZF ⟨u, hA₂X u huA⟩
  obtain ⟨μ, hμ⟩ := ng_name_exists_l M hZF B X
  obtain ⟨w, hw, _, _⟩ := zf_check_l M hZF hp ω
  let ρ := ng_elementary_env_l w μ u
  let φ := ssk_mem_s kpair_convention_l
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I C ω
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω X
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I T S
  obtain ⟨K, L, hK, hL, hk, hl⟩ := ng_operations_l hZFC φ ρ B R z p ω (hA₂X u huA) hBound hD
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hC) ⟨J, hJ.1⟩ hT
  obtain ⟨C₀, hC₀, hMaster⟩ := hP X (hX B (hBound B (fun _ h => h)))
  obtain ⟨C₁, hC₁, h₁⟩ := ZFC.fc_club_refine_l I hZFC hω hS hD hK ht hC₀
  obtain ⟨C₂, hC₂, h₂⟩ := ZFC.fc_club_refine_l I hZFC hω hS hD hL ht hC₁
  obtain ⟨N, d, S₀, hSub, hElem, hAN, hN⟩ := selem_club_hull_l I hZFC hω hModel hC₂ hA₂X ha
  have hN₁ := ((h₂ N).mp hN).1
  have hN₀ := ((h₁ N).mp hN₁).1
  have hKN := ((h₁ N).mp hN₁).2
  have hLN := ((h₂ N).mp hN).2
  have hCount := (hC₀.members N hN₀).2
  obtain ⟨q, hqp, hm⟩ := hMaster N hN₀ p (hAN p hpA) hp hpz
  refine ⟨c, T₀, N, d, S₀, q, ⟨hModel, hMem⟩, hSub, hElem,
    fun a ha => hAN a ((hA₂ a).mpr (Or.inl ((hA₁ a).mpr (Or.inl ha)))), hCount, hqp, hm, ?_⟩
  intro U hU hq
  have hpU := hU.upward q p hq hp hqp.2.2
  obtain ⟨Y, Z, v, c', T', d', S', hY, hZ, hv, hc', hs', he'⟩ :=
    ng_elementary_l O hZF hU hpU hω hun (hAN u huA) hw hμ hC hT hS hD hK hL hk hl
      hSub.subset hKN hLN hm hq
  obtain ⟨Z', v', hZ', hv', hz'⟩ := ng_countable_l O hZF hU hω hCount
  have heZ : Z' = Z := (extension_ext_l O hZF hU).eq_of_same_members _ _
    (fun x => (hZ' x).trans (hZ x).symm)
  have hev : v' = v := (extension_ext_l O hZF hU).eq_of_same_members _ _
    (fun x => ⟨hv'.2 v hv.1 x, hv.2 v' hv'.1 x⟩)
  subst Z' v'
  exact ⟨Y, Z, v, c', T', d', S', hY, hZ, hv, ng_transitive_l O hZF hU hX hY, hz', hc', hs', he'⟩

end YesMetaZFC.Model.Forcing.Internal
