import YesMetaZFC.SetTheory.InaccessibleHierarchy
import YesMetaZFC.SetTheory.LargeCardinal.RankEnumerationSyntax

/-! # 源中的实际秩层枚举族

先对每个 Vα 取最小序数枚举，再用原对象选择公理统一成图。正则 Hδ 的
小定义域函数封闭保证整张枚举图属于 Vδ，随后提供可传输的有界最小性检验。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_family_l (hZFC : M.Models ZFC) {ω δ X κ : M.Domain} (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hκ : M.mem κ δ) :
    ∃ G T, M.mem G X ∧ M.mem T X ∧ M.TransitiveSet T ∧ M.mem κ T ∧ M.mem G T ∧ Fn0_d κ T G ∧
      ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) α p := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hH := ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX
  have hκX := ZF.v_ordinal_mem_l I hZF hX hκ
  have ht := ZF.v_transitive_l I hZF hX
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => κ⟩
  let φ : BinarySchema 0 := { body := er_enum_m (.bound 1) .newest }
  have sat α p : φ.denote ρ α p ↔ Er_enum_d I α p := er_enum_sat_l I hZF.1 ..
  obtain ⟨G, hg, gs⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := κ) (Y := X) (fun α hα => by
    have hαδ := hr.isCardinal.1.transitive κ hκ α hα
    obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hαδ)
    obtain ⟨ξ, hξ, hVξ⟩ := ZFC.inaccessible_level_small_l I hZFC hω hωδ hr hs hαδ hV
    obtain ⟨μ, g, hμδ, hμ, bij⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ hVξ
    have hμX := ZF.v_ordinal_mem_l I hZF hX hμδ
    have hVX := ZF.v_mem_l I hZF hV hX hαδ
    have hgX := ZFC.h_function_l hZFC hω hr hωδ hH hμX (bij.1.1.mono_target_l I (ht V hVX))
    obtain ⟨p, hp⟩ := I.total μ g
    exact ⟨p, ZFC.h_kpair_l hZFC hω hr hωδ hH hp hμX hgX, (sat α p).mpr ⟨V, μ, g, hV, hp, hμ, bij⟩⟩)
  have hGX := ZFC.h_function_l hZFC hω hr hωδ hH hκX hg
  obtain ⟨p, hp⟩ := I.total κ G
  have hpX := ZFC.h_kpair_l hZFC hω hr hωδ hH hp hκX hGX
  obtain ⟨β, T, hβ, hT, hpT⟩ := (ZF.v_limit_mem_l I hZF hX hr.isLimitOrdinal.2.2 p).mp hpX
  have hTt := ZF.v_transitive_l I hZF hT
  obtain ⟨hκT, hGT⟩ := hp.mem_l M hTt hpT
  have bound α p (hap : Rd_entry_d α p G) : M.mem p T := by
    obtain ⟨r, hr, hrG⟩ := hap
    exact (hr.mem_l M hTt (hTt G hGT r hrG)).2
  exact ⟨G, T, hGX, ZF.v_mem_l I hZF hT hX hβ, hTt, hκT, hGT,
    (fn0_of_function_l (ZF.modelsKP hZF) hg).retarget_l bound, fun α p hp => (sat α p).mp (gs α p hp)⟩

theorem er_stage_l (hZF : M.Models ZF) {κ H F T G : M.Domain} (hκ : M.IsOrdinal κ) (hT : M.TransitiveSet T)
    (history : ∀ α U, Rd_entry_d α U F → V_d (kp_pair_l (ZF.modelsKP hZF)) α U)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP hZF)) α p) (h : M.Domain) :
    Er_stage_d κ H F T G h := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro α _ U _ p hp hαU hαp
  obtain ⟨V, μ, g, hV, hpg, hμ, hg⟩ := enums α p hαp
  have eq := ZF.v_unique_l I hZF hV (history α U hαU)
  subst V
  obtain ⟨hμT, hgT⟩ := hpg.mem_l M hT hp
  exact ⟨μ, hμT, g, hgT, hpg, ⟨fn0_of_function_l (ZF.modelsKP hZF) hg.1.1, hg.2⟩,
    fun ν hν hsur => ZF.enumeration_minimal_l I hZF hμ hg (hκ.mem hν)
      (fn0_function_l (ZF.modelsKP hZF) hsur.1) hsur.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
