import YesMetaZFC.SetTheory.LargeCardinal.TypeImageSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationUltraRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCriticalPoint

/-! # 相对类型像证书的实际读取

秩段、商、常值图和坍塌均读取原证书；源实例由工作模型的实际闭性构造。
只使用内层有限序列闭性与相对秩证书，毋须内层 ZF 或游戏特有的反射句子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω μ K₀ Z R₀ η C : M.Domain} (nc : Nonempty {x // M.mem x C}) {s}
  (ρ : Env (rt_model_l C nc) s)
  (o κ δ τ U D u X K R L F c d Y T j κ' U' D' u' : Term s)
local notation "v" => (fun (t : Term s) => Subtype.val (Definitional.Term.eval ρ t))

theorem ti_image_read_l (owner : Ep_source_d hZF ω μ K₀ Z R₀) (power : Sc_power_d Z)
    (hC : M.mem C Z) (rankC : Vr_d Z η C) (fs : Fs_read_d ω C)
    (hw : v o = ω) (hδ : M.IsLimitOrdinal (v δ)) (regular : Sc_regular_d Z (v δ))
    (valid : Formula.satisfies ρ (ti_image_m o κ δ τ U D u X K R L F c d Y T j κ' U' D' u')) :
    M.mem (v X) Z ∧ Vr_d Z (v δ) (v X) ∧ ∃ K₁, Ep_source_d hZF ω (v κ) K₁ (v X) (v R) ∧
      M.mem (v L) (v δ) ∧ M.mem (v κ) (v L) ∧ M.mem (v τ) (v L) ∧
      It_local_d ω (v X) (v κ) (v L) (v F) ∧ Sc_inaccessible_d ω (v X) (v L) ∧
      Ex_strength_d hZF ω (v κ) (v L) (v X) (v F) ∧ Smem_d I (v c) (v X) (v R) ∧
      Smem_d I (v d) (v Y) (v T) ∧ It_ultra_d hZF ω (v κ) (v L) (v F) (v c) (v d) (v j) ∧
      Wd_crit_d I (v X) (v j) (v κ) (v κ') ∧ M.MemberSubset (v L) (v κ') ∧ M.IsLimitOrdinal (v κ') ∧
      Rd_entry_d (v U) (v U') (v j) ∧ Rd_entry_d (v D) (v D') (v j) ∧ Rd_entry_d (v u) (v u') (v j) := by
  let N := rt_model_l C nc
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have Δ (φ : Formula 1 s) (hd : φ.IsDelta0) (h : Formula.satisfies ρ φ) :=
    (rt_model_delta_l fs.transitive nc hd ρ).mp h
  have smem (a A B : Term s) (h : Formula.satisfies ρ (smem_m (𝒞 := kpair_convention_l) a A B)) :
      Smem_d I (v a) (v A) (v B) :=
    (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair ..).mp ((smem_sat_l J ..).mp h)
  have entry (a b f : Term s) (h : Formula.satisfies ρ (rd_entry0_m a b f)) : Rd_entry_d (v a) (v b) (v f) := by
    simpa only [rd_entry0_sat_l hZF.1, @eval_image_env_l N M Subtype.val] using Δ _ (rd_entry0_delta_l ..) h
  simp only [ti_image_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨rank, _, hLδ, hκL, hτL, quality, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩ := valid
  have rank := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ δ X).mp rank
  have mx := smem c X R mx
  have my := smem d Y T my
  have hXZ := owner.transitive C hC (v X) (X.eval ρ).property
  have full := Vr_d.of_rank_l hZF owner.transitive hC rankC (X.eval ρ).property rank
  have trans := full.transitive_l hZF owner.transitive hXZ
  have quality := Δ _ (ex_quality_delta_l ..) quality
  simp only [ex_quality_m, Formula.satisfies_conj_iff] at quality
  obtain ⟨loc, card, strong⟩ := quality
  have loc := (ex_local_sat_l _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)).mp loc
  have card := (ex_inaccessible_sat_l _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)).mp card
  simp only [@eval_image_env_l N M Subtype.val, hw] at loc card
  have ord := (loc.ordinals_l (ZF.modelsKP hZF) trans).1
  have localCopy := loc
  obtain ⟨hωX, hκX, _, _, pre⟩ := localCopy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω (v κ) := ord.transitive ω pre.1.2.2.1
  obtain ⟨K₁, source⟩ := owner.rank_l hZF hXZ full hδ regular hωX mx hκX ord below
  have strong := (ex_strength_sat_l hZF (K₀ := K₁) (R := v R) _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val, hw] using source)).mp strong
  simp only [@eval_image_env_l N M Subtype.val, hw] at strong
  obtain ⟨P, hP, subsets⟩ := power.rank_l hZF owner.transitive hXZ full hδ K₁ source.finite_mem
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory source.finite hP subsets)
  have actual := it_ultra_read_l hZFC fs nc ρ o κ L F c d j hw source mx family (loc.coherent_l hZF (source.read_source_l hZF)) ultra
  have critical := (wd_crit_sat_l J ext ρ X j κ κ').mp critical
  have image := (rt_entry_l fs.transitive nc hZF.1 ..).mp critical.image
  have crit := actual.critical_l hZF source family source (fun _ _ _ _ _ _ => Iff.rfl) loc hκL mx my image
  have bound : M.MemberSubset (v L) (v κ') := by
    have bound := (Formula.satisfies_subset_iff ..).mp (Δ _ (.atom ..) bound)
    simpa only [Structure.MemberSubset, @eval_image_env_l N M Subtype.val] using bound
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  exact ⟨hXZ, full, K₁, source, hLδ, hκL, hτL, loc, card, strong, mx, my, actual, crit, bound, limit,
    entry U U' j hU, entry D D' j hD, entry u u' j hu⟩

end YesMetaZFC.SetTheory.LargeCardinal
