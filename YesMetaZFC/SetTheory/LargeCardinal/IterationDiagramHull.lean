import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReflectHull
import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationUltraPull

/-! # 保留原树序的可数模型列及全初等边列

指定有限参数一并放入种子；原树序逐点固定。证书层同时反射原超幂公式，
供同一小树的操作列继续读取指定商和塌缩。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_hull_l {ω T Q G : M.Domain} (hω : M.IsOmega ω)
    (diagram : It_diagram_d hZF ω ω T Q G) (sources : ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c)
    {n} (v : Fin n → M.Domain) : ∃ B R b K U S u J C V π Q₀ G₀,
      Ep_source_d hZF ω ω K B R ∧ Ep_source_d hZF ω ω J U S ∧ Smem_d I b B R ∧ Smem_d I u U S ∧
      Smap_d I ω b u B U π ∧ M.CardinalLessOrEqual I B ω ∧ M.mem C B ∧ Fs_read_d ω C ∧ M.TransitiveSet V ∧
      Rd_entry_d C V π ∧ M.mem T C ∧ M.mem Q₀ C ∧ M.mem G₀ C ∧
      Rd_entry_d T T π ∧ Rd_entry_d Q₀ Q π ∧ Rd_entry_d G₀ G π ∧
      It_diagram_d hZF ω ω T Q₀ G₀ ∧ (∀ i c, Rd_entry_d i c Q₀ → It_source_d hZF ω c) ∧
      Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V ∧
      ∀ i, ∃ x, M.mem x C ∧ Rd_entry_d x (v i) π := by
  let w : Fin (n + 3) → M.Domain := Fin.cases T (Fin.cases Q (Fin.cases G v))
  obtain ⟨B, R, b, K, U, S, u, J, C, V, π, sb, su, mb, mu, hj, count, hC, fs, vt, hCV, reflect, params⟩ :=
    ep_reflect_hull_l hZFC hω w
      (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (by simp -implicitDefEqProofs)
  obtain ⟨T₀, hT, hTT⟩ := params 0
  obtain ⟨Q₀, hQ, hQQ⟩ := params 1
  obtain ⟨G₀, hG, hGG⟩ := params 2
  obtain ⟨eq, small, ready⟩ := it_diagram_pull_l hZF sb su mb mu hj hC fs.transitive vt hCV hQ hG hTT hQQ hGG diagram sources
  change T₀ = T at eq
  subst T₀
  exact ⟨B, R, b, K, U, S, u, J, C, V, π, Q₀, G₀, sb, su, mb, mu, hj, count, hC, fs, vt, hCV,
    hT, hQ, hG, hTT, hQQ, hGG, small, ready, reflect, fun i => params i.succ.succ.succ⟩

end YesMetaZFC.SetTheory.LargeCardinal
