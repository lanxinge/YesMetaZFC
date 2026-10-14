import YesMetaZFC.SetTheory.LargeCardinal.IterationFailureCopy
import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramHull
import YesMetaZFC.SetTheory.LargeCardinal.IterationNicePull
import YesMetaZFC.SetTheory.LargeCardinal.IterationCutPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationInitialPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationDescent

/-! # 可数 nice 树返回原秩层

返回失败给出正则根上的真实下降复制树。包含整棵树和截断列的可数反射壳
恢复同一含恒等步的 nice 树、同一秩段及下降值；原正则根给出初始行，双重基础反证排除失败。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定可数根到任意真实秩层的初等图，含 padding 的 nice ω 树有共尾良基枝及返回因子。 -/
theorem it_pnice_return_l {ω c X R T Q G E L o θ A a S π : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (mx : Smem_d I c X R)
    (count : M.CardinalLessOrEqual I X ω) (ho : ∀ x, ¬ M.mem x o)
    (rank : V_d I θ A) (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    It_return_d hZF ω o T Q G a A π := by
  classical
  have hw := nice.tree.omega
  apply Classical.byContradiction
  intro bad
  -- 失败产生原树序上的真实下降复制树；整套列图同时进入反射壳。
  obtain ⟨δ, Z, z, Rz, Q', G', E', L', A', D', regular, above, outer, mz, copied, powers, cuts, root, _, drop⟩ :=
    it_pnice_failure_copy_l hZFC nice mx count ho rank ma embed bad
  let v : Fin 5 → M.Domain := Fin.cases z (Fin.cases E' (Fin.cases L' (Fin.cases A' (fun _ => D'))))
  obtain ⟨B, Rb, b, K, U, Su, u, J, C, V, σ, q, g, sb, su, mb, mu, hs, countB, hC, fs, vt, hCV,
    hT, hq, hg, hTT, hQQ, hGG, diagram, _, reflect, params⟩ :=
    it_diagram_hull_l hZFC hw copied.tree.diagram copied.tree.sources v
  obtain ⟨c₀, _, hcc⟩ := params 0
  obtain ⟨e, he, hEE⟩ := params 1
  obtain ⟨l, hl, hLL⟩ := params 2
  obtain ⟨d, hd, hAA⟩ := params 3
  obtain ⟨n, hn, hDD⟩ := params 4
  have small := it_pnice_pull_l hZFC sb su mb mu hs hC fs vt hCV hq hg he hl
    hcc hTT hQQ hGG hEE hLL diagram copied powers reflect
  have smallcuts := it_cut_pull_l hZF sb su mb mu hs hC fs.transitive vt hCV hq he hd hn
    hQQ hEE hAA hDD copied.tree.diagram copied.tree.sources cuts
  have hoω := (diagram.model_domain o).mpr ⟨c₀, small.tree.root o ho⟩
  -- 大根截断等于背景正则 Vβ；同一反塌缩的限制给出真实初始行。
  obtain ⟨a₀, ha₀⟩ := (smallcuts.code_domain o).mp hoω
  obtain ⟨a', _, haa⟩ := hs.1.1.2.2 a₀ (sb.transitive C hC a₀ (rd_entry_transitive_l fs.transitive hn ha₀).2)
  have ha' := (hs.entry_l hZF hw sb.transitive su.transitive mb mu
    (hs.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem o hoω) haa hDD).mp ha₀
  obtain ⟨β, hβ⟩ := (cuts.height_domain o).mp hoω
  obtain ⟨V₀, P₀, mv₀, hV₀, vr, reg, hωV⟩ := cuts.ranks o z a' β Z Rz (copied.tree.root o ho) ha' hβ mz
  obtain ⟨Z₀, R₀, _, mz₀, sz⟩ := copied.tree.sources o z (copied.tree.root o ho)
  obtain ⟨ez, er⟩ := smdl_unique_l I mz₀.1 mz.1
  subst Z₀ R₀
  have βreg := (root β hβ).1
  have βδ := ZF.v_ordinal_height_l hZF outer βreg.1.1 (sz.rank_height_l hZF hV₀ vr reg hωV).1
  obtain ⟨W, vw⟩ := ZF.v_exists_l I hZF βreg.1.1
  obtain ⟨P, F, hP, hF, vc, _⟩ := vr_source_l hZF outer regular.isLimitOrdinal βδ vw
  have eq := vr.unique_l hZF sz.transitive hV₀ (ZF.v_mem_l I hZF vw outer βδ) ⟨P, F, hP, hF, fun t _ => vc t⟩
  have actual : V_d I β V₀ := eq ▸ vw
  have ωβ := vr.ordinal_height_l hZF sz.transitive hV₀ (hw.isOrdinal hZF) hωV
  obtain ⟨X₁, P₁, p, ι, _, _, _, initial⟩ := pn_initial_pull_l hZFC sb su mb mu hs countB haa mv₀ ωβ βreg actual
  -- 原下降值沿同一张图回拉，直接与已完成的模型／原高度双重基础反证矛盾。
  apply it_pnice_no_drop_l hZFC small smallcuts ho ha₀ initial
  intro i j k f α β _ pred edge hα hβ
  exact it_drop_pull_l hZF hw sb.transitive su.transitive mb mu hs sb.omega_mem hGG hAA drop
    k j f α β edge pred.1 ((smallcuts.height_domain k).mpr ⟨α, hα⟩) ((smallcuts.height_domain j).mpr ⟨β, hβ⟩) hα hβ

end YesMetaZFC.SetTheory.LargeCardinal
