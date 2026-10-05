import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.Skolem
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 极限秩初段中的实际小 Skolem 壳

代码集与有限参数空间由固定的有限次配对和幂集界控制；选择图和枚举图
再由关系图封闭放入 Vδ。这里只需 δ 为大于 ω 的极限序数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem scode_rank_mem_l (hZF : M.Models ZF) {ω δ Z C : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hZ : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z)
    (hωZ : M.mem ω Z) (hC : Scode_d (kp_pair_l (ZF.modelsKP hZF)) ω C) : M.mem C Z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  have hPZ := ZF.v_product_mem_l I hZF hZ hδ hωZ hωZ hP
  obtain ⟨O, hO⟩ := ZF.exists_cartesianProduct hZF I ω P
  have hOZ := ZF.v_product_mem_l I hZF hZ hδ hωZ hPZ hO
  obtain ⟨J, hJ⟩ := ZF.fseq_space_exists_l I hZF hω O
  have hJZ := ZF.v_fseq_mem_l I hZF hZ hδ hω hωZ hOZ hJ
  have op {k c i j} (hc : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c O := by
    obtain ⟨a, o, ho, ha, code⟩ := hc
    exact (hO c).mpr ⟨o, num_mem_l hZF.1 hω ho, a, (hP a).mpr ⟨i, hi, j, hj, ha⟩, code⟩
  have program {n F} (hF : Sfm_d I ω n F) : M.mem F J := by
    refine (hJ F).mpr ⟨n, hF.1, hF.2.1.2.1, hF.2.1.2.2, fun r hr => ?_⟩
    obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp hr
    have hrω := hω.transitive hZF n hF.1 r hr
    refine ⟨c, ?_, hc⟩
    rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact op hs hi hj
    · exact op hs hi hj
    · exact op hs (hω.transitive hZF r hrω i hi) (hω.transitive hZF r hrω j hj)
    · exact op hs hi (hω.transitive hZF r hrω j hj)
  obtain ⟨Y, hY, hJY, hωY⟩ := ZF.v_joint_bound_l I hZF hZ hJZ hωZ
  apply ZF.v_relation_mem_l I hZF hZ hδ hY
  intro a ha
  obtain ⟨n, F, r, code, hF, hr⟩ := (hC a).mp ha
  exact ⟨F, hJY F (program hF), r, hωY r (hω.transitive hZF n hF.1 r hr), code⟩

/-- 直接给论文所用秩初段构造实例；不把 Vδ 换成 Hχ，也不要求 Vδ 满足 ZF。 -/
theorem sh_source_of_v_l (hZFC : M.Models ZFC) {ω δ Z : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ)
    (hZ : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ Z) :
    Sh_source_d (ZF.modelsKP (ZFC.models_zf_l hZFC)) ω Z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hωZ := ZF.v_ordinal_mem_l I hZF hZ hωδ
  have trans := ZF.v_transitive_l I hZF hZ
  have function {A B f} (hA : M.mem A Z) (hB : M.mem B Z) (hf : M.IsSetFunctionFromTo I f A B) : M.mem f Z := by
    obtain ⟨Y, hY, hAY, hBY⟩ := ZF.v_joint_bound_l I hZF hZ hA hB
    exact ZF.v_relation_mem_l I hZF hZ hδ hY fun p hp =>
      (fn0_of_function_l (ZF.modelsKP hZF) hf).1 p hp |>.elim fun a ha => ha.2.elim fun b hb =>
        ⟨a, hAY a ha.1, b, hBY b hb.1, hb.2⟩
  intro c A R U κ f hA _ _ hκZ _ hm hκ hωκ hUA hf
  obtain ⟨u, C, J, T, D, K, N, g, skolem, hull, hg⟩ := ssk_hull_enum_l I hZFC hω hκ hωκ hm hUA hf
  have hC := scode_rank_mem_l hZF hω hδ hZ hωZ skolem.codes
  have hJ := ZF.v_fseq_mem_l I hZF hZ hδ hω hωZ hA skolem.params
  have hT := ZF.v_product_mem_l I hZF hZ hδ hC hωZ skolem.labels
  have hD := ZF.v_product_mem_l I hZF hZ hδ hT hJ skolem.domain
  have hN := ZF.v_subset_mem_l I hZF hZ hA hull.2.1
  exact ⟨u, C, J, T, D, K, N, g, trans A hA u skolem.point, hC, hJ, hT, hD,
    function hD hA skolem.graph, hN, function hκZ hN hg.1.1, skolem,
    ⟨hull.1, hull.2.1, hull.2.2.1, fun B _ hUB _ => hull.2.2.2 B hUB⟩, hg⟩

end YesMetaZFC.SetTheory.Internal
