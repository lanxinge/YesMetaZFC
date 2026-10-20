import YesMetaZFC.Model.SetTheory.Internal.ZfcRank
import YesMetaZFC.Model.SetTheory.Internal.SourceBinaryRelation
import YesMetaZFC.Model.SetTheory.Internal.SourceCollection
import YesMetaZFC.Model.SetTheory.Internal.SourcePower

/-! # 从内部 ZFC 导出原递归所需的源理论

普通收集先给集合界，全内部分离构造源内真值图，选择再给源内见证函数。
没有把统一化或小定义域收集写进 ZFC 证书的假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_algebra_models_l (h : M.Models ZFC) (ρ : Env M 0) : Formula.satisfies ρ sc_algebra_m := by
  let hf := ZFC.models_zf_l h
  let hk := ZF.modelsKP hf
  simp only [sc_algebra_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, pair0_sat_l h.1, rd_graph_sat_l hk,
    sc_total0_sat_l h.1, fn0_sat_l h.1, Formula.satisfies_subset_iff]
  refine ⟨⟨KP.exists_pair hk, KP.exists_union hk, ?_, fun _ _ _ ht => sc_choice_graph_l h ht⟩,
    rd_fibers_exists_l hk⟩
  intro A B
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hf (kp_pair_l hk) A B
  exact ⟨P, fun t => (hp t).trans ⟨fun ⟨x, hx, y, hy, pair⟩ => ⟨x, y, hx, hy, pair⟩,
    fun ⟨x, y, hx, hy, pair⟩ => ⟨x, hx, y, hy, pair⟩⟩⟩

section Source
variable (hZF : M.Models ZF) {ω c X R : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Zc_model_d.theory_l (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (h : Zc_model_d I ω c X R) : Sc_theory_d I ω X R := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  let nx : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  refine ⟨fun E F n r i f D hE hF hr hi hf hD => ?_,
    (sc_algebra_sat_l (ZF.modelsKP hZF) hX nx ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩).mp
      (sc_algebra_models_l (h.membership_l I hZF hω hm nx) _)⟩
  obtain ⟨A, hA, sep⟩ := h.schemas.separation E F n r i f D hE hF hr hi hf hD
  exact ⟨A, hA, (ssep_relation_l I hX hm hD hA).mp sep⟩

theorem Zc_model_d.power_l (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (h : Zc_model_d I ω c X R) : Sc_power_d X := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  let nx : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  apply (sc_power_sat_l hX nx ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩).mp
  simp only [sc_power_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isPowerSet_iff]
  exact ZF.exists_powerSet (ZFC.models_zf_l (h.membership_l I hZF hω hm nx))

theorem Zc_model_d.collection_l (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (h : Zc_model_d I ω c X R) : Sc_collection_d I ω X R := by
  have theory := h.theory_l hZF hω hX hm
  intro D _ _ E F n r i j f A hE hF hr hi hj hij hf hA _ total
  have mem x y (hx : M.mem x X) (hy : M.mem y X) : M.PairMember I x y R ↔ M.mem x y :=
    (hm.2 x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
  obtain ⟨C, hC, bound⟩ := h.schemas.collection E F n r i j f A hE hF hr hi hj hij hf hA
    (fun x hx ha => total x ((mem x A hx hA).mp ha))
  obtain ⟨Q, hQ, _, graph⟩ := sc_binary_relation_l hZF hω hX hm theory hE hF hr hi hj hij hf hA hC
  obtain ⟨B, hB, fn, sub⟩ := theory.algebra.choice A C Q hA hC hQ (fun x hx => by
    obtain ⟨y, hy, hc, ht⟩ := bound x (hX A hA x hx) ((mem x A (hX A hA x hx) hA).mpr hx)
    exact ⟨y, (mem y C hy hC).mp hc, (graph x y).mpr ⟨hx, (mem y C hy hC).mp hc, ht⟩⟩)
  exact ⟨B, C, hB, hC, fn, fun x y ⟨p, pair, hp⟩ => ((graph x y).mp ⟨p, pair, sub p hp⟩).2.2⟩
end Source

end YesMetaZFC.SetTheory.Internal
