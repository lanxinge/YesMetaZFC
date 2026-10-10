import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 严格极限秩段中的原有秩历史

较早层及其整张历史都由有界关系闭包回收。历史的容器改用该层自身，
逐层方程保持不变；只要求给定的两份实际秩证书，不要求源具备全层级。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 较早层的历史可从秩段回到原源：反向幂集见证由原秩证书自动回收。 -/
theorem Vr_d.of_rank_l (hZF : M.Models ZF) {Z α V β W : M.Domain}
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (hv : Vr_d Z α V)
    (hW : M.mem W V) (hw : Vr_d V β W) : Vr_d Z β W := by
  have ht := hv.transitive_l hZF hZ hV
  obtain ⟨B, F, hB, hF, cert⟩ := hw
  have step {δ U} (hU : M.mem U V) (eq : ∀ t, M.mem t V → Vc_step_d δ B F U t)
      t (h : M.mem t Z) : Vc_step_d δ B F U t := by
    refine ⟨fun hu => (eq t (ht U hU t hu)).mp hu, fun hs => ?_⟩
    obtain ⟨γ, hγ, T, hT, hg, sub⟩ := hs
    exact (eq t (hv.subset_mem_l hZ hV (ht B hB T hT) h sub)).mpr ⟨γ, hγ, T, hT, hg, sub⟩
  refine ⟨B, F, hZ V hV B hB, hZ V hV F hF, fun t ht =>
    ⟨(cert W hW).1, (cert W hW).2.1, ?_, step hW (fun t ht => (cert t ht).2.2.2) t ht⟩⟩
  intro δ hδ U hU hu
  exact step (hv.transitive_l hZF hZ hV B hB U hU) (fun t ht => (cert t ht).2.2.1 δ hδ U hU hu) t ht

theorem Vr_d.rank_l (hZF : M.Models ZF) {Z α V β W : M.Domain}
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α)
    (hβ : M.mem β V) (hW : M.mem W Z) (hw : Vr_d Z β W) : M.mem W V ∧ Vr_d V β W := by
  have ho : M.IsOrdinal β := by obtain ⟨_, _, _, _, cert⟩ := hw; exact (cert W hW).1
  have hβα := hv.ordinal_height_l hZF hZ hV ho hβ
  have hWV := (hv.compare_l hZF hZ hV hW hw (hα.1.transitive β hβα)).2 hβα
  obtain ⟨B, F, hB, hF, cert⟩ := hw
  have fn := (cert W hW).2.1
  have range δ U (hu : Rd_entry_d δ U F) : M.mem U W :=
    ((cert U (hZ B hB U (fn.bound_l hu).2)).2.2.2).mpr
      ⟨δ, (fn.bound_l hu).1, U, (fn.bound_l hu).2, hu, fun _ h => h⟩
  have fw := fn.retarget_l range
  have hFV := hv.relation_mem_l hZF hZ hV hα hβ hWV hF fw.1
  refine ⟨hWV, W, F, hWV, hFV, fun t ht => ⟨ho, fw, ?_, ?_⟩⟩
  · intro δ hδ U _ hu
    exact ((cert t (hZ V hV t ht)).2.2.1 δ hδ U (fn.bound_l hu).2 hu).trans
      ⟨fun ⟨γ, hγ, T, _, hg, sub⟩ => ⟨γ, hγ, T, range γ T hg, hg, sub⟩,
        fun ⟨γ, hγ, T, _, hg, sub⟩ => ⟨γ, hγ, T, (fn.bound_l hg).2, hg, sub⟩⟩
  · exact ((cert t (hZ V hV t ht)).2.2.2).trans
      ⟨fun ⟨γ, hγ, T, _, hg, sub⟩ => ⟨γ, hγ, T, range γ T hg, hg, sub⟩,
        fun ⟨γ, hγ, T, _, hg, sub⟩ => ⟨γ, hγ, T, (fn.bound_l hg).2, hg, sub⟩⟩

end YesMetaZFC.SetTheory
