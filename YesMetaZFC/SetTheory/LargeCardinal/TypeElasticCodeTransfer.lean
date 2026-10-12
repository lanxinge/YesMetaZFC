import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticProgramSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeProgramReflect

/-! # 同一伸展名字列在传递证书层之间搬运

全部存在见证都是原查询列及其实际坐标；只使用传递性和有界绝对性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hE hX

theorem ee_stretch_code_source_l {d} (ρ : Env N d) (ω n κ v d₀ e z p : Term d)
    (valid : Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p)) :
    Ee_stretch_code_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (v.eval ρ).val
      (d₀.eval ρ).val (e.eval ρ).val (z.eval ρ).val (p.eval ρ).val := by
  simp only [ee_stretch_code_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨C, kw, kn, kk, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (ee_stretch_code_m ω n κ v d₀ e z p) := by
    simp only [ee_stretch_code_m, Formula.satisfies_exists_iff]
    exact ⟨C.val, kw.val, kn.val, kk.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (ee_stretch_code_sat_l hE _ _ _ _ _ _ _ _ _).mp full

theorem ee_stretch_code_reflect_l {d} (ρ : Env N d) (ω n κ v d₀ e z p : Term d)
    (code : Ee_stretch_code_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (v.eval ρ).val
      (d₀.eval ρ).val (e.eval ρ).val (z.eval ρ).val (p.eval ρ).val) :
    Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p) := by
  obtain ⟨C, kw, kn, kk, pair, hw, hn, hk, old, ew, en, ed, ek⟩ := code
  have hC := (pair.mem_l M hX (p.eval ρ).property).2
  let c₀ : (N).Domain := ⟨C, hC⟩
  let w₀ : (N).Domain := ⟨kw, (rd_entry_transitive_l hX hC ew).2⟩
  let n₀ : (N).Domain := ⟨kn, (rd_entry_transitive_l hX hC en).2⟩
  let k₀ : (N).Domain := ⟨kk, (rd_entry_transitive_l hX hC ek).2⟩
  simp only [ee_stretch_code_m, Formula.satisfies_exists_iff]
  refine ⟨c₀, w₀, n₀, k₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, kpair0_sat_l hE, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨pair, hw, hn, hk, old, ew, en, ed, ek⟩

end YesMetaZFC.SetTheory.LargeCardinal
