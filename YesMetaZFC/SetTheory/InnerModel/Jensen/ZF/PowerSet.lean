import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Collection

/-! # J 内部的幂集

背景幂集的 J 部分先取得层界，再在 J 内以有界子集公式分离。
得到的成员规格遍历 J 的对象域，准确表达 J 自身的全部子集。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem l_model_power_l (hZF : M.Models ZF)
    (X : (l_model_l (ZF.models_kpi_l hZF)).Domain) :
    ∃ P : (l_model_l (ZF.models_kpi_l hZF)).Domain,
      (l_model_l (ZF.models_kpi_l hZF)).IsPowerSetOf P X := by
  let hM := ZF.models_kpi_l hZF
  let N := l_model_l hM
  have sub (x : N.Domain) : N.MemberSubset x X ↔ M.MemberSubset x.val X.val :=
    ⟨fun h y hy => h ⟨y, l_transitive_l hM x.property hy⟩ hy, fun h y hy => h y.val hy⟩
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X.val
  obtain ⟨D, hd⟩ := jl_trace_l hZF P
  obtain ⟨a, U, ha, hu⟩ := l_bound_l hM (fun x hx => ((hd x).mp hx).2)
  let W : N.Domain := ⟨U, l_layer_l hM ha⟩
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  let ρ := rd_seed_env_l (M := N) X
  obtain ⟨Q, hq⟩ := l_model_separation_l hM φ ρ W
  have hq' (x : N.Domain) : N.mem x Q ↔ N.mem x W ∧ N.MemberSubset x X :=
    (hq x).trans (and_congr_right fun _ => Formula.satisfies_subset_iff _ _ _)
  exact ⟨Q, fun x => (hq' x).trans ⟨And.right,
    fun hx => ⟨hu x.val ((hd x.val).mpr ⟨(hp x.val).mpr ((sub x).mp hx), x.property⟩), hx⟩⟩⟩

end YesMetaZFC.SetTheory.InnerModel
