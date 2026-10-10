import YesMetaZFC.SetTheory.InnerModel.Separation.Family

/-! # Def(U) 的有限基构造

任意原公式在传递集合 U 内定义的子集，都由其真值表和参数纤维取得。
公式可以有任意量词复杂度；不假定 U 满足 KP 或收集。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rt_definable_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hUC : M.MemberSubset U C) (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) {n} (φ : UnarySchema n) (ρ : Env (rt_model_l U hn) n) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ ∃ hx : M.mem x U, φ.denote ρ ⟨x, hx⟩ := by
  obtain ⟨d, hd⟩ := (show ∃ d, M.mem d U from hn.elim fun x => ⟨x.val, x.property⟩)
  let d' : (rt_model_l U hn).Domain := ⟨d, hd⟩
  let e : Rt_env U n := fun i => if h : i.val < n then ρ.bound ⟨i.val, h⟩ else d'
  have he i : e i.castSucc = ρ.bound i := by
    change (if h : i.val < n then ρ.bound ⟨i.val, h⟩ else d') = _
    rw [dif_pos i.isLt]
  obtain ⟨R, hRC, hR⟩ := rt_formula_l hKP hC hU hu hn φ.body φ.freeClosed Fin.castSucc
  obtain ⟨q, hqC, hq⟩ := rt_tuple_closed_l hKP hC (fun i => (e i).val) (fun i => hUC _ (e i).property)
  obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .fiber hRC hqC hqC
  refine ⟨Y, hYC, fun x => ((hR.fiber_l hKP e hq).mp hY x).trans ?_⟩
  apply exists_congr; intro hx
  apply Formula.closed_env_l _ φ.freeClosed
  exact funext (Fin.cases rfl he)

end YesMetaZFC.SetTheory.InnerModel
