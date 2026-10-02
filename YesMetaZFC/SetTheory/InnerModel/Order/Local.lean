import YesMetaZFC.SetTheory.InnerModel.Order.Sigma1
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded
import YesMetaZFC.SetTheory.InnerModel.Separation.Enclosure

/-! # 参数与关系表的局部封闭性

传递界在原闭包内逐个构造并有限合并；随后对实际关系公式进行有界分离。
输出关系也有闭包内传递界，因此可以继续充当下一步规范扩张的参数。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rw_rel_enclosed_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    {n} (φ : Delta0BinarySchema n) (ρ : Env M n)
    (hρ : ∀ i, ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem (ρ.bound i) T)
    {X S : M.Domain} (hX : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem X T)
    (hs : Rw_rel_d (φ.toBinarySchema.denote ρ) X S) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem S T := by
  obtain ⟨A, hAC, ha, hXA⟩ := hX
  have hXC := hc A hAC X hXA
  obtain ⟨P, hPC, hp⟩ := hC.exists_l hKP .prod hXC hXC hXC
  obtain ⟨B, hBC, hb, hPB⟩ := rd_relation_enclosed_l hKP hC hAC ha hPC (by
    intro p hpP
    obtain ⟨x, y, hx, hy, he⟩ := (hp p).mp hpP
    exact ⟨x, y, ha X hXA x hx, ha X hXA y hy, he⟩)
  let η := ρ.push X
  obtain ⟨T, hTC, ht, bt, hη⟩ := rd_finite_enclosed_l hKP hC hBC hb (List.ofFn η.bound) (by
    intro a hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact Fin.cases ⟨A, hAC, ha, hXA⟩ hρ i)
  obtain ⟨Y, hYC, hy⟩ := rd_separation_l hKP hC hc hTC ht (rw_slice_s φ) η
    (fun i => hη _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) (bt P hPB)
  have hy' : Rw_rel_d (φ.toBinarySchema.denote ρ) X Y := by
    intro p
    rw [hy p]
    change (M.mem p P ∧ Formula.satisfies ((ρ.push X).push p) (rw_slice_s φ).body) ↔ _
    rw [rw_slice_sat_l hKP.1]
    exact ⟨And.right, fun h => ⟨h.elim (fun x hx => hx.2.elim
      (fun y hy => (hp p).mpr ⟨x, y, hx.1, hy.1, hy.2.1⟩)), h⟩⟩
  have he := hy'.unique_l hKP.1 hs
  subst Y
  obtain ⟨V, hVC, hv, _, hSV⟩ := rd_bounded_enclosed_l hKP hC hTC ht hYC
    (fun p hpS => ht P (bt P hPB) p ((hy p).mp hpS).1)
  exact ⟨V, hVC, hv, hSV⟩

theorem rw_domain_closed_l (hKP : M.Models KP) {C U P : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hp : Rw_domain_d U P) : M.mem P C := by
  obtain ⟨A, hAC, ha⟩ := hC.exists_l hKP .prod hU hU hU
  obtain ⟨B, hBC, hb⟩ := hC.exists_l hKP .prod hU hAC hU
  have he : B = P := by
    apply hKP.1.eq_of_same_members; intro p
    rw [hb p, hp p]
    constructor
    · rintro ⟨a, q, haU, hqA, hpq⟩
      obtain ⟨b, c, hbU, hcU, hq⟩ := (ha q).mp hqA
      exact ⟨a, haU, b, hbU, c, hcU, q, hq, hpq⟩
    · rintro ⟨a, haU, b, hbU, c, hcU, q, hq, hpq⟩
      exact ⟨a, q, haU, (ha q).mpr ⟨b, c, hbU, hcU, hq⟩, hpq⟩
  exact he ▸ hBC

theorem rw_image_enclosed_l (hKP : M.Models KP) {C U P Y : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (k : Rd_sym) (hp : Rw_domain_d U P) (hy : Rw_image_d k U P Y) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem Y T := by
  obtain ⟨A, hAC, ha⟩ := rd_family_image_l hKP hC hU hu k
  have values x : (∃ p, M.mem p P ∧ Rw_fun_d k U p x) ↔
      ∃ a b c, M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c x := by
    constructor
    · rintro ⟨_, _, a, ha, b, hb, c, hc, _, h⟩; exact ⟨a, b, c, ha, hb, hc, h⟩
    · rintro ⟨a, b, c, ha, hb, hc, h⟩
      obtain ⟨q, hq⟩ := (kp_pair_l hKP).total b c
      obtain ⟨p, hpq⟩ := (kp_pair_l hKP).total a q
      exact ⟨p, (hp p).mpr ⟨a, ha, b, hb, c, hc, q, hq, hpq⟩, a, ha, b, hb, c, hc, ⟨q, hq, hpq⟩, h⟩
  have he : A = Y := hKP.1.eq_of_same_members _ _ fun x => (ha x).trans ((hy x).trans (values x)).symm
  subst A
  obtain ⟨V, hv⟩ := rd_step_exists_l hKP U
  obtain ⟨T, hTC, ht, _, hYT⟩ := rd_bounded_enclosed_l hKP hC (rd_step_closed_l hKP hC hU hu hv)
    (rd_step_transitive_l hKP.1 hu hv) hAC (by
      intro x hx
      obtain ⟨a, b, c, ha, hb, hc, h⟩ := (values x).mp ((hy x).mp hx)
      exact (hv x).mpr (Or.inr ⟨k, a, b, c, ha, hb, hc, h⟩))
  exact ⟨T, hTC, ht, hYT⟩

end YesMetaZFC.SetTheory.InnerModel
