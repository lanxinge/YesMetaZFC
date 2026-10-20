import YesMetaZFC.Model.SetTheory.Internal.RelationRealization
import YesMetaZFC.Model.SetTheory.Internal.RelationSubset
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax

/-! # 共同低层回收原关系的有界函数码

乘积的有界规格先识别全部原关系有序对，再把新函数码作为乘积的子集
回收到同一低层。所得背景函数是真正属于所属源的图，而非外部任取的函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_realize_product_l {Γ Y S k D A P : M.Domain}
    (hΓ : M.TransitiveSet Γ) (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, Rd_entry_d x a k → ∀ b, Rd_entry_d b a S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y b k)
    (d a p : (smdl_structure_l I (R := S) ny).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k) (hP : Rd_entry_d P p.val k)
    (product : M.IsCartesianProduct I P D A) :
    ∀ z : (smdl_structure_l I (R := S) ny).Domain,
      Rd_entry_d z.val p.val S ↔ ∃ x, Rd_entry_d x.val d.val S ∧ ∃ y, Rd_entry_d y.val a.val S ∧
        KPair_d (smdl_structure_l I (R := S) ny) z x y := by
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨D, fk.1.input_mem_of_pairMember hD⟩⟩
  let ρ : Env (rt_model_l Γ nx) 3 := ⟨Fin.cases ⟨P, fk.1.input_mem_of_pairMember hP⟩
    (Fin.cases ⟨A, fk.1.input_mem_of_pairMember hA⟩ (fun _ => ⟨D, fk.1.input_mem_of_pairMember hD⟩)),
      fun _ => ⟨D, fk.1.input_mem_of_pairMember hD⟩⟩
  let η : Env (smdl_structure_l I (R := S) ny) 3 := ⟨Fin.cases p (Fin.cases a (fun _ => d)), fun _ => d⟩
  have en := ext.native_l I ny
  have transfer := rr_realize_delta_l I hΓ nx ny fk pred (sh_product_m .newest (.bound 2) (.bound 1))
    (by simp -implicitDefEqProofs) (sh_product_delta_l ..) ρ η (Fin.cases hP (Fin.cases hA (fun _ => hD)))
  have moved := transfer.mp ((sh_product_sat_l (ZF.modelsKP hZF) ..).mpr product)
  simp only [sh_product_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l en] at moved
  intro z
  refine ⟨moved.1 z, ?_⟩
  rintro ⟨x, hx, y, hy, pair⟩
  obtain ⟨w, hw, code⟩ := moved.2 x hx y hy
  exact kpair_unique_l _ en code pair ▸ hw

theorem rr_capture_function_l {Y S H Γ k D A P : M.Domain}
    (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S) (closed : Rr_closed_d I Y S H)
    (hΓ : M.TransitiveSet Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ a, Rd_entry_d a H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x a k)
    (pred : ∀ x a, Rd_entry_d x a k → ∀ b, Rd_entry_d b a S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y b k)
    (d a f : (smdl_structure_l I (R := S) ny).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k)
    (hP : M.mem P Γ) (product : M.IsCartesianProduct I P D A) (fn : Fn0_d d a f) :
    ∃ F, M.mem F Γ ∧ Rd_entry_d F f.val k ∧ Fn0_d D A F := by
  obtain ⟨p, hp, hPp⟩ := fk.1.2.2 P hP
  have prod := rr_realize_product_l hZF hΓ ny ext fk pred d a ⟨p, hp⟩ hD hA hPp product
  obtain ⟨F, hF, hFf, _⟩ := rr_capture_l I closed hΓ fk image pred hPp f.property
    (fun z hz hzf => (prod ⟨z, hz⟩).mpr (fn.1 ⟨z, hz⟩ hzf))
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨F, hF⟩⟩
  have transfer := rr_realize_delta_l I hΓ nx ny fk pred (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨A, fk.1.input_mem_of_pairMember hA⟩
      (fun _ => ⟨D, fk.1.input_mem_of_pairMember hD⟩)), fun _ => ⟨F, hF⟩⟩ : Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases f (Fin.cases a (fun _ => d)), fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 3)
    (Fin.cases hFf (Fin.cases hA (fun _ => hD)))
  exact ⟨F, hF, hFf, (fn0_sat_l hZF.1 ..).mp (transfer.mpr ((fn0_sat_l (ext.native_l I ny) ..).mpr fn))⟩

end YesMetaZFC.SetTheory.Internal
