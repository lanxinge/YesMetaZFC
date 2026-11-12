import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 原关系共同切片上的实际函数投影

所属函数先展开成对象码之间的背景图，再经完整前驱实现送到施加源。
同一个图同时给出两个定义域坐标之间的交换方程，供分量初等过渡使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_cross_projection_l {N R Γ Y S k D E u v : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ x, M.mem x Y)
    (en : Extensional (smdl_structure_l I (R := R) nx))
    (ey : Extensional (smdl_structure_l I (R := S) ny))
    (U d e p : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val R)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a z k)
    (hp : (smdl_structure_l I (R := R) nx).mem p U) (fn : Fn0_d e d p)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val R)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val R)
    (ru : M.IsRestrictionOf I u k D) (rv : M.IsRestrictionOf I v k E)
    (d' e' : (smdl_structure_l I (R := S) ny).Domain)
    (hdd : Rd_entry_d d.val d'.val k) (hee : Rd_entry_d e.val e'.val k) :
    ∃ t, Fn0_d E D t ∧
      (∀ x y : (smdl_structure_l I (R := R) nx).Domain, Rd_entry_d x.val y.val t ↔ Rd_entry_d x y p) ∧
      ∃ p' : (smdl_structure_l I (R := S) ny).Domain, Rd_entry_d p.val p'.val k ∧ Fn0_d e' d' p' ∧
        ∀ s r x y, Rd_entry_d s r t → Rd_entry_d s x v → Rd_entry_d r y u → Rf_val_d I Y S x y p'.val := by
  let N₀ := smdl_structure_l I (R := R) nx
  let Y₀ := smdl_structure_l I (R := S) ny
  obtain ⟨E₀, D₀, t, ec₀, dc₀, ft, graph⟩ := smdl_graph_l hZF nx en e d p fn
  have eq := hZF.1.eq_of_same_members E₀ E (fun x => (ec₀ x).trans (ec x).symm)
  subst E₀
  have eq := hZF.1.eq_of_same_members D₀ D (fun x => (dc₀ x).trans (dc x).symm)
  subst D₀
  obtain ⟨P, hP, hpP⟩ := fk.1.2.2 p.val ((carrier p.val).mpr ⟨p.property, hp⟩)
  let p' : Y₀.Domain := ⟨P, hP⟩
  have moved := rr_native_function_l I nx ny en ey U trans carrier fk pred e d p e' d' p' hee hdd hpP fn
  refine ⟨t, ft, graph, p', hpP, moved.1, fun s r x y hsr hsx hry => ?_⟩
  let s' : N₀.Domain := ⟨s, ((ec s).mp (ft.bound_l hsr).1).1⟩
  let r' : N₀.Domain := ⟨r, ((dc r).mp (ft.bound_l hsr).2).1⟩
  have hsx := ((rv.2 s x).mp hsx).2
  have hry := ((ru.2 r y).mp hry).2
  let x' : Y₀.Domain := ⟨x, fk.1.output_mem_of_pairMember hsx⟩
  let y' : Y₀.Domain := ⟨y, fk.1.output_mem_of_pairMember hry⟩
  exact (rf_val_native_l I ny ey x' y' p').mpr ((moved.2 s' r' x' y' hsx hry).mp ((graph s' r').mp hsr))

end YesMetaZFC.SetTheory.Internal
