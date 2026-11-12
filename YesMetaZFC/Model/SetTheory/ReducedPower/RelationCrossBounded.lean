import YesMetaZFC.Model.SetTheory.Relations.CrossCapture
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize

/-! # 原关系共同切片中的全部有界代表

当前源的有界代表先恢复其原函数码，再展开该原函数的对象码图。
该图与共同切片实现的实际复合恰好是原代表；反向也覆盖每个原函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_cross_functions_l {N T Γ Y S H k D t G : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y Y)
    (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (ey : Extensional (smdl_structure_l I (R := S) ny))
    (U d a p : (smdl_structure_l I (R := T) nx).Domain)
    (trans : (smdl_structure_l I (R := T) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y S ↔ ∃ b, Rd_entry_d b x T ∧ Rd_entry_d b z k)
    (closed : Rr_closed_d I Y S H)
    (hp : (smdl_structure_l I (R := T) nx).mem p U)
    (product : (smdl_structure_l I (R := T) nx).IsCartesianProduct (kp_pair_l hN) p d a)
    (d' a' : (smdl_structure_l I (R := S) ny).Domain)
    (hd : Rd_entry_d d.val d'.val k) (ha : Rd_entry_d a.val a'.val k)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (rt : M.IsRestrictionOf I t k D)
    (family : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d' B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) :
    ∀ g, (M.mem g G ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a'.val S) ↔
      ∃ f : (smdl_structure_l I (R := T) nx).Domain, ∃ F,
        (smdl_structure_l I (R := T) nx).mem f U ∧ Fn0_d d a f ∧ Fn0_d D Γ F ∧
        (∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) ∧
        Cp0_d D Γ Y F k g := by
  let N₀ := smdl_structure_l I (R := T) nx
  let Y₀ := smdl_structure_l I (R := S) ny
  have hdU : N₀.mem d U := ((carrier d.val).mp (fk.1.input_mem_of_pairMember hd)).2
  have haU : N₀.mem a U := ((carrier a.val).mp (fk.1.input_mem_of_pairMember ha)).2
  have inside x (hx : M.mem x D) : M.mem x Γ :=
    (carrier x).mpr ⟨((dc x).mp hx).1, trans d hdU ⟨x, ((dc x).mp hx).1⟩ ((dc x).mp hx).2⟩
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (rt.isSetFunctionFromTo fk.1 inside)
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have exchange (f : N₀.Domain) (f' : Y₀.Domain) (hf : Rd_entry_d f.val f'.val k) (fn : Fn0_d d a f)
      {F g : M.Domain} (fF : Fn0_d D Γ F)
      (graph : ∀ s v : N₀.Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) (fg : Fn0_d D Y g) :
      (∀ s (x y : Y₀.Domain), Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f')) ↔
        Cp0_d D Γ Y F k g := by
    have moved := rr_native_function_l I nx ny hN.1 ey U trans carrier fk pred d a f d' a' f' hd ha hf fn
    have point s v y x (hsv : Rd_entry_d s v F) (hvy : Rd_entry_d v y k) (hsx : Rd_entry_d s x t) :
        Rd_entry_d (⟨x, (ft.bound_l hsx).2⟩ : Y₀.Domain) (⟨y, fk.1.output_mem_of_pairMember hvy⟩ : Y₀.Domain) f' := by
      let s' : N₀.Domain := ⟨s, ((dc s).mp (fF.bound_l hsv).1).1⟩
      let v' : N₀.Domain := ⟨v, ((carrier v).mp (fF.bound_l hsv).2).1⟩
      exact (moved.2 s' v' ⟨x, (ft.bound_l hsx).2⟩ ⟨y, fk.1.output_mem_of_pairMember hvy⟩
        ((rt.2 s x).mp hsx).2 hvy).mp ((graph s' v').mp hsv)
    constructor
    · intro decode
      refine ⟨fg, fun s hs => ?_⟩
      obtain ⟨v, hv, hsv⟩ := fF.2.1 s hs
      obtain ⟨y, hy, hvy⟩ := fk.1.2.2 v hv
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      exact ⟨v, hv, y, hy, hsv, hvy, (decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr (point s v y x hsv hvy hsx)⟩
    · intro comp s x y hsx
      obtain ⟨v, hv, hsv⟩ := fF.2.1 s (ft.bound_l hsx).1
      obtain ⟨z, hz, hvz⟩ := fk.1.2.2 v hv
      have value := point s v z x.val hsv hvz hsx
      have read := (comp.value_l fF key hsv).mpr hvz
      constructor
      · intro h
        have eq : (⟨z, hz⟩ : Y₀.Domain) = y := Subtype.ext
          (fg.2.2 s (ft.bound_l hsx).1 z hz y.val y.property read h)
        exact eq ▸ value
      · intro h
        exact congrArg (fun u : Y₀.Domain => u.val)
          (moved.1.2.2 x (moved.1.bound_l h).1 ⟨z, hz⟩ (moved.1.bound_l value).2
            y (moved.1.bound_l h).2 value h) ▸ read
  intro g
  constructor
  · rintro ⟨hg, bounded⟩
    obtain ⟨fg, B, f', fn', decode⟩ := (family g).mp hg
    have fn : Fn0_d d' a' f' := fn'.retarget_l (fun x y hxy => by
      obtain ⟨s, hs, hsx⟩ := (pred d.val d'.val hd x.val).mp (fn'.bound_l hxy).1
      have hsD := (dc s).mpr ⟨((carrier s).mp (fk.1.input_mem_of_pairMember hsx)).1, hs⟩
      exact bounded s y.val ((decode s x y ((rt.2 s x.val).mpr ⟨hsD, hsx⟩)).mpr hxy))
    obtain ⟨f, hf, hff, fn⟩ := rr_cross_capture_l I nx ny hN ey U d a p trans carrier fk image pred closed hp product d' a' f' hd ha fn
    obtain ⟨D', A, F, dc', ac, fF, graph⟩ := smdl_graph_l hZF nx hN.1 d a f fn
    have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
    subst D'
    have fF := fF.mono_target_l (fun v hv => (carrier v).mpr ⟨((ac v).mp hv).1,
      trans a haU ⟨v, ((ac v).mp hv).1⟩ ((ac v).mp hv).2⟩)
    exact ⟨f, F, hf, fn, fF, graph, (exchange f f' hff fn fF graph fg).mp decode⟩
  · rintro ⟨f, F, hf, fn, fF, graph, comp⟩
    obtain ⟨v, hv, hfv⟩ := fk.1.2.2 f.val ((carrier f.val).mpr ⟨f.property, hf⟩)
    let f' : Y₀.Domain := ⟨v, hv⟩
    have moved := rr_native_function_l I nx ny hN.1 ey U trans carrier fk pred d a f d' a' f' hd ha hfv fn
    refine ⟨(family g).mpr ⟨comp.1, a', f', moved.1, (exchange f f' hfv fn fF graph comp.1).mpr comp⟩, ?_⟩
    intro s y hsy
    obtain ⟨v, hv, hsv⟩ := fF.2.1 s (comp.1.bound_l hsy).1
    let s' : N₀.Domain := ⟨s, ((dc s).mp (fF.bound_l hsv).1).1⟩
    let v' : N₀.Domain := ⟨v, ((carrier v).mp hv).1⟩
    exact (pred a.val a'.val ha y).mpr ⟨v, (fn.bound_l ((graph s' v').mp hsv)).2,
      (comp.value_l fF key hsv).mp hsy⟩

end YesMetaZFC.SetTheory.Internal
