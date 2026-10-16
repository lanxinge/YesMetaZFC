import YesMetaZFC.Model.SetTheory.Internal.RelationRelative
import YesMetaZFC.SetTheory.Collapse.RelationIso

/-! # 关系模型内部函数的实际坐标图

输入坐标图逐点进入内部定义域；函数仍由关系模型中的原对象给出。
背景替换只展开它的值，不把全部背景函数充作源内代表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_extensional_l {c X R : M.Domain} (model : Smdl_d I c X R) (ext : Wc_ext_d X R) :
    Extensional (smdl_structure_l I (R := R) model.2.1) :=
  ⟨fun x y same => Subtype.ext (ext x.val x.property y.val y.property (fun z hz => same ⟨z, hz⟩))⟩

theorem smdl_function_l {c X R D t : M.Domain} (model : Smdl_d I c X R) (ext : Wc_ext_d X R)
    (d B f : (smdl_structure_l I (R := R) model.2.1).Domain)
    (function : Fn0_d d B f) (ft : Fn0_d D X t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val R) :
    ∃ g, Fn0_d D X g ∧ ∀ s (x y : (smdl_structure_l I (R := R) model.2.1).Domain),
      Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  let N := smdl_structure_l I (R := R) model.2.1
  have en := smdl_extensional_l hZF model ext
  let φ : Formula 1 3 := rd_entry0_m (.bound 1) .newest (.bound 2)
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
  let ρ : Env M 4 := ⟨Fin.cases f.val (Fin.cases t (Fin.cases R (fun _ => X))), fun _ => X⟩
  let ψ : BinarySchema 4 := {
    body := .conj (.mem .newest (.bound 5)) (Formula.existsMem (.bound 5)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
        (rr_rel_m kpair_convention_l φ (.bound 6) (.bound 5) (Fin.cases (.bound 1) (Fin.cases .newest (fun _ => .bound 3))))))
    freeClosed := by
      simp only [Formula.existsMem, Definitional.Formula.FreeClosed]
      exact ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, ⟨by simp -implicitDefEqProofs,
        rr_rel_closed_l kpair_convention_l φ closed _ _ _ rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))⟩⟩⟩ }
  have bound s y (h : ψ.denote ρ s y) : M.mem y X := (Formula.satisfies_conj_iff ..).mp h |>.1
  have sat s (y : N.Domain) : ψ.denote ρ s y.val ↔
      ∃ x : N.Domain, Rd_entry_d s x.val t ∧ Rd_entry_d x y f := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]
    have decode (x : N.Domain) := (rr_rel_sat_l I model.2.1 φ closed
      ⟨Fin.cases y (Fin.cases x (fun _ => f)), fun _ => f⟩ (((ρ.push s).push y.val).push x.val)
      (.bound 6) (.bound 5) (Fin.cases (.bound 1) (Fin.cases .newest (fun _ => .bound 3)))
      rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans (rd_entry0_sat_l en ..)
    exact ⟨fun ⟨_, x, hx, hsx, h⟩ => ⟨⟨x, hx⟩, hsx, (decode ⟨x, hx⟩).mp h⟩,
      fun ⟨x, hsx, h⟩ => ⟨y.property, x.val, x.property, hsx, (decode x).mpr h⟩⟩
  obtain ⟨g, fg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := D) (target := X)
    (fun s hs => by
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      obtain ⟨y, _, hxy⟩ := function.2.1 ⟨x, hx⟩ (domain s x hsx)
      exact ⟨y.val, (sat s y).mpr ⟨⟨x, hx⟩, hsx, hxy⟩⟩)
    (fun s _ y z hy hz => by
      obtain ⟨x, hsx, hxy⟩ := (sat s ⟨y, bound s y hy⟩).mp hy
      obtain ⟨x', hsx', hxz⟩ := (sat s ⟨z, bound s z hz⟩).mp hz
      have eq : x = x' := Subtype.ext ((fn0_function_l (ZF.modelsKP hZF) ft).1.2 s x.val x'.val hsx hsx')
      exact congrArg Subtype.val (function.2.2 x (domain s x.val hsx) _ (function.bound_l hxy).2
        _ (function.bound_l hxz).2 hxy (eq.symm ▸ hxz)))
    (fun s y _ h => bound s y h)
  refine ⟨g, fn0_of_function_l (ZF.modelsKP hZF) fg, ?_⟩
  intro s x y hsx
  refine (spec s y.val).trans ((and_congr_right fun _ => sat s y).trans ⟨?_, ?_⟩)
  · rintro ⟨_, x', hsx', h⟩
    have eq : x' = x := Subtype.ext ((fn0_function_l (ZF.modelsKP hZF) ft).1.2 s x'.val x.val hsx' hsx)
    exact eq ▸ h
  · exact fun h => ⟨(ft.bound_l hsx).1, x, hsx, h⟩

end YesMetaZFC.SetTheory.Internal
