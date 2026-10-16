import YesMetaZFC.Model.SetTheory.Internal.RelationFunction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

/-! # 原始关系模型拥有的全部函数代表

实际函数空间中只保留能由模型内函数码逐点读出的图。分离给出这一个集合，
上一节的坐标展开保证每个内部函数都有代表，随后原商构造直接使用该集合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_function_family_l {c X R D t : M.Domain} (model : Smdl_d I c X R) (ext : Wc_ext_d X R)
    (d : (smdl_structure_l I (R := R) model.2.1).Domain) (ft : Fn0_d D X t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val R) :
    ∃ G, (∀ g, M.mem g G ↔ Fn0_d D X g ∧
      ∃ B f : (smdl_structure_l I (R := R) model.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := R) model.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ∧
      ∀ B f : (smdl_structure_l I (R := R) model.2.1).Domain, Fn0_d d B f →
        ∃ g, M.mem g G ∧ ∀ s (x y : (smdl_structure_l I (R := R) model.2.1).Domain),
          Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  let N := smdl_structure_l I (R := R) model.2.1
  have en := smdl_extensional_l hZF model ext
  let φ : Formula 1 3 := fn0_m (.bound 2) (.bound 1) .newest
  let χ : Formula 1 3 := rd_entry0_m (.bound 1) .newest (.bound 2)
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
  have closed' : χ.FreeClosed := by simp -implicitDefEqProofs [χ]
  let ρ : Env M 5 := ⟨Fin.cases t (Fin.cases D (Fin.cases d.val (Fin.cases R (fun _ => X)))), fun _ => X⟩
  let ψ : UnarySchema 5 := {
    body := Formula.existsMem (.bound 5) (Formula.existsMem (.bound 6)
      (.conj (rr_rel_m kpair_convention_l φ (.bound 7) (.bound 6) (Fin.cases .newest (Fin.cases (.bound 1) (fun _ => .bound 5))))
        (Formula.forallMem (.bound 4) (Formula.forallMem (.bound 8) (Formula.forallMem (.bound 9)
          (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 6))
            (.iff (rd_entry0_m (.bound 2) .newest (.bound 5))
              (rr_rel_m kpair_convention_l χ (.bound 10) (.bound 9) (Fin.cases .newest (Fin.cases (.bound 1) (fun _ => .bound 3)))))))))))
    freeClosed := by
      simp only [Formula.existsMem, Formula.forallMem, Definitional.Formula.FreeClosed]
      refine ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, ⟨?_, ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩,
        ⟨⟨rfl, rfl⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩⟩⟩⟩
      · exact rr_rel_closed_l kpair_convention_l φ closed _ _ _ rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      · simp -implicitDefEqProofs
      · simp -implicitDefEqProofs
      · exact rr_rel_closed_l kpair_convention_l χ closed' _ _ _ rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) }
  have sat g : ψ.denote ρ g ↔ ∃ B f : N.Domain, Fn0_d d B f ∧
      ∀ s (x y : N.Domain), Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1]
    have fn (B f : N.Domain) := (rr_rel_sat_l I model.2.1 φ closed
      ⟨Fin.cases f (Fin.cases B (fun _ => d)), fun _ => d⟩ (((ρ.push g).push B.val).push f.val)
      (.bound 7) (.bound 6) (Fin.cases .newest (Fin.cases (.bound 1) (fun _ => .bound 5)))
      rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans (fn0_sat_l en ..)
    have value (B f : N.Domain) s (x y : N.Domain) := (rr_rel_sat_l I model.2.1 χ closed'
      ⟨Fin.cases y (Fin.cases x (fun _ => f)), fun _ => f⟩ ((((((ρ.push g).push B.val).push f.val).push s).push x.val).push y.val)
      (.bound 10) (.bound 9) (Fin.cases .newest (Fin.cases (.bound 1) (fun _ => .bound 3)))
      rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans (rd_entry0_sat_l en ..)
    constructor
    · rintro ⟨B, hB, f, hf, hfn, h⟩
      exact ⟨⟨B, hB⟩, ⟨f, hf⟩, (fn ⟨B, hB⟩ ⟨f, hf⟩).mp hfn, fun s x y hsx =>
        (h s (ft.bound_l hsx).1 x.val x.property y.val y.property hsx).trans (value ⟨B, hB⟩ ⟨f, hf⟩ s x y)⟩
    · rintro ⟨B, f, hfn, h⟩
      exact ⟨B.val, B.property, f.val, f.property, (fn B f).mpr hfn,
        fun s _ x hx y hy hsx => (h s ⟨x, hx⟩ ⟨y, hy⟩ hsx).trans (value B f s ⟨x, hx⟩ ⟨y, hy⟩).symm⟩
  obtain ⟨A, space⟩ := ZF.exists_functionSpace hZF I D X
  obtain ⟨G, gs⟩ := ZF.separation_exists_d hZF ψ ρ A
  have spec g := (gs g).trans (and_congr ((space g).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩) (sat g))
  refine ⟨G, spec, fun B f hfn => ?_⟩
  obtain ⟨g, fg, eval⟩ := smdl_function_l hZF model ext d B f hfn ft domain
  exact ⟨g, (spec g).mpr ⟨fg, B, f, hfn, eval⟩, eval⟩

end YesMetaZFC.SetTheory.Internal
