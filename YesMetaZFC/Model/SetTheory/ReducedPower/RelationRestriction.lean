import YesMetaZFC.Model.SetTheory.Relations.Small
import YesMetaZFC.Model.SetTheory.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize

/-! # 原关系代表的测度限制保持同一个商

两种原子的精确真值集在原关系源内分离，再沿实际坐标读到 P。
真实测度与其 P 限制因此具有相同的核和商关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_atom_trace_l {ω c X R c' Y S q D t P f g : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d F G : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P)
    (hf : ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val t →
      (Rd_entry_d s y.val f ↔ Rd_entry_d x y F))
    (hg : ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val t →
      (Rd_entry_d s y.val g ↔ Rd_entry_d x y G)) (k : Bool) :
    ∃ A, M.mem A P ∧ ∀ s, M.mem s A ↔ M.mem s D ∧ Rp_atom_d I k Y S f g s := by
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm model ex
  have en := ext.native_l I model.2.1
  let φ : UnarySchema 2 := {
    body := .existsE (.existsE (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4))
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
        (if k then Formula.extensionalEq (.bound 1) .newest else .mem (.bound 1) .newest))))
    freeClosed := by cases k <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  let ρ : Env (smdl_structure_l I (R := S) model.2.1) 2 := ⟨Fin.cases G (fun _ => F), fun _ => d⟩
  have read s (x : (smdl_structure_l I (R := S) model.2.1).Domain) (hsx : Rd_entry_d s x.val t) :
      φ.denote ρ x ↔ Rp_atom_d I k Y S f g s := by
    have native : φ.denote ρ x ↔ ∃ y z : (smdl_structure_l I (R := S) model.2.1).Domain,
        Rd_entry_d x y F ∧ Rd_entry_d x z G ∧ (if k then y = z else Rd_entry_d y.val z.val S) := by
      cases k <;> simp only [φ, UnarySchema.denote, Bool.false_eq_true, ↓reduceIte,
        Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l en,
        Formula.satisfies_extensionalEq_iff_eq en, Formula.satisfies_mem_iff] <;> rfl
    refine native.trans ⟨?_, ?_⟩
    · rintro ⟨y, z, hxy, hxz, rel⟩
      refine ⟨y.val, y.property, z.val, z.property, (hf s x y hsx).mpr hxy, (hg s x z hsx).mpr hxz, ?_⟩
      cases k
      · exact rel
      · exact congrArg Subtype.val rel
    · rintro ⟨y, hy, z, hz, hsy, hsz, rel⟩
      refine ⟨⟨y, hy⟩, ⟨z, hz⟩, (hf s x ⟨y, hy⟩ hsx).mp hsy, (hg s x ⟨z, hz⟩ hsx).mp hsz, ?_⟩
      cases k
      · exact rel
      · exact Subtype.ext rel
  obtain ⟨B, hB, sep⟩ := sc_separate_raw_l I hZF hω hm theory model hq φ ρ d
  obtain ⟨A, trace⟩ := rt_trace_exists_l I hZF D t S B
  refine ⟨A, (hP A).mpr ⟨B, hB, trace⟩, fun s => (trace s).trans ?_⟩
  apply and_congr_right
  intro hs
  obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
  refine ⟨fun ⟨y, hsy, hy⟩ => ?_, fun ha => ?_⟩
  · have eq := (fn0_function_l (ZF.modelsKP hZF) ft).1.2 s y x hsy hsx
    exact (read s ⟨x, hx⟩ hsx).mp ((sep ⟨x, hx⟩).mp (eq ▸ hy)).2
  · exact ⟨x, hsx, (sep ⟨x, hx⟩).mpr ⟨domain s x hsx, (read s ⟨x, hx⟩ hsx).mpr ha⟩⟩

theorem rc_restrict_model_l {ω c X R c' Y S q D t P U V o G p C T : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : Base_d D U)
    (upward : ∀ A B, M.mem A U → M.mem B P → M.MemberSubset A B → M.mem B U)
    (hv : ∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U)
    (hG : ∀ g, M.mem g G → ∃ f : (smdl_structure_l I (R := S) source.2.1).Domain,
      ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
        (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) : Rp_model_d I D Y V S o G p C T := by
  have transfer k f g (hf : M.mem f G) (hg : M.mem g G) :
      (∃ A, M.mem A U ∧ ∀ s, M.mem s A → Rp_atom_d I k Y S f g s) ↔
        ∃ A, M.mem A V ∧ ∀ s, M.mem s A → Rp_atom_d I k Y S f g s := by
    obtain ⟨F, hF⟩ := hG f hf
    obtain ⟨G, hG⟩ := hG g hg
    obtain ⟨A, hA, trace⟩ := rc_atom_trace_l hZF hω ex hm theory source hq d F G ft domain hP hF hG k
    refine ⟨fun ⟨B, hB, truth⟩ => ?_, fun ⟨B, hB, truth⟩ => ⟨B, ((hv B).mp hB).2, truth⟩⟩
    have large := upward B A hB hA
      (fun s hs => (trace s).mpr ⟨hU.bounds B hB s hs, truth s hs⟩)
    exact ⟨A, (hv A).mpr ⟨hA, large⟩, fun s hs => ((trace s).mp hs).2⟩
  exact rp_change_filter_l I model
    (fun f g hf hg => (rp_atom_eq_l I).symm.trans ((transfer true f g hf hg).trans (rp_atom_eq_l I)))
    (fun f g hf hg => transfer false f g hf hg)

end YesMetaZFC.SetTheory.Internal
