import YesMetaZFC.SetTheory.InnerModel.Relative.Class
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 相对 J 并类的实际结构与基础封闭性 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def la_model_l (hM : M.Models KPi) : Structure.{u} where
  Domain := {x : M.Domain // La_d S x}
  nonempty := ⟨⟨S, la_seed_l S hM⟩⟩
  mem x y := M.mem x.val y.val

theorem la_model_ext_l (hM : M.Models KPi) (hS : M.TransitiveSet S) : Extensional (la_model_l S hM) := by
  refine ⟨fun a b h => Subtype.ext ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members a.val b.val (fun x => ?_))⟩
  exact ⟨fun hx => (h ⟨x, la_transitive_l S hM hS a.property hx⟩).mp hx,
    fun hx => (h ⟨x, la_transitive_l S hM hS b.property hx⟩).mpr hx⟩

theorem la_model_delta_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} {φ : Formula 1 n} (hφ : φ.IsDelta0)
    (ρ : Env (la_model_l S hM) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l (M := la_model_l S hM) (N := M) Subtype.val ρ) φ :=
  delta0_image_l (M := la_model_l S hM) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun a y => ⟨fun h => ⟨⟨y, la_transitive_l S hM hS a.property h⟩, h, rfl⟩,
      fun ⟨_, hx, he⟩ => he ▸ hx⟩) hφ ρ

theorem la_closed_l (hM : M.Models KPi) (k : Rd_sym) {a b c t}
    (ha : La_d S a) (hb : La_d S b) (hc : La_d S c) (ht : Rd_fun_d k a b c t) : La_d S t := by
  let e : Fin 3 → M.Domain := Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))
  obtain ⟨i, U, hi, hU⟩ := la_finite_bound_l S hM e
    (Fin.cases ha (Fin.cases hb (Fin.cases hc (fun i => Fin.elim0 i))))
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l ((KPi.models_iff_l.mp hM).1) hi.1
  obtain ⟨V, hv⟩ := ja_value_exists_l S hM s
  have h := jh_step_spec_l hM (ja_successor_l S hM hi.1 hs hi.2 hv)
  exact ⟨s, V, ⟨ho, hv⟩, h.1 k a b c (h.2.1 a (hU 0)) (h.2.1 b (hU 1)) (h.2.1 c (hU 2)) t ht⟩

theorem la_model_separation_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} (φ : Delta0UnarySchema n)
    (ρ : Env (la_model_l S hM) n) (X : (la_model_l S hM).Domain) :
    ∃ Y : (la_model_l S hM).Domain, ∀ x,
      M.mem x.val Y.val ↔ M.mem x.val X.val ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨Y, hy, hY⟩ := la_separation_l S hM hS φ (image_env_l (M := la_model_l S hM) (N := M) Subtype.val ρ)
    (fun i => by exact (ρ.bound i).property) X.property
  refine ⟨⟨Y, hy⟩, fun x => (hY x.val).trans (and_congr_right fun _ => ?_)⟩
  have h := la_model_delta_l S hM hS φ.delta0 (ρ.push x)
  rw [image_env_push_l (M := la_model_l S hM) (N := M) Subtype.val ρ x] at h
  exact h.symm

end YesMetaZFC.SetTheory.InnerModel.Relative
