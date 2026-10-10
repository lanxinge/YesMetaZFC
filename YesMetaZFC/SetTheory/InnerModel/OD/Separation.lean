import YesMetaZFC.SetTheory.InnerModel.OD.RelativeClosure

/-! # 两种参数可定义类中的分离集 -/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def oa_sep_s {n} (φ : UnarySchema n) : UnarySchema (n+1) := {
  body := .forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 2))
    (pred_m φ (fun i => .bound ⟨i.val+3, by omega⟩) .newest))) }

theorem oa_sep_schema_l {n} (φ : UnarySchema n) (ρ : Env M n) (X Y : M.Domain) :
    (oa_sep_s φ).denote (ρ.push X) Y ↔ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.denote ρ x := by
  simp only [oa_sep_s, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, pred_sat_l]
  rfl

theorem oa_separation_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n} (φ : UnarySchema n)
    (ρ : Env M n) (hρ : ∀ i, Oa_d k A (ρ.bound i)) {X} (hX : Oa_d k A X) :
    ∃ Y, Oa_d k A Y ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.denote ρ x := by
  obtain ⟨Y, hy⟩ := ZF.separation_exists_d hZF φ ρ X
  have defn Z : (oa_sep_s φ).denote (ρ.push X) Z ↔ Z = Y :=
    (oa_sep_schema_l φ ρ X Z).trans
      ⟨fun hz => hZF.1.eq_of_same_members Z Y (fun x => (hz x).trans (hy x).symm), fun he => he.symm ▸ hy⟩
  exact ⟨Y, oa_unique_l hZF k A (oa_sep_s φ) (ρ.push X) (Fin.cases hX hρ) defn, hy⟩

end YesMetaZFC.SetTheory.InnerModel
