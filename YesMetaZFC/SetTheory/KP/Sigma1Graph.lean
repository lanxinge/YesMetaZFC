import YesMetaZFC.SetTheory.KP.Sigma1Operations

/-! # Σ₁ 单值关系的实际集合图 -/

namespace YesMetaZFC.SetTheory.KP
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem s1_graph_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z) :
    ∃ F, ∀ p, M.mem p F ↔ ∃ x, M.mem x X ∧ ∃ y, φ.schema.denote ρ x y ∧ KPair_d M p x y := by
  let δ : Delta0BinarySchema n := { body := Formula.extensionalEq .newest (.bound 1), delta0 := .atom _ _ _ }
  let ψ := (S1_binary.of_delta0 δ).pair φ
  have ident x y : (S1_binary.of_delta0 δ).schema.denote ρ x y ↔ y = x :=
    (S1_binary.of_delta0_sat_l δ ρ x y).trans (Formula.satisfies_extensionalEq_iff_eq hKP.1 ..)
  have sat x p : ψ.schema.denote ρ x p ↔ ∃ y, φ.schema.denote ρ x y ∧ KPair_d M p x y := by
    rw [S1_binary.pair_sat_l hKP]
    exact ⟨fun ⟨a, y, ha, hy, hp⟩ => ⟨y, hy, (ident x a).mp ha ▸ hp⟩,
      fun ⟨y, hy, hp⟩ => ⟨x, y, (ident x x).mpr rfl, hy, hp⟩⟩
  obtain ⟨F, hf⟩ := s1_image_l hKP ψ ρ X (by
    intro x hx
    obtain ⟨y, hy⟩ := ht x hx
    obtain ⟨p, hp⟩ := (kpair_interpretation_l M hKP.1 (exists_pair hKP)).total x y
    exact ⟨p, (sat x p).mpr ⟨y, hy, hp⟩⟩) (by
      intro x hx p q hp hq
      obtain ⟨y, hy, hp⟩ := (sat x p).mp hp
      obtain ⟨z, hz, hq⟩ := (sat x q).mp hq
      have he := hu x hx y z hy hz; subst z
      exact kpair_unique_l M hKP.1 hp hq)
  exact ⟨F, fun p => (hf p).trans (exists_congr fun x => and_congr_right fun _ => sat x p)⟩

end YesMetaZFC.SetTheory.KP
