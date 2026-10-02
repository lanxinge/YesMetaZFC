import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.Sigma1Graph

/-! # Σ₁ 图的精确函数接口 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem s1_function_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X Y : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z)
    (hb : ∀ x, M.mem x X → ∀ y, φ.schema.denote ρ x y → M.mem y Y) :
    ∃ F, Fn0_d X Y F ∧ ∀ x y, Rd_entry_d x y F ↔ M.mem x X ∧ φ.schema.denote ρ x y := by
  obtain ⟨F, hf⟩ := KP.s1_graph_l hKP φ ρ X ht hu
  have entry x y : Rd_entry_d x y F ↔ M.mem x X ∧ φ.schema.denote ρ x y := by
    constructor
    · rintro ⟨p, hp, hpF⟩
      obtain ⟨a, ha, b, hφ, hpair⟩ := (hf p).mp hpF
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hpair hp
      exact ⟨ha, hφ⟩
    · rintro ⟨hx, hφ⟩
      obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x y
      exact ⟨p, hp, (hf p).mpr ⟨x, hx, y, hφ, hp⟩⟩
  refine ⟨F, ⟨?_, ?_, fun x hx y _ z _ hy hz => hu x hx y z ((entry x y).mp hy).2 ((entry x z).mp hz).2⟩, entry⟩
  · intro p hp
    obtain ⟨x, hx, y, hy, hp⟩ := (hf p).mp hp
    exact ⟨x, hx, y, hb x hx y hy, hp⟩
  · intro x hx
    obtain ⟨y, hy⟩ := ht x hx
    exact ⟨y, hb x hx y hy, (entry x y).mpr ⟨hx, hy⟩⟩

end YesMetaZFC.SetTheory.InnerModel
