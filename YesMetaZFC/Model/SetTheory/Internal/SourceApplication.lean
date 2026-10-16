import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 源内函数值族的逐点求值

把两份源内代表在指定好集合上复合，坏坐标取同一个源内对象。所有候选
函数值由函数值族的一次并和坐标包络界住，因此只用已有的有界统一化。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_apply_on_l {ω c X R D A f x : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (model : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hA : M.mem A X)
    (hf : M.mem f X) (ff : Fn0_d D X f) (hx : M.mem x X) (fx : Fn0_d D X x)
    (total : ∀ s, M.mem s A → ∃ t z y, Rd_entry_d s t f ∧ Rd_entry_d s z x ∧ Rd_entry_d z y t) :
    ∃ g, M.mem g X ∧ Fn0_d D X g ∧
      ∀ s t z y, M.mem s A → Rd_entry_d s t f → Rd_entry_d s z x → Rd_entry_d s y g → Rd_entry_d z y t := by
  obtain ⟨B, hB, bound⟩ := theory.algebra.envelope_l hf
  obtain ⟨H, hH, un⟩ := theory.algebra.union B hB
  obtain ⟨C, hC, coords⟩ := theory.algebra.envelope_l hH
  obtain ⟨P, hP, boundX⟩ := theory.algebra.envelope_l hx
  obtain ⟨Q, hQ, insert⟩ := theory.algebra.insert_l hC hD
  have inside t z y (ht : M.mem t B) (entry : Rd_entry_d z y t) : M.mem y C := by
    obtain ⟨p, pair, hp⟩ := entry
    exact (coords z y ⟨p, pair, (un p).mpr ⟨t, ht, hp⟩⟩).2
  let ρ : Env M 6 := ⟨fun i => [f, x, A, B, P, D].get i, fun _ => D⟩
  let φ : BinarySchema 6 := {
    body := .disj
      (.conj (.mem (.bound 1) (.bound 4)) (Formula.existsMem (.bound 5) (Formula.existsMem (.bound 7)
        (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4))
          (.conj (rd_entry0_m (.bound 3) .newest (.bound 5)) (rd_entry0_m .newest (.bound 2) (.bound 1)))))))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.extensionalEq .newest (.bound 7))) }
  have read s y : φ.denote ρ s y ↔
      (M.mem s A ∧ ∃ t, M.mem t B ∧ ∃ z, M.mem z P ∧ Rd_entry_d s t f ∧ Rd_entry_d s z x ∧ Rd_entry_d z y t) ∨
      (¬ M.mem s A ∧ y = D) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have params : ∀ i, M.mem (ρ.bound i) X :=
    Fin.cases hf (Fin.cases hx (Fin.cases hA (Fin.cases hB (Fin.cases hP (Fin.cases hD (fun i => Fin.elim0 i))))))
  obtain ⟨g, hg, fg, choose⟩ := sc_uniform_source_l hZF hω hX model theory φ
    (.disj (.conj (.mem _ _) (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))) (.conj (.neg (.mem _ _)) (.atom ..)))
    ρ params hD hQ (fun s _ => by
      classical
      by_cases hs : M.mem s A
      · obtain ⟨t, z, y, hst, hsz, hzy⟩ := total s hs
        exact ⟨y, (insert y).mpr (Or.inl (inside t z y (bound s t hst).2 hzy)),
          (read s y).mpr (Or.inl ⟨hs, t, (bound s t hst).2, z, (boundX s z hsz).2, hst, hsz, hzy⟩)⟩
      · exact ⟨D, (insert D).mpr (Or.inr rfl), (read s D).mpr (Or.inr ⟨hs, rfl⟩)⟩)
  refine ⟨g, hg, fg.mono_target_l (hX Q hQ), fun s t z y hs hst hsz hsy => ?_⟩
  rcases (read s y).mp (choose s y hsy) with ⟨_, t', _, z', _, hst', hsz', hzy⟩ | ⟨no, _⟩
  · exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 s t' t hst' hst ▸
      (fn0_function_l (ZF.modelsKP hZF) fx).1.2 s z' z hsz' hsz ▸ hzy
  · exact (no hs).elim

end YesMetaZFC.SetTheory.Internal
