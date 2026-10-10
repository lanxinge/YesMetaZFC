import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 源内部函数族的对角与全定义域延拓

族 B 的定义域 A 可以只是 D 的子集。A 上读取 B(p)(p)，其余点取源中基点；
固定有界关系的源内统一化同时给出实际函数图和值域界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_diagonal_l {ω c X R D A B C} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hA : M.mem A X) (hB : M.mem B X) (hC : M.mem C X)
    (hAD : M.MemberSubset A D) (hBC : Fn0_d A C B)
    (hg : ∀ p g, Rd_entry_d p g B → Sfun_d X D g) :
    ∃ f, Sfun_d X D f ∧ ∀ p g x, Rd_entry_d p g B → (Rd_entry_d p x f ↔ Rd_entry_d p x g) := by
  classical
  obtain ⟨z, hz⟩ := hm.1.2.1
  let ρ : Env M 4 := ⟨Fin.cases A (Fin.cases B (Fin.cases C (fun _ => z))), fun _ => z⟩
  let φ : BinarySchema 4 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m (.bound 2) (.bound 1) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 5))) }
  have sat p x : φ.denote ρ p x ↔ (M.mem p A ∧ ∃ g, M.mem g C ∧ Rd_entry_d p g B ∧ Rd_entry_d p x g) ∨
      (¬ M.mem p A ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hd : φ.body.IsDelta0 := .disj (.conj (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    (.conj (.neg (.mem _ _)) (.atom _ _ _))
  obtain ⟨U, hUX, hu⟩ := theory.algebra.union C hC
  obtain ⟨V, hVX, coords⟩ := theory.algebra.envelope_l hUX
  obtain ⟨L, hL, hl⟩ := theory.algebra.insert_l hVX hz
  have bound p g x (hgc : M.mem g C) (hpx : Rd_entry_d p x g) : M.mem x L := by
    obtain ⟨q, code, hqg⟩ := hpx
    exact (hl x).mpr (Or.inl (coords p x ⟨q, code, (hu q).mpr ⟨g, hgc, hqg⟩⟩).2)
  obtain ⟨f, hf, hFL, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ hd ρ
    (Fin.cases hA (Fin.cases hB (Fin.cases hC (fun _ => hz)))) hD hL (fun p hp => by
      by_cases ha : M.mem p A
      · obtain ⟨g, hgc, hpg⟩ := hBC.2.1 p ha
        obtain ⟨x, _, hpx⟩ := ((hg p g hpg).function_l hX).2.1 p hp
        exact ⟨x, bound p g x hgc hpx, (sat p x).mpr (Or.inl ⟨ha, g, hgc, hpg, hpx⟩)⟩
      · exact ⟨z, (hl z).mpr (Or.inr rfl), (sat p z).mpr (Or.inr ⟨ha, rfl⟩)⟩)
  have value p g x (hpg : Rd_entry_d p g B) (hpx : Rd_entry_d p x f) : Rd_entry_d p x g := by
    rcases (sat p x).mp (hs p x hpx) with ⟨_, g', _, hpg', hx⟩ | ⟨ha, _⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hBC).1.2 p g' g hpg' hpg ▸ hx
    · exact (ha (hBC.bound_l hpg).1).elim
  refine ⟨f, ⟨hf, L, hL, hFL⟩, fun p g x hpg => ⟨value p g x hpg, fun hx => ?_⟩⟩
  obtain ⟨y, _, hy⟩ := hFL.2.1 p (hAD p (hBC.bound_l hpg).1)
  exact (fn0_function_l (ZF.modelsKP hZF) ((hg p g hpg).function_l hX)).1.2 p y x (value p g y hpg hy) hx ▸ hy

end YesMetaZFC.SetTheory.Internal
