import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

/-! # 几乎处处有界的代表可在源内改成处处有界

在不满足界的坐标上取给定基点。新图由源内统一化实际构造；等价只使用
原来的测度一集合，不要求源拥有背景中的全部函数或全部子集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_bound_l {ω c X R D B U f z : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hB : M.mem B X)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (hz : M.mem z B) (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (bounded : ∃ A, M.mem A U ∧ ∀ v, M.mem v A → ∃ x, M.mem x B ∧ Rd_entry_d v x f) :
    ∃ g, M.mem g X ∧ Fn0_d D B g ∧ Rp_eq_d X U f g := by
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases B (fun _ => z)), fun _ => z⟩
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 2)))
      (.conj (.neg (Formula.existsMem (.bound 3) (rd_entry0_m (.bound 2) .newest (.bound 3))))
        (Formula.extensionalEq .newest (.bound 4))) }
  have sat v x : φ.denote ρ v x ↔ (M.mem x B ∧ Rd_entry_d v x f) ∨
      (¬ (∃ y, M.mem y B ∧ Rd_entry_d v y f) ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨g, C, hgX, _, hg, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.disj (.conj (.mem _ _) (rd_entry0_delta_l ..))
      (.conj (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.atom _ _ _))) ρ
    (Fin.cases hfX (Fin.cases hB (fun _ => hX B hB z hz))) hD (fun v _ => by
      classical
      by_cases h : ∃ y, M.mem y B ∧ Rd_entry_d v y f
      · obtain ⟨y, hy, hvy⟩ := h
        exact ⟨y, hX B hB y hy, (sat v y).mpr (Or.inl ⟨hy, hvy⟩)⟩
      · exact ⟨z, hX B hB z hz, (sat v z).mpr (Or.inr ⟨h, rfl⟩)⟩)
  have into v x (hvx : Rd_entry_d v x g) : M.mem x B :=
    ((sat v x).mp (select v x hvx)).elim And.left (fun h => h.2.symm ▸ hz)
  have hgB : Fn0_d D B g := fn0_of_function_l (ZF.modelsKP hZF)
    ⟨(fn0_function_l (ZF.modelsKP hZF) hg).1, (fn0_function_l (ZF.modelsKP hZF) hg).2.1,
      fun v hv => (hg.2.1 v hv).imp fun x hx => ⟨into v x hx.2, hx.2⟩⟩
  obtain ⟨A, hAU, bound⟩ := bounded
  refine ⟨g, hgX, hgB, A, hAU, fun v hv => ?_⟩
  obtain ⟨x, hxB, hvx⟩ := bound v hv
  obtain ⟨y, _, hvy⟩ := hg.2.1 v (hU A hAU v hv)
  rcases (sat v y).mp (select v y hvy) with ⟨_, hvy'⟩ | ⟨hn, _⟩
  · exact ⟨x, hX B hB x hxB, hvx, (fn0_function_l (ZF.modelsKP hZF) hf).1.2 v y x hvy' hvx ▸ hvy⟩
  · exact (hn ⟨x, hxB, hvx⟩).elim

/-- 对集合值代表逐点取交；几乎处处已在界内时，商中的值不变。 -/
theorem rs_cap_l {ω c X R D B U f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hB : M.mem B X)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (bounded : ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x f → M.MemberSubset x B) :
    ∃ g, M.mem g X ∧ Fn0_d D X g ∧
      (∀ s x, Rd_entry_d s x g → M.MemberSubset x B) ∧ Rp_eq_d X U f g := by
  obtain ⟨_, C, hCX, hfC⟩ := sc_function_domain_l hZF hω hX hm theory hD hfX hf
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases B (fun _ => C)), fun _ => B⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4) (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
      (.conj (Formula.subset (.bound 1) .newest) (Formula.forallMem .newest
        (.iff (.mem .newest (.bound 2)) (.mem .newest (.bound 5)))))) }
  have sat s y : φ.denote ρ s y ↔ ∃ x, M.mem x C ∧ Rd_entry_d s x f ∧
      M.MemberSubset y x ∧ ∀ z, M.mem z x → (M.mem z y ↔ M.mem z B) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]; rfl
  obtain ⟨g, H, hgX, hHX, hg, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.mem _ _))))))
    ρ (Fin.cases hfX (Fin.cases hB (fun _ => hCX))) hD (fun s hs => by
      obtain ⟨x, hx, hsx⟩ := hfC.2.1 s hs
      let ψ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
      obtain ⟨y, hyX, ys⟩ := sc_separate_source_l I hZF hω hX hm theory ψ (.mem _ _)
        ⟨fun _ => B, fun _ => B⟩ (fun _ => hB) (hX C hCX x hx)
      have read z : M.mem z y ↔ M.mem z x ∧ M.mem z B := by
        simpa only [ψ, UnarySchema.denote, Formula.satisfies_mem_iff] using! ys z
      exact ⟨y, hyX, (sat s y).mpr ⟨x, hx, hsx, fun z hz => ((read z).mp hz).1,
        fun z hz => (read z).trans ⟨And.right, fun h => ⟨hz, h⟩⟩⟩⟩)
  obtain ⟨A, hAU, bound⟩ := bounded
  refine ⟨g, hgX, hg.mono_target_l (hX H hHX), fun s y hsy => ?_, A, hAU, fun s hs => ?_⟩
  · obtain ⟨x, _, _, sub, spec⟩ := (sat s y).mp (select s y hsy)
    exact fun z hz => (spec z (sub z hz)).mp hz
  · obtain ⟨y, _, hsy⟩ := hg.2.1 s (hU A hAU s hs)
    obtain ⟨x, hx, hsx, sub, spec⟩ := (sat s y).mp (select s y hsy)
    have eq : y = x := hZF.1.eq_of_same_members y x fun z =>
      ⟨sub z, fun hz => (spec z hz).mpr (bound s x hs hsx z hz)⟩
    exact ⟨x, hX C hCX x hx, hsx, eq ▸ hsy⟩

end YesMetaZFC.SetTheory.Internal
