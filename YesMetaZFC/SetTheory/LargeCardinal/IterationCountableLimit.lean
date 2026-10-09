import YesMetaZFC.SetTheory.LargeCardinal.IterationCountable
import YesMetaZFC.SetTheory.LargeCardinal.IterationEmbedding

/-! # 可数模型列的实际可数极限与返回因子 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 可数指标上的可数模型锥由各腿的实际像覆盖，故其极限仍可数。 -/
theorem It_cone_d.countable_l {ω α T Q G B d N W P : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d hZF ω α T Q G)
    (inside : M.MemberSubset B α) (countB : M.CardinalLessOrEqual I B ω)
    (count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω)
    (cone : It_cone_d hZF ω B Q G d N W P) : M.CardinalLessOrEqual I N ω := by
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ f x,
    ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 1 : Term 3)⌝ₛ, f, ⌜(Term.bound 2 : Term 3)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(x, ⌜(Term.newest : Term 3)⌝ₛ, f)⟫ }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  have sat i y : φ.denote ρ i y ↔ ∃ f x, Rd_entry_d i f P ∧ Rd_entry_d x y f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  apply ZFC.countable_cover_l I hZFC hω φ ρ countB
  · intro i hi D spec
    obtain ⟨c, X, R, hc, mx⟩ := diagram.model_l hZF (inside i hi)
    obtain ⟨f, hf⟩ := (cone.domain i).mp hi
    have ff := (cone.elementary i f c X R hf hc mx).1.1
    have fd : M.IsSetFunctionFromTo I f X D := ⟨ff.1, ff.2.1, fun x hx => by
      obtain ⟨y, hy, hxy⟩ := ff.2.2 x hx
      exact ⟨y, (spec y).mpr ⟨hy, (sat i y).mpr ⟨f, x, hf, hxy⟩⟩, hxy⟩⟩
    obtain ⟨g, hg⟩ := ZFC.surjection_bound_l I hZFC fd (by
      intro y hy
      obtain ⟨f', x, hf', hxy⟩ := (sat i y).mp ((spec y).mp hy).2
      have hxy := cone.function.2 i f' f hf' hf ▸ hxy
      exact ⟨x, ff.input_mem_of_pairMember hxy, hxy⟩)
    obtain ⟨k, hk⟩ := count i c X R hc mx.1
    exact ZF.exists_compositionInjection hZF I hg hk
  · intro y hy
    obtain ⟨i, f, x, hf, hxy⟩ := cone.cover y hy
    exact ⟨i, (cone.domain i).mpr ⟨f, hf⟩, (sat i y).mpr ⟨f, x, hf, hxy⟩⟩

/-- 可数列的返回极限可继续作为下一棵 nice ω 树的可数完整源。 -/
theorem it_countable_limit_l {ω α T Q G B z c₀ d Y W P : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d hZF ω α T Q G) (branch : It_branch_d α T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d hZF ω B Q G d Y W P)
    (countB : M.CardinalLessOrEqual I B ω)
    (count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω) :
    ∃ L A p H R r c N V P' σ, It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
      Smem_d I c N V ∧ It_cone_d hZF ω B Q G c N V P' ∧ It_source_d hZF ω c ∧
      M.CardinalLessOrEqual I N ω ∧ Smap_d I ω c d N Y σ ∧
      (∀ i f, Rd_entry_d i f P' ↔ M.mem i B ∧ It_project_d r i f) ∧
      ∀ i f j, Rd_entry_d i f P → Rd_entry_d i j P' → It_comp_d j σ f := by
  obtain ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready, hs, ps, law⟩ :=
    it_embedding_limit_l hZF hω diagram branch hz hc source my maps
  exact ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready,
    cone.countable_l hZFC hω diagram branch.subset countB count, hs, ps, law⟩

end YesMetaZFC.SetTheory.LargeCardinal
