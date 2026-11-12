import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Enumeration
import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 可数模型列的实际可数极限与返回因子 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已有统一阶段枚举时，极限的可数性只需 ZF。 -/
theorem It_cone_d.countable_enum_l {M : Structure} (hZF0 : M.Models ZF)
    {ω α T Q G B d N W P E : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (countB : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF0)) B ω)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q E)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P) :
    M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF0)) N ω := by
  obtain ⟨D, f, product, fn, onto, _⟩ := cone.enumeration_l hZF0 diagram inside en
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF0 (kp_pair_l (ZF.modelsKP hZF0)) ω
  have count := ZF.countable_product_l (kp_pair_l (ZF.modelsKP hZF0)) hZF0 hω
    countB ⟨id, hid.1⟩ product
  exact ZF.ordinal_image_bound_l (kp_pair_l (ZF.modelsKP hZF0)) hZF0
    (hω.isOrdinal (ZF.modelsKP hZF0)) count fn onto

/-- 可数指标上的可数模型锥由各腿的实际像覆盖，故其极限仍可数。 -/
theorem It_cone_d.countable_l {ω α T Q G B d N W P : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (inside : M.MemberSubset B α) (countB : M.CardinalLessOrEqual I B ω)
    (count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P) : M.CardinalLessOrEqual I N ω := by
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

/-! 传递极限模型中的成员继承同一内部可数界。

这是强 cover-condensation 的目标入口：先证明目标集合 `U` 属于传递
极限载体 `N`，再把 `N` 的可数注入限制到 `U`。 -/
theorem It_cone_d.countable_member_l {ω α T Q G B d N W P U : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (inside : M.MemberSubset B α) (countB : M.CardinalLessOrEqual I B ω)
    (count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P) (transitive : M.TransitiveSet N)
    (hU : M.mem U N) : M.CardinalLessOrEqual I U ω := by
  obtain ⟨g, hg⟩ := cone.countable_l hZFC hω diagram inside countB count
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I (fun x hx => transitive U hU x hx)
  obtain ⟨k, hk⟩ := ZF.exists_compositionInjection hZF I hf hg
  exact ⟨k, hk⟩

/-! 内部可数且非空的集合自动拥有 ω 到它的满射。

`CardinalLessOrEqual` 只给出单射；`injection_retract_l` 在像外返回固定成员，
因而其反向函数在原单射像上仍是恒等，足以得到真正的满射，不引入截面选择。 -/
theorem countable_surjection_zf_l {M : Structure} (hZF0 : M.Models ZF)
    {ω X : M.Domain}
    (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF0)) X ω)
    (nonempty : ∃ x, M.mem x X) :
    ∃ e, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF0)) e ω X ∧
      M.IsSetSurjectiveOnto (kp_pair_l (ZF.modelsKP hZF0)) e ω X := by
  obtain ⟨g, hg⟩ := count
  obtain ⟨a, ha⟩ := nonempty
  obtain ⟨e, he, retract⟩ := ZF.injection_retract_l
    (kp_pair_l (ZF.modelsKP hZF0)) hZF0 hg (fun x hx => hx) ha
  refine ⟨e, he, ?_⟩
  intro x hx
  obtain ⟨i, hi, hix⟩ := hg.1.2.2 x hx
  exact ⟨i, hi, retract x i hix⟩

/-- 可数列的返回极限可继续作为下一棵 nice ω 树的可数完整源。 -/
theorem it_countable_limit_l {ω α T Q G B z c₀ d Y W P : M.Domain}
    (hω : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (branch : It_branch_d α T B)
    (hz : M.mem z B) (hc : Rd_entry_d z c₀ Q) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (maps : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y W P)
    (countB : M.CardinalLessOrEqual I B ω)
    (count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω) :
    ∃ L A p H R r c N V P' σ, It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N V ∧
      Smem_d I c N V ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G c N V P' ∧ (∃ K, Ep_source_d I ω ω K N V) ∧
      M.CardinalLessOrEqual I N ω ∧ Smap_d I ω c d N Y σ ∧
      (∀ i f, Rd_entry_d i f P' ↔ M.mem i B ∧ It_project_d r i f) ∧
      (∀ i f j, Rd_entry_d i f P → Rd_entry_d i j P' → It_comp_d j σ f) ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
      Wf_rel_d N V := by
  obtain ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready, hs, ps, law, ls, wfN⟩ :=
    it_embedding_limit_l hZF hω diagram branch hz hc source my maps
  exact ⟨L, A, p, H, R, r, c, N, V, P', σ, s, limit, mn, cone, ready,
    cone.countable_l hZFC hω diagram branch.subset countB count, hs, ps, law, ls, wfN⟩

end YesMetaZFC.SetTheory.LargeCardinal
