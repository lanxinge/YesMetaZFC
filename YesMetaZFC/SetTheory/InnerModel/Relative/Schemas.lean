import YesMetaZFC.SetTheory.InnerModel.Relative.Reflection
import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Separation

/-! # 相对 J 并类的全分离、全收集和内部幂集 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)
local notation "Nₛ" => la_model_l S (ZF.models_kpi_l hZF)
include hZF hS

theorem la_full_separation_l {n} (φ : UnarySchema n) (ρ : Env Nₛ n) (X : (Nₛ).Domain) :
    ∃ Y : (Nₛ).Domain, ∀ x, (Nₛ).mem x Y ↔ (Nₛ).mem x X ∧ φ.denote ρ x := by
  -- 有限反射把全公式化为真实层上的有界公式，再调用 rud 闭包中的分离。
  let hM := ZF.models_kpi_l hZF
  obtain ⟨b, T, hb, hT⟩ := la_finite_bound_l S (ZF.models_kpi_l hZF) (fun i => ((ρ.push X).bound i).val)
    (fun i => ((ρ.push X).bound i).property)
  let A : (Nₛ).Domain := ⟨T, la_layer_l S hM hb⟩
  obtain ⟨a, U, ha, hAU, hc⟩ := ja_closed_layer_l S hZF hS (lr_queries_l φ.body φ.freeClosed) A
  have ht : (Nₛ).TransitiveSet U := fun x hx y hy => ja_transitive_l S hM hS ha.2 x.val hx y.val hy
  have hX : (Nₛ).mem X U := ja_transitive_l S hM hS ha.2 T hAU X.val (hT 0)
  have hρ i : (Nₛ).mem (ρ.bound i) U := ja_transitive_l S hM hS ha.2 T hAU _ (hT i.succ)
  let e : Fin (n+1) → Term (n+2) := Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)
  let ψ : Delta0UnarySchema (n+1) := {
    body := lr_rel_m φ.body (.bound 1) e
    freeClosed := lr_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))
    delta0 := jl_rel_delta_l .. }
  have tr x (hx : (Nₛ).mem x X) : φ.denote ρ x ↔ ψ.toUnarySchema.denote (ρ.push U) x :=
    lr_reflect_core_l φ.body φ.freeClosed hc (ρ.push x) ((ρ.push U).push x) (.bound 1) e
      rfl (Fin.cases rfl (fun _ => rfl)) (Fin.cases (ht X hX x hx) hρ)
  obtain ⟨Y, hy⟩ := la_model_separation_l S (ZF.models_kpi_l hZF) hS ψ (ρ.push U) X
  exact ⟨Y, fun x => (hy x).trans (and_congr_right fun hx => (tr x hx).symm)⟩

omit hS in
theorem la_trace_l (B : M.Domain) : ∃ D, ∀ x, M.mem x D ↔ M.mem x B ∧ La_d S x := by
  let φ : UnarySchema 1 := { body := la_m (.bound 1) .newest }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ (ja_env_l S) B
  exact ⟨D, fun x => (hd x).trans (and_congr_right fun _ => la_sat_l (ZF.modelsKP hZF) _ _ _)⟩

theorem la_full_collection_l {n} (φ : BinarySchema n) (ρ : Env Nₛ n) (X : (Nₛ).Domain)
    (ht : ∀ x, (Nₛ).mem x X → ∃ y, φ.denote ρ x y) :
    ∃ Y : (Nₛ).Domain, ∀ x, (Nₛ).mem x X → ∃ y, (Nₛ).mem y Y ∧ φ.denote ρ x y := by
  -- 背景收集只产生一个见证池；取并类迹及统一层界，才得到内模型自己的收集集。
  let η := (image_env_l (M := Nₛ) (N := M) Subtype.val ρ).push S
  let e : Fin (n+2) → Term (n+3) := Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+3, by omega⟩))
  let ψ : BinarySchema (n+1) := {
    body := .conj (la_m (.bound 2) .newest) (la_rel_m φ.body (.bound 2) e)
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨la_m_freeClosed _ _ rfl rfl,
        la_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))⟩ }
  have sat x y : ψ.denote η x y ↔ La_d S y ∧
      Formula.satisfies ((η.push x).push y) (la_rel_m φ.body (.bound 2) e) := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, la_sat_l (ZF.modelsKP hZF)]; rfl
  have tr (x y : (Nₛ).Domain) : Formula.satisfies ((η.push x.val).push y.val)
      (la_rel_m φ.body (.bound 2) e) ↔ φ.denote ρ x y :=
    la_rel_sat_l (ZF.models_kpi_l hZF) S hS φ.body φ.freeClosed ((ρ.push x).push y) ((η.push x.val).push y.val)
      (.bound 2) e rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  obtain ⟨B, hB⟩ := ZF.collection_exists_d hZF ψ η X.val (fun x hx => by
    let z : (Nₛ).Domain := ⟨x, la_transitive_l S (ZF.models_kpi_l hZF) hS X.property hx⟩
    obtain ⟨y, hy⟩ := ht z hx
    exact ⟨y.val, (sat x y.val).mpr ⟨y.property, (tr z y).mpr hy⟩⟩)
  obtain ⟨D, hd⟩ := la_trace_l S hZF B
  obtain ⟨a, Y, ha, hy⟩ := la_bound_l S (ZF.models_kpi_l hZF) (fun x hx => ((hd x).mp hx).2)
  refine ⟨⟨Y, la_layer_l S (ZF.models_kpi_l hZF) ha⟩, fun x hx => ?_⟩
  obtain ⟨y, hyB, hp⟩ := hB x.val hx
  obtain ⟨hyL, hyφ⟩ := (sat x.val y).mp hp
  exact ⟨⟨y, hyL⟩, hy y ((hd y).mpr ⟨hyB, hyL⟩), (tr x ⟨y, hyL⟩).mp hyφ⟩

theorem la_model_power_l (X : (Nₛ).Domain) : ∃ P : (Nₛ).Domain, (Nₛ).IsPowerSetOf P X := by
  -- 仅将属于并类的旧幂集成员纳入层界，不假定内模型拥有背景的全部子集。
  have sub (x : (Nₛ).Domain) : (Nₛ).MemberSubset x X ↔ M.MemberSubset x.val X.val :=
    ⟨fun h y hy => h ⟨y, la_transitive_l S (ZF.models_kpi_l hZF) hS x.property hy⟩ hy,
      fun h y hy => h y.val hy⟩
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X.val
  obtain ⟨D, hd⟩ := la_trace_l S hZF P
  obtain ⟨a, U, ha, hu⟩ := la_bound_l S (ZF.models_kpi_l hZF) (fun x hx => ((hd x).mp hx).2)
  let W : (Nₛ).Domain := ⟨U, la_layer_l S (ZF.models_kpi_l hZF) ha⟩
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  obtain ⟨Q, hq⟩ := la_model_separation_l S (ZF.models_kpi_l hZF) hS φ (rd_seed_env_l (M := Nₛ) X) W
  have hq' (x : (Nₛ).Domain) : (Nₛ).mem x Q ↔ (Nₛ).mem x W ∧ (Nₛ).MemberSubset x X :=
    (hq x).trans (and_congr_right fun _ => Formula.satisfies_subset_iff _ _ _)
  exact ⟨Q, fun x => (hq' x).trans ⟨And.right,
    fun hx => ⟨hu x.val ((hd x.val).mpr ⟨(hp x.val).mpr ((sub x).mp hx), x.property⟩), hx⟩⟩⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
