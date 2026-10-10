import YesMetaZFC.SetTheory.InnerModel.OD.Minimum

/-! # OD 参数下的唯一可定义闭性与规范选择集

把 OD 参数替换为其单序数定义码，再应用已有原公式编译。选择集由分离直接
构造，包含每一行的规范选择值；此处不假设背景选择公理。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- 从一个 OD 参数唯一可定义的对象仍为 OD。 -/
theorem od_unique_parameter_l (hZF : M.Models ZF) {A x : M.Domain} (hA : Od_d A)
    (φ : UnarySchema 1)
    (hx : ∀ y, φ.denote (⟨fun _ => A, fun _ => A⟩ : Env M 1) y ↔ y = x) : Od_d x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨q, hq⟩ := (od_code_range_l I hZF).mp hA
  let ψ : UnarySchema 1 := { body := .existsE (.conj
    (od_eval_m (𝒞 := kpair_convention_l) (.bound 2) .newest)
    (pred_m φ (fun _ => .newest) (.bound 1))) }
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  have sat y : ψ.denote ρ y ↔ ∃ a, Od_eval_d I q a ∧
      φ.denote (⟨fun _ => a, fun _ => a⟩ : Env M 1) y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, od_eval_sat_l I hZF.1, pred_sat_l]
    apply exists_congr
    intro a
    apply and_congr_right
    intro _
    exact Formula.closed_env_l _ φ.freeClosed (funext (Fin.cases rfl (fun _ => rfl)))
  refine od_of_unique_l hZF ψ ρ (fun _ => od_eval_ordinal_l I hZF hq) (fun y => (sat y).trans ?_)
  refine ⟨fun ⟨a, ha, hy⟩ => ?_, fun he => ⟨A, hq, (hx y).mpr he⟩⟩
  have eq := od_eval_unique_l I hZF ha hq; subst a
  exact (hx y).mp hy

def Od_choices_d (I : kpair_convention_l.Interpretation M) (A C : M.Domain) : Prop :=
  ∀ x, M.mem x C ↔ ∃ a, M.mem a A ∧ Od_pick_d I a x

def od_choices_m {d} (A C : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest C.weaken) (Formula.existsMem A.weaken
    (od_pick_m (𝒞 := kpair_convention_l) .newest (.bound 1))))
derive_free_closed od_choices_m

theorem od_choices_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (A C : Term d) :
    Formula.satisfies ρ (od_choices_m A C) ↔ Od_choices_d I (A.eval ρ) (C.eval ρ) := by
  simp only [od_choices_m, Od_choices_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, od_pick_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

theorem od_choices_exists_l (hZF : M.Models ZF) (I : kpair_convention_l.Interpretation M)
    {A : M.Domain} (hA : Od_d A) : ∃ C, Od_d C ∧ Od_choices_d I A C := by
  obtain ⟨U, hU⟩ := KP.exists_union (ZF.modelsKP hZF) A
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1)
      (od_pick_m (𝒞 := kpair_convention_l) .newest (.bound 1)) }
  have sat x : φ.denote ρ x ↔ ∃ a, M.mem a A ∧ Od_pick_d I a x := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, od_pick_sat_l I hZF.1]
    rfl
  obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ ρ U
  have hC : Od_choices_d I A C := fun x => (hc x).trans ((and_congr_right fun _ => sat x).trans
    ⟨And.right, fun ⟨a, ha, hx⟩ => ⟨(hU x).mpr ⟨a, ha, hx.1⟩, a, ha, hx⟩⟩)
  let ψ : UnarySchema 1 := { body := od_choices_m (.bound 1) .newest }
  refine ⟨C, od_unique_parameter_l hZF hA ψ (fun D => ?_), hC⟩
  exact (od_choices_sat_l I hZF.1 _ _ _).trans
    ⟨fun hD => hZF.1.eq_of_same_members D C (fun x => (hD x).trans (hC x).symm), fun he => he.symm ▸ hC⟩

end YesMetaZFC.SetTheory.InnerModel
