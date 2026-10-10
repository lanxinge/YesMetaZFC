import YesMetaZFC.SetTheory.InnerModel.Order.InitialSigma1

/-! # 逐层 Jensen 序的全局序律与 Δ₁ 判定

有限参数及任意模型内 L 对象集合都有真实 J 层界。该层的已证良序给出全局
三歧性和最小元；相等或反向比较提供互补的 Σ₁ 定义。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def js_less_m {n} (x y : Term n) : Formula 1 n := binary_pred_m js_less_s.schema Fin.elim0 x y
derive_free_closed js_less_m
theorem js_less_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (x y : Term n) :
    Formula.satisfies ρ (js_less_m x y) ↔ Js_lt_d (x.eval ρ) (y.eval ρ) := by
  rw [js_less_m, binary_pred_sat_l, js_less_sat_l hKP]

theorem js_domain_l (hM : M.Models KPi) {x y : M.Domain} (h : Js_lt_d x y) : L_d x ∧ L_d y := by
  obtain ⟨a, U, R, ha, hu, hx, hy, _⟩ := h
  have hU := (js_value_constructible_l hM ha hu).1
  exact ⟨l_transitive_l hM hU hx, l_transitive_l hM hU hy⟩

theorem js_irrefl_l (hM : M.Models KPi) (x : M.Domain) : ¬ Js_lt_d x x := by
  rintro ⟨a, U, R, ha, hu, hx, _, hxx⟩
  exact (js_coherence_l hM ha hu).2.1.linear.2.1.1 x hx hxx

theorem js_trans_l (hM : M.Models KPi) {x y z : M.Domain} (hxy : Js_lt_d x y) (hyz : Js_lt_d y z) : Js_lt_d x z := by
  obtain ⟨a, U, R, ha, hu, hy, hz, hyz⟩ := hyz
  have hx := js_less_initial_l hM ha hu hy hxy
  exact (js_less_at_l hM ha hu hx hz).mpr ((js_coherence_l hM ha hu).2.1.linear.2.1.2 x hx y hy z hz
    ((js_less_at_l hM ha hu hx hy).mp hxy) hyz)

theorem js_compare_l (hM : M.Models KPi) {x y : M.Domain} (hx : L_d x) (hy : L_d y) :
    x = y ∨ Js_lt_d x y ∨ Js_lt_d y x := by
  obtain ⟨a, U, ha, hU⟩ := l_finite_bound_l hM (n := 2) (Fin.cases x (fun _ => y)) (Fin.cases hx (fun _ => hy))
  obtain ⟨R, ho, hr, _⟩ := jh_local_wellorder_l hM ha.1 ha.2
  exact (ho.linear.2.2 x (hU 0) y (hU 1)).elim
    (fun he => Or.inl ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members x y he))
    (fun h => Or.inr (h.imp ((hr x y (hU 0) (hU 1)).mpr) ((hr y x (hU 1) (hU 0)).mpr)))

theorem js_min_l (hM : M.Models KPi) {X : M.Domain} (hX : ∀ x, M.mem x X → L_d x)
    (hn : ∃ x, M.mem x X) : Po_min_d Js_lt_d X := by
  obtain ⟨a, U, ha, hU⟩ := l_bound_l hM hX
  obtain ⟨R, ho, hr, _⟩ := jh_local_wellorder_l hM ha.1 ha.2
  obtain ⟨x, hx, hm⟩ := ho.least X hU hn
  exact ⟨x, hx, fun y hy => (hm y hy).elim
    (fun he => Or.inl ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members x y he))
    (fun h => Or.inr ((hr x y (hU x hx) (hU y hy)).mpr h))⟩

def js_not_less_s : S1_binary 0 where
  matrix := {
    body := .disj (Formula.extensionalEq (.bound 2) (.bound 1)) (js_less_s.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .disj (.atom _ _ _) (js_less_s.matrix.delta0.bind_l _) }

theorem js_not_less_sat_l (hE : Extensional M) (ρ : Env M 0) (x y : M.Domain) :
    js_not_less_s.schema.denote ρ x y ↔ x = y ∨ js_less_s.schema.denote ρ y x := by
  have matrix T : Formula.satisfies (((ρ.push x).push y).push T)
      (js_less_s.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest) ↔
      Formula.satisfies (((ρ.push y).push x).push T) js_less_s.matrix.body := by
    rw [S1_binary.matrix_sat_l]
    exact Formula.closed_env_l _ js_less_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  rw [S1_binary.sat_l, S1_binary.sat_l]
  simp only [js_not_less_s, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE]
  change (∃ T, x = y ∨ Formula.satisfies (((ρ.push x).push y).push T)
    (js_less_s.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest)) ↔ _
  simp only [matrix]
  exact ⟨fun ⟨T, h⟩ => h.elim Or.inl (fun h => Or.inr ⟨T, h⟩),
    fun h => h.elim (fun he => ⟨x, Or.inl he⟩) (fun ⟨T, h⟩ => ⟨T, Or.inr h⟩)⟩

theorem js_delta1_l (hM : M.Models KPi) {x y : M.Domain} (hx : L_d x) (hy : L_d y) (ρ : Env M 0) :
    js_less_s.schema.denote ρ x y ↔ ¬ js_not_less_s.schema.denote ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [js_not_less_sat_l hKP.1, js_less_sat_l hKP, js_less_sat_l hKP]
  constructor
  · intro h g; rcases g with he | g
    · subst y; exact js_irrefl_l hM x h
    · exact js_irrefl_l hM x (js_trans_l hM h g)
  · intro hn
    exact (js_compare_l hM hx hy).elim (fun h => (hn (Or.inl h)).elim)
      (fun h => h.elim id (fun h => (hn (Or.inr h)).elim))

/-- 正反同一对 Σ₁ 公式在每个 J 层内互补。 -/
theorem jh_local_delta1_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 0) (x y : (rt_model_l C hn).Domain) :
    js_less_s.schema.denote ρ x y ↔ ¬ js_not_less_s.schema.denote ρ x y := by
  rw [js_not_less_sat_l (rt_model_ext_l (KPi.models_iff_l.mp hM).1.1 (jh_value_transitive_l hM h) hn),
    jh_local_sigma1_l hM ha h, jh_local_sigma1_l hM ha h]
  constructor
  · intro hxy g; rcases g with he | g
    · subst y; exact js_irrefl_l hM x.val hxy
    · exact js_irrefl_l hM x.val (js_trans_l hM hxy g)
  · intro hn
    rcases js_compare_l hM ⟨a, C, ⟨ha, h⟩, x.property⟩ ⟨a, C, ⟨ha, h⟩, y.property⟩ with he | hxy | hyx
    · exact (hn (Or.inl (Subtype.ext he))).elim
    · exact hxy
    · exact (hn (Or.inr hyx)).elim

end YesMetaZFC.SetTheory.InnerModel
