import YesMetaZFC.SetTheory.InnerModel.ProofCode.Minimum.Formula

/-! # 由最小 J 构造码得到 L 对象的全局良序

对象按其唯一最小码名排序。所有码名选择均由关系定理提供，不引入不可计算
的选择函数，也不要求背景模型的序数或自然数外部良基。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Lo_lt_d (x y : M.Domain) : Prop := ∃ v w, Pm_min_d v x ∧ Pm_min_d w y ∧ Pn_lt_d v w

theorem lo_domain_l (hM : M.Models KPi) {x y : M.Domain} (h : Lo_lt_d x y) : L_d x ∧ L_d y := by
  obtain ⟨v, w, hv, hw, _⟩ := h
  exact ⟨(pm_min_iff_l hM x).mpr ⟨v, hv⟩, (pm_min_iff_l hM y).mpr ⟨w, hw⟩⟩

theorem lo_irrefl_l (hM : M.Models KPi) (x : M.Domain) : ¬ Lo_lt_d x x := by
  rintro ⟨v, w, hv, hw, h⟩
  have he := pm_min_unique_l hM hv hw; subst w
  exact pn_irrefl_l hM hv.valid_l h

theorem lo_trans_l (hM : M.Models KPi) {x y z : M.Domain} (hxy : Lo_lt_d x y) (hyz : Lo_lt_d y z) : Lo_lt_d x z := by
  obtain ⟨v, w, hv, hw, h⟩ := hxy
  obtain ⟨w', t, hw', ht, g⟩ := hyz
  have he := pm_min_unique_l hM hw hw'; subst w'
  exact ⟨v, t, hv, ht, pn_trans_l hM hv.valid_l hw.valid_l ht.valid_l h g⟩

theorem lo_compare_l (hM : M.Models KPi) {x y : M.Domain} (hx : L_d x) (hy : L_d y) : x = y ∨ Lo_lt_d x y ∨ Lo_lt_d y x := by
  obtain ⟨v, hv⟩ := pm_min_exists_l hM hx
  obtain ⟨w, hw⟩ := pm_min_exists_l hM hy
  rcases pn_compare_l hM hv.valid_l hw.valid_l with he | he | he
  · subst w; exact Or.inl (pn_eval_unique_l hM hv.1 hw.1)
  · exact Or.inr (Or.inl ⟨v, w, hv, hw, he⟩)
  · exact Or.inr (Or.inr ⟨w, v, hw, hv, he⟩)

theorem lo_min_l (hM : M.Models KPi) {X : M.Domain} (hx : ∀ x, M.mem x X → L_d x) (hn : ∃ x, M.mem x X) :
    Po_min_d Lo_lt_d X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := jh_env_l X
  obtain ⟨V, hv⟩ := KP.s1_image_l hKP pm_min_s ρ X
    (fun x hxX => (pm_min_exists_l hM (hx x hxX)).imp (fun v hv => (pm_min_sat_l hM ρ x v).mpr hv))
    (fun x _ v w hv hw => pm_min_unique_l hM ((pm_min_sat_l hM ρ x v).mp hv) ((pm_min_sat_l hM ρ x w).mp hw))
  have hV v : M.mem v V ↔ ∃ x, M.mem x X ∧ Pm_min_d v x :=
    (hv v).trans (exists_congr fun x => and_congr_right fun _ => pm_min_sat_l hM ρ x v)
  have nonempty : ∃ v, M.mem v V := by
    obtain ⟨x, hxX⟩ := hn
    obtain ⟨v, hv⟩ := pm_min_exists_l hM (hx x hxX)
    exact ⟨v, (hV v).mpr ⟨x, hxX, hv⟩⟩
  obtain ⟨v, hvV, hmin⟩ := pn_min_l hM (fun v hvV => ((hV v).mp hvV).elim (fun _ h => h.2.valid_l)) nonempty
  obtain ⟨x, hxX, hvx⟩ := (hV v).mp hvV
  refine ⟨x, hxX, fun y hyX => ?_⟩
  obtain ⟨w, hwy⟩ := pm_min_exists_l hM (hx y hyX)
  rcases hmin w ((hV w).mpr ⟨y, hyX, hwy⟩) with he | he
  · subst w; exact Or.inl (pn_eval_unique_l hM hvx.1 hwy.1)
  · exact Or.inr ⟨v, w, hvx, hwy, he⟩

def lo_lt_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
        .conj (pm_min_s.matrix_m Fin.elim0 (.bound 7) (.bound 4) (.bound 2)) <|
          .conj (pm_min_s.matrix_m Fin.elim0 (.bound 6) (.bound 3) (.bound 1))
            (pn_lt_s.matrix_m Fin.elim0 (.bound 4) (.bound 3) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (pm_min_s.matrix.delta0.bind_l _) (.conj (pm_min_s.matrix.delta0.bind_l _) (pn_lt_s.matrix.delta0.bind_l _))))))) }

theorem lo_lt_sat_l (hM : M.Models KPi) (ρ : Env M 0) (x y : M.Domain) : lo_lt_s.schema.denote ρ x y ↔ Lo_lt_d x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [S1_binary.sat_l]
  simp only [lo_lt_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    po_matrix_env_l pm_min_s ρ, po_matrix_env_l pn_lt_s ρ]
  change (∃ T v, M.mem v T ∧ ∃ w, M.mem w T ∧ ∃ V, M.mem V T ∧ ∃ W, M.mem W T ∧ ∃ Q, M.mem Q T ∧
    pm_min_s.matrix_binary.toBinarySchema.denote (ρ.push x) v V ∧
      pm_min_s.matrix_binary.toBinarySchema.denote (ρ.push y) w W ∧ pn_lt_s.matrix_binary.toBinarySchema.denote (ρ.push v) w Q) ↔ _
  constructor
  · rintro ⟨T, v, _, w, _, V, _, W, _, Q, _, hv, hw, h⟩
    exact ⟨v, w, (pm_min_sat_l hM ρ x v).mp ((pm_min_s.sat_l ρ x v).mpr ⟨V, hv⟩),
      (pm_min_sat_l hM ρ y w).mp ((pm_min_s.sat_l ρ y w).mpr ⟨W, hw⟩),
        (pn_lt_sat_l hKP ρ v w).mp ((pn_lt_s.sat_l ρ v w).mpr ⟨Q, h⟩)⟩
  · rintro ⟨v, w, hv, hw, h⟩
    obtain ⟨V, hv⟩ := (pm_min_s.sat_l ρ x v).mp ((pm_min_sat_l hM ρ x v).mpr hv)
    obtain ⟨W, hw⟩ := (pm_min_s.sat_l ρ y w).mp ((pm_min_sat_l hM ρ y w).mpr hw)
    obtain ⟨Q, h⟩ := (pn_lt_s.sat_l ρ v w).mp ((pn_lt_sat_l hKP ρ v w).mpr h)
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [v, w, V, W, Q]
    exact ⟨T, v, (ht v (by simp)).2, w, (ht w (by simp)).2, V, (ht V (by simp)).2,
      W, (ht W (by simp)).2, Q, (ht Q (by simp)).2, hv, hw, h⟩

def lo_lt_m {n} (x y : Term n) : Formula 1 n := binary_pred_m lo_lt_s.schema Fin.elim0 x y
derive_free_closed lo_lt_m
theorem lo_lt_formula_l (hM : M.Models KPi) {n} (ρ : Env M n) (x y : Term n) :
    Formula.satisfies ρ (lo_lt_m x y) ↔ Lo_lt_d (x.eval ρ) (y.eval ρ) := by
  rw [lo_lt_m, binary_pred_sat_l, lo_lt_sat_l hM]

end YesMetaZFC.SetTheory.InnerModel
