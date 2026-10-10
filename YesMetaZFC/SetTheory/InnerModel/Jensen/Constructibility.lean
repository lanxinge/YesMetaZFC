import YesMetaZFC.SetTheory.InnerModel.Jensen.Relativization
import YesMetaZFC.SetTheory.Axioms.Constructible

/-! # J 的内部层级识别与可构造公理

J 已经是 KPi 模型，故它自行产生递归证书。证书的 Σ₁ 向上绝对性及背景
递归唯一性将内部层与背景层识别，最后得到原句子 V=L 的模型性。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem l_sigma1_up_l (hM : M.Models KPi) {n} (φ : S1_binary n) (ρ : Env (l_model_l hM) n)
    {x y : (l_model_l hM).Domain} (h : φ.schema.denote ρ x y) :
    φ.schema.denote (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) x.val y.val := by
  obtain ⟨w, hw⟩ := (φ.sat_l ρ x y).mp h
  have h := (l_model_delta_l hM φ.matrix.delta0 (((ρ.push x).push y).push w)).mp hw
  rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ((ρ.push x).push y) w,
    image_env_push_l (M := l_model_l hM) (N := M) Subtype.val (ρ.push x) y,
    image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
  exact (φ.sat_l _ x.val y.val).mpr ⟨w.val, h⟩

theorem l_jh_value_up_l (hM : M.Models KPi) {a Y : (l_model_l hM).Domain}
    (hy : Jh_value_d (M := l_model_l hM) a Y) : Jh_value_d (M := M) a.val Y.val := by
  have h := l_sigma1_up_l hM (rc_value_s jh_op_s) (jh_env_l a) hy
  exact (Formula.closed_env_l _ (rc_value_s jh_op_s).schema.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp h

/-- J 内外对序数的判断一致；此处使用已证明的两个 KP 实例。 -/
theorem l_ordinal_iff_l (hM : M.Models KPi) (a : (l_model_l hM).Domain) :
    (l_model_l hM).IsOrdinal a ↔ M.IsOrdinal a.val := by
  let ρ := (jh_env_l a).push a
  exact (KP.ord0_sat_l (l_model_kp_l hM) ρ .newest).symm.trans
    ((l_model_delta_l hM (KP.ord0_delta_l .newest) ρ).trans
      (KP.ord0_sat_l (KPi.models_iff_l.mp hM).1 _ .newest))

/-- 双向识别内部 J 层，包含非标准序数和非标准递归历史。 -/
theorem l_jh_value_iff_l (hM : M.Models KPi) (a Y : (l_model_l hM).Domain) :
    Jh_value_d (M := l_model_l hM) a Y ↔ Jh_value_d (M := M) a.val Y.val := by
  refine ⟨l_jh_value_up_l hM, fun hy => ?_⟩
  obtain ⟨Z, hz⟩ := jh_value_exists_l (l_model_kpi_l hM) a
  have he : Y = Z := Subtype.ext (jh_value_unique_l hM hy (l_jh_value_up_l hM hz))
  exact he.symm ▸ hz

theorem l_internal_constructible_l (hM : M.Models KPi) (x : (l_model_l hM).Domain) :
    L_d (M := l_model_l hM) x := by
  obtain ⟨a, Y, ha, hx⟩ := x.property
  let b : (l_model_l hM).Domain := ⟨a, l_ordinal_l hM ha.1⟩
  let Z : (l_model_l hM).Domain := ⟨Y, l_layer_l hM ha⟩
  exact ⟨b, Z, ⟨(l_ordinal_iff_l hM b).mpr ha.1, (l_jh_value_iff_l hM b Z).mpr ha.2⟩, hx⟩

theorem vl_sat_l (hKP : M.Models KP) (f : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0) Axioms.vl_axiom.formula ↔ ∀ x : M.Domain, L_d x := by
  simp only [Axioms.vl_axiom, Sentence.ofFormula, Formula.satisfies_forall_iff,
    l_sat_l hKP, Definitional.Term.eval_newest]

theorem l_model_vl_l (hM : M.Models KPi) : (l_model_l hM).SatisfiesSentence Axioms.vl_axiom := by
  rw [Structure.satisfiesSentence_iff]
  exact fun f => (vl_sat_l (l_model_kp_l hM) f).mpr (l_internal_constructible_l hM)

/-- 任意 KPi 背景模型的 Jensen 内模型满足原演绎核中的 KP + V=L。 -/
theorem l_model_kpl_l (hM : M.Models KPi) : (l_model_l hM).Models KPL := by
  refine ⟨(l_model_kp_l hM).1, fun s hs => ?_⟩
  cases hs with
  | kp hs => exact (l_model_kp_l hM).2 s hs
  | constructible => exact l_model_vl_l hM

end YesMetaZFC.SetTheory.InnerModel
