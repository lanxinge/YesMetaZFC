import YesMetaZFC.Model.Forcing.Internal.Homogeneous.Definition

/-! # 弱齐性下地参数真值的地模型定义

扩张真值先由真值引理给出泛型条件，再交换 check 基点。弱齐性排除相反判定，
因此存在条件力迫的原公式恰好计算每个泛型扩张的地参数真值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
local notation "E" => extension_l M hZF B R z U
include O hU hb hv

theorem gforce_of_truth_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (η : Env E n) (hη : ∀ i, e (v i) = η.bound i)
    (ht : Formula.satisfies η φ) : Gforce_d M B R z φ v := by
  have hbB := (hU.proper b hb).1
  obtain ⟨ρ, hρ, hn⟩ := check_env_l hZF hbB v
  have hval := qenv_val_l (R := R) (z := z) (U := U) hZF ρ hn
  have heq i : (qenv_l hZF ρ hn).bound i = η.bound i :=
    (qval_unique_l (hv (v i) (ρ.bound i) (hρ i)) (hval (.bound i))).symm.trans (hη i)
  have hsat := (lr_env_congr_l φ hφ (qenv_l hZF ρ hn) η heq).mpr ht
  obtain ⟨p, hp, hf⟩ := (forcing_truth_l O hZF hU φ hφ ρ (qenv_l hZF ρ hn) hval).mpr hsat
  obtain ⟨q, hq, hqp, hqb⟩ := hU.directed p b hp hb
  have hq' := hU.proper q hq
  exact gforce_change_base_l O hZF φ hφ v ρ hbB hρ ⟨hq'.1, hq'.2, hqb⟩
    ((forces_regular_l O hZF φ ρ hn).1 p q (hU.proper p hp).1 ⟨hq'.1, hq'.2, hqp⟩ hf)

/-- 右侧是泛型扩张真值，左侧是完全不含泛型参数的地模型原公式。 -/
theorem whom_ground_truth_l (hH : Whom_d M B R z) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (η : Env E n) (hη : ∀ i, e (v i) = η.bound i) :
    Gforce_d M B R z φ v ↔ Formula.satisfies η φ := by
  refine ⟨fun h => ?_, gforce_of_truth_l O hZF hU hb e hv φ hφ v η hη⟩
  apply Classical.byContradiction
  intro hn
  exact whom_consistent_l O hZF hH φ hφ v h
    (gforce_of_truth_l O hZF hU hb e hv (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ) v η hη
      ((Formula.satisfies_neg_iff η φ).mpr hn))

end YesMetaZFC.Model.Forcing.Internal
