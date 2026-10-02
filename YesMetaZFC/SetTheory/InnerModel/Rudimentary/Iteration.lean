import YesMetaZFC.SetTheory.InnerModel.Recursion.Existence
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Step
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv

/-! # 有限基的内部迭代

递归式 X(a)=s(U∪⋃{X(b):b∈a}) 对所有内部集合有唯一解。
在内部自然数上，这是从 s(U) 开始的一步扩张迭代；ω 处给出闭包。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rd_iter_op_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (rd_graph_m .range (.bound 5) (.bound 5) (.bound 5) (.bound 2))
        (.conj (rd_graph_m .union (.bound 2) (.bound 2) (.bound 2) (.bound 1))
          (.conj (join0_m .newest (.bound 6) (.bound 1)) (rd_step_m .newest (.bound 4)))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_graph_delta_l ..)
      (.conj (rd_graph_delta_l ..) (.conj (join0_delta_l ..) (rd_step_delta_l ..)))))) }

def rd_seed_env_l (U : M.Domain) : Env M 1 := ⟨fun _ => U, fun _ => U⟩

theorem rd_iter_op_sat_l (hKP : M.Models KP) (U F Y : M.Domain) :
    rd_iter_op_s.schema.denote (rd_seed_env_l U) F Y ↔ ∃ R V H,
      Rd_fun_d .range F F F R ∧ Rd_fun_d .union R R R V ∧ M.IsUnionOfTwo H U V ∧ Rd_step_d H Y := by
  rw [S1_binary.sat_l]
  simp only [rd_iter_op_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_graph_sat_l hKP, join0_sat_l, rd_step_sat_l hKP]
  change (∃ T R, M.mem R T ∧ ∃ V, M.mem V T ∧ ∃ H, M.mem H T ∧ _) ↔ _
  constructor
  · rintro ⟨_, R, _, V, _, H, _, hr, hv, hh, hy⟩
    exact ⟨R, V, H, hr, hv, hh, hy⟩
  · rintro ⟨R, V, H, hr, hv, hh, hy⟩
    obtain ⟨P, hp⟩ := KP.exists_pair hKP R V
    obtain ⟨T, ht⟩ := KP.exists_insert hKP P H
    exact ⟨T, R, (ht R).mpr (Or.inl ((hp R).mpr (Or.inl rfl))),
      V, (ht V).mpr (Or.inl ((hp V).mpr (Or.inr rfl))), H, (ht H).mpr (Or.inr rfl), hr, hv, hh, hy⟩

theorem rd_iter_op_total_l (hKP : M.Models KP) (U F : M.Domain) :
    ∃ Y, rd_iter_op_s.schema.denote (rd_seed_env_l U) F Y := by
  obtain ⟨R, hr⟩ := rd_fun_exists_l hKP .range F F F
  obtain ⟨V, hv⟩ := rd_fun_exists_l hKP .union R R R
  obtain ⟨H, hh⟩ := KP.exists_unionOfTwo hKP U V
  obtain ⟨Y, hy⟩ := rd_step_exists_l hKP H
  exact ⟨Y, (rd_iter_op_sat_l hKP U F Y).mpr ⟨R, V, H, hr, hv, hh, hy⟩⟩

theorem rd_iter_op_unique_l (hKP : M.Models KP) (U F Y Z : M.Domain)
    (hy : rd_iter_op_s.schema.denote (rd_seed_env_l U) F Y)
    (hz : rd_iter_op_s.schema.denote (rd_seed_env_l U) F Z) : Y = Z := by
  obtain ⟨R, V, H, hr, hv, hh, hy⟩ := (rd_iter_op_sat_l hKP U F Y).mp hy
  obtain ⟨R', V', H', hr', hv', hh', hz⟩ := (rd_iter_op_sat_l hKP U F Z).mp hz
  have er := rd_fun_unique_l hKP.1 hr hr'; subst R'
  have ev := rd_fun_unique_l hKP.1 hv hv'; subst V'
  have eh := hKP.1.eq_of_same_members H H' (fun t => (hh t).trans (hh' t).symm); subst H'
  exact rd_step_unique_l hKP.1 hy hz

def Rd_iter_d (U a Y : M.Domain) : Prop := Rc_value_d rd_iter_op_s (rd_seed_env_l U) a Y

def rd_iter_m {n} (U a Y : Term n) : Formula 1 n :=
  binary_pred_m (rc_value_s rd_iter_op_s).schema (fun _ => U) a Y
derive_free_closed rd_iter_m

theorem rd_iter_sat_l (hE : Extensional M) {n} (ρ : Env M n) (U a Y : Term n) :
    Formula.satisfies ρ (rd_iter_m U a Y) ↔ Rd_iter_d (U.eval ρ) (a.eval ρ) (Y.eval ρ) := by
  rw [rd_iter_m, binary_pred_sat_l]
  apply Iff.trans ?_ (rc_value_sat_l hE rd_iter_op_s (rd_seed_env_l (U.eval ρ)) (a.eval ρ) (Y.eval ρ))
  exact Formula.closed_env_l _ (rc_value_s rd_iter_op_s).schema.freeClosed rfl

theorem rd_iter_exists_l (hM : M.Models KPi) (U a : M.Domain) : ∃ Y, Rd_iter_d U a Y :=
  rc_value_exists_l hM _ _ (rd_iter_op_total_l (KPi.models_iff_l.mp hM).1 U)
    (rd_iter_op_unique_l (KPi.models_iff_l.mp hM).1 U) a

theorem rd_iter_unique_l (hM : M.Models KPi) {U a Y Z : M.Domain}
    (hy : Rd_iter_d U a Y) (hz : Rd_iter_d U a Z) : Y = Z :=
  rc_value_unique_l hM _ _ (rd_iter_op_unique_l (KPi.models_iff_l.mp hM).1 U) hy hz

/-- 展开方程中的每个前值仍使用同一个实际 Σ₁ 递归关系。 -/
theorem rd_iter_equation_l (hM : M.Models KPi) {U a Y : M.Domain} (hy : Rd_iter_d U a Y) :
    ∃ H, Rd_step_d H Y ∧ ∀ t, M.mem t H ↔ M.mem t U ∨ ∃ b, M.mem b a ∧ ∃ V, Rd_iter_d U b V ∧ M.mem t V := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨G, _, hop, hg⟩ := rc_value_equation_l hM rd_iter_op_s (rd_seed_env_l U)
    (rd_iter_op_unique_l hKP U) hy
  obtain ⟨R, V, H, hr, hv, hh, hY⟩ := (rd_iter_op_sat_l hKP U G Y).mp hop
  refine ⟨H, hY, fun t => (hh t).trans (or_congr_right ?_)⟩
  rw [hv t]
  change (∃ v, M.mem v R ∧ M.mem t v) ↔ _
  constructor
  · rintro ⟨v, hvR, htv⟩
    obtain ⟨b, hbg⟩ := (hr v).mp hvR
    exact ⟨b, ((hg b v).mp hbg).1, v, ((hg b v).mp hbg).2, htv⟩
  · rintro ⟨b, hb, v, hbv, htv⟩
    exact ⟨v, (hr v).mpr ⟨b, (hg b v).mpr ⟨hb, hbv⟩⟩, htv⟩

theorem rd_step_mono_l {U V X Y : M.Domain} (hu : M.MemberSubset U V)
    (hx : Rd_step_d U X) (hy : Rd_step_d V Y) : M.MemberSubset X Y := by
  intro t ht
  apply (hy t).mpr
  rcases (hx t).mp ht with ht | ⟨k, a, b, c, ha, hb, hc, h⟩
  · exact Or.inl (hu t ht)
  · exact Or.inr ⟨k, a, b, c, hu a ha, hu b hb, hu c hc, h⟩

theorem rd_iter_mono_l (hM : M.Models KPi) {U a b X Y : M.Domain} (hab : M.MemberSubset a b)
    (hx : Rd_iter_d U a X) (hy : Rd_iter_d U b Y) : M.MemberSubset X Y := by
  obtain ⟨H, hH, hh⟩ := rd_iter_equation_l hM hx
  obtain ⟨K, hK, hk⟩ := rd_iter_equation_l hM hy
  exact rd_step_mono_l (fun t ht => (hk t).mpr (((hh t).mp ht).imp_right
    (fun ⟨c, hc, V, hv, ht⟩ => ⟨c, hab c hc, V, hv, ht⟩))) hH hK

end YesMetaZFC.SetTheory.InnerModel
