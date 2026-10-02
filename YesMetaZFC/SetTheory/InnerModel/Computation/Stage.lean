import YesMetaZFC.SetTheory.InnerModel.Computation.Sigma1
import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # J 搜索的单步计算

第 a 步先按现有内部递归构造 Jₐ，再运行独立集合程序。Σ₁ 证书同时保存
层级递归证据与程序的中间值；阶段对象不是外部枚举或未解释的输入接口。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Cs_stage_d {n} (p : Cp_code (n + 1)) (ρ : Env M n) (a y : M.Domain) : Prop :=
  ∃ A, Jh_value_d a A ∧ Cp_eval_d p (ρ.push A) y

def cs_stage_s {n} (p : Cp_code (n + 1)) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj ((rc_value_s jh_op_s).matrix_m Fin.elim0 (.bound 4) (.bound 1) .newest)
        (cp_cert_m p (Fin.cases (.bound 1) (fun i => .bound ⟨i.val + 5, by omega⟩)) (.bound 3) (.bound 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj ((rc_value_s jh_op_s).matrix.delta0.bind_l _) (cp_cert_delta_l ..))) }

theorem cs_stage_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (a y : M.Domain) :
    (cs_stage_s p).schema.denote ρ a y ↔ Cs_stage_d p ρ a y := by
  let φ := rc_value_s jh_op_s
  let η : Env M 0 := ⟨Fin.elim0, ρ.free⟩
  have hj A : φ.schema.denote η a A ↔ Jh_value_d a A :=
    Formula.closed_env_l _ φ.schema.freeClosed (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))
  have h0 {d} (ν : Env M d) :
      (⟨fun i => (Fin.elim0 i : Term d).eval ν, ν.free⟩ : Env M 0) = ⟨Fin.elim0, ν.free⟩ := by
    rw [Env.mk.injEq]
    exact ⟨funext (fun i => Fin.elim0 i), rfl⟩
  rw [S1_binary.sat_l]
  simp only [cs_stage_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    S1_binary.matrix_sat_l, cp_cert_sat_l hKP, cp_env_cons_l, h0]
  change (∃ T A, M.mem A T ∧ ∃ W, M.mem W T ∧
    φ.matrix_binary.toBinarySchema.denote (η.push a) A W ∧ Cp_cert_d p (ρ.push A) y T) ↔ _
  constructor
  · rintro ⟨T, A, _, W, _, hw, hy⟩
    exact ⟨A, (hj A).mp ((φ.sat_l η a A).mpr ⟨W, hw⟩), cp_cert_sound_l hKP.1 p _ hy⟩
  · rintro ⟨A, ha, hy⟩
    obtain ⟨W, hw⟩ := (φ.sat_l η a A).mp ((hj A).mpr ha)
    obtain ⟨B, hb⟩ := cp_cert_complete_l hKP hy
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [A, W, B]
    exact ⟨T, A, (ht A (by simp)).2, W, (ht W (by simp)).2, hw, cp_cert_mono_l p _ (ht B (by simp)).1 hb⟩

theorem cs_stage_total_l (hM : M.Models KPi) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (a : M.Domain) :
    ∃ y, Cs_stage_d p ρ a y := by
  obtain ⟨A, ha⟩ := jh_value_exists_l hM a
  obtain ⟨y, hy⟩ := cp_eval_total_l (KPi.models_iff_l.mp hM).1 p (ρ.push A)
  exact ⟨y, A, ha, hy⟩

theorem cs_stage_unique_l (hM : M.Models KPi) {n} {p : Cp_code (n + 1)} {ρ : Env M n} {a y z : M.Domain}
    (hy : Cs_stage_d p ρ a y) (hz : Cs_stage_d p ρ a z) : y = z := by
  obtain ⟨A, ha, hy⟩ := hy
  obtain ⟨B, hb, hz⟩ := hz
  have he := jh_value_unique_l hM ha hb; subst B
  exact cp_eval_unique_l (KPi.models_iff_l.mp hM).1.1 p _ hy hz

end YesMetaZFC.SetTheory.InnerModel
