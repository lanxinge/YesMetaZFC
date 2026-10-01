import YesMetaZFC.SetTheory.InnerModel.Computation.Delta0

/-! # Δ₁ 程序图与 Σ₁ 见证验证的双向编译

总程序的图及其补集各有实际 Σ₁ 公式。任意 Σ₁ 矩阵编译为集合程序，
反向将接受执行及其见证编译为 Σ₁ 矩阵；这里不引入无界搜索指令。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_negative_s {n} (p : Cp_code (n + 1)) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest
      (.conj (cp_cert_m p (fun i => .bound ⟨i.val + 3, by omega⟩) .newest (.bound 1))
        (.neg (Formula.extensionalEq .newest (.bound 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.conj (cp_cert_delta_l ..) (.neg (.atom _ _ _))) }

theorem cp_negative_matrix_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (x y T : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push T) (cp_negative_s p).matrix.body ↔
      ∃ z, M.mem z T ∧ Cp_cert_d p (ρ.push x) z T ∧ z ≠ y := by
  simp only [cp_negative_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    cp_cert_sat_l hKP, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1]
  rfl

theorem cp_negative_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (x y : M.Domain) :
    (cp_negative_s p).schema.denote ρ x y ↔ ¬ Cp_eval_d p (ρ.push x) y := by
  rw [S1_binary.sat_l]
  simp only [cp_negative_matrix_l hKP]
  constructor
  · rintro ⟨T, z, _, hz, hn⟩ hy
    exact hn (cp_eval_unique_l hKP.1 p _ (cp_cert_sound_l hKP.1 p _ hz) hy)
  · intro hn
    obtain ⟨z, A, hz⟩ := cp_cert_total_l hKP p (ρ.push x)
    obtain ⟨T, ht⟩ := cp_cover_l hKP [A, z]
    exact ⟨T, z, (ht z (by simp)).2, cp_cert_mono_l p _ (ht A (by simp)).1 hz,
      fun he => hn (he ▸ cp_cert_sound_l hKP.1 p _ hz)⟩

/-- 接受指输出非空；对布尔程序恰好是输出 {∅}。 -/
def Cp_accept_d {n} (p : Cp_code n) (ρ : Env M n) : Prop :=
  ∃ y, Cp_eval_d p ρ y ∧ ∃ t, M.mem t y

theorem cp_accept_bit_l (hKP : M.Models KP) {n} {p : Cp_code n} {ρ : Env M n} {P : Prop}
    (h : Cp_decides_d p ρ P) : Cp_accept_d p ρ ↔ P := by
  refine ⟨fun ⟨y, hy, t, ht⟩ => ((h y hy t).mp ht).2, fun hp => ?_⟩
  obtain ⟨y, hy⟩ := cp_eval_total_l hKP p ρ
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  exact ⟨y, hy, e, (h y hy e).mpr ⟨he, hp⟩⟩

def cp_verifier_l {n} (φ : S1_binary n) : Cp_code (n + 3) := cp_delta_l φ.matrix

theorem cp_verifier_sat_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    φ.schema.denote ρ x y ↔ ∃ w, Cp_accept_d (cp_verifier_l φ) (((ρ.push x).push y).push w) := by
  rw [S1_binary.sat_l]
  apply exists_congr; intro w
  exact (cp_accept_bit_l hKP (fun v hv => (cp_delta_correct_l hKP φ.matrix ((ρ.push x).push y) w v).mp hv)).symm

/-- 槽位依次是见证、输出、输入、参数；一个集合同时界住见证与计算证书。 -/
def cp_witness_s {n} (p : Cp_code (n + 3)) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (cp_cert_m p (Fin.cases (.bound 1) (fun i => .bound ⟨i.val + 3, by omega⟩)) .newest (.bound 2))
        (Formula.existsMem .newest .truth)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (cp_cert_delta_l ..) (.existsMem _ .truth))) }

theorem cp_witness_matrix_l (hKP : M.Models KP) {n} (p : Cp_code (n + 3)) (ρ : Env M n) (x y T : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push T) (cp_witness_s p).matrix.body ↔
      ∃ w, M.mem w T ∧ ∃ v, M.mem v T ∧ Cp_cert_d p (((ρ.push x).push y).push w) v T ∧ ∃ t, M.mem t v := by
  simp only [cp_witness_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_truth_iff, cp_cert_sat_l hKP, cp_env_cons_l, and_true]
  rfl

theorem cp_witness_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 3)) (ρ : Env M n) (x y : M.Domain) :
    (cp_witness_s p).schema.denote ρ x y ↔ ∃ w, Cp_accept_d p (((ρ.push x).push y).push w) := by
  rw [S1_binary.sat_l]
  simp only [cp_witness_matrix_l hKP]
  constructor
  · rintro ⟨T, w, _, v, _, hv, ht⟩
    exact ⟨w, v, cp_cert_sound_l hKP.1 p _ hv, ht⟩
  · rintro ⟨w, v, hv, hn⟩
    obtain ⟨A, ha⟩ := cp_cert_complete_l hKP hv
    obtain ⟨T, ht⟩ := cp_cover_l hKP [A, w, v]
    exact ⟨T, w, (ht w (by simp)).2, v, (ht v (by simp)).2,
      cp_cert_mono_l p _ (ht A (by simp)).1 ha, hn⟩

theorem cp_verifier_roundtrip_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    (cp_witness_s (cp_verifier_l φ)).schema.denote ρ x y ↔ φ.schema.denote ρ x y :=
  (cp_witness_sat_l hKP _ ρ x y).trans (cp_verifier_sat_l hKP φ ρ x y).symm

end YesMetaZFC.SetTheory.InnerModel
