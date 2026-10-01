import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure

/-! # 最小闭包的 Σ₁ 公开接口 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rd_closure_d (U C : M.Domain) : Prop := ∃ ω, Omega0_d ω ∧ Rd_iter_d U ω C

def rd_closure_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (.conj (omega0_m .newest)
      ((rc_value_s rd_iter_op_s).matrix_m (fun _ => .bound 3) .newest (.bound 2) (.bound 1)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.conj (omega0_delta_l _)
      ((rc_value_s rd_iter_op_s).matrix.delta0.bind_l _)) }

theorem rd_closure_sat_l (hE : Extensional M) (ρ : Env M 0) (U C : M.Domain) :
    rd_closure_s.schema.denote ρ U C ↔ Rd_closure_d U C := by
  have hc ω T : (rc_value_s rd_iter_op_s).matrix_binary.toBinarySchema.denote
      ((⟨fun _ => U, ρ.free⟩ : Env M 1).push ω) C T ↔
      ∃ A F, Rc_cert_d rd_iter_op_s (rd_seed_env_l U) A F T ∧ M.mem ω A ∧ Rd_entry_d ω C F := by
    apply Iff.trans ?_ (rc_matrix_sat_l hE rd_iter_op_s (rd_seed_env_l U) ω C T)
    exact Formula.closed_env_l _ (rc_value_s rd_iter_op_s).matrix.freeClosed rfl
  rw [S1_binary.sat_l]
  simp only [rd_closure_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    omega0_sat_l hE, S1_binary.matrix_sat_l]
  change (∃ T ω, M.mem ω T ∧ Omega0_d ω ∧
    (rc_value_s rd_iter_op_s).matrix_binary.toBinarySchema.denote
      ((⟨fun _ => U, ρ.free⟩ : Env M 1).push ω) C T) ↔ _
  simp only [hc]
  exact ⟨fun ⟨T, ω, _, hω, A, F, hF, ha, hy⟩ => ⟨ω, hω, T, A, F, hF, ha, hy⟩,
    fun ⟨ω, hω, T, A, F, hF, ha, hy⟩ => ⟨T, ω, hF.trans A hF.domain ω ha, hω, A, F, hF, ha, hy⟩⟩

theorem rd_closure_exists_l (hM : M.Models KPi) (U : M.Domain) : ∃ C, Rd_closure_d U C := by
  obtain ⟨ω, hω⟩ := omega0_exists_l hM
  obtain ⟨C, hc⟩ := rd_iter_exists_l hM U ω
  exact ⟨C, ω, hω, hc⟩

/-- 闭包、包含性和最小性均是已经证明的结论，而非构造的输入合同。 -/
theorem rd_closure_spec_l (hM : M.Models KPi) {U C : M.Domain} (hc : Rd_closure_d U C) :
    Rd_closed_d C ∧ M.MemberSubset U C ∧
      ∀ D, Rd_closed_d D → M.MemberSubset U D → M.MemberSubset C D := by
  obtain ⟨ω, hω, hc⟩ := hc
  have hs := rd_iter_omega_closed_l hM hω hc
  exact ⟨hs.1, hs.2, fun _ hd hu => rd_iter_le_l hM hd hu hc⟩

theorem rd_closure_unique_l (hM : M.Models KPi) {U C D : M.Domain}
    (hc : Rd_closure_d U C) (hd : Rd_closure_d U D) : C = D := by
  have hc := rd_closure_spec_l hM hc
  have hd := rd_closure_spec_l hM hd
  exact (KPi.models_iff_l.mp hM).1.1.eq_of_same_members C D
    (fun t => ⟨hc.2.2 D hd.1 hd.2.1 t, hd.2.2 C hc.1 hc.2.1 t⟩)

theorem rd_closure_transitive_l (hM : M.Models KPi) {U C : M.Domain}
    (hu : M.TransitiveSet U) (hc : Rd_closure_d U C) : M.TransitiveSet C :=
  hc.elim fun _ h => rd_iter_transitive_l hM hu h.2

theorem rd_closure_mono_l (hM : M.Models KPi) {U V C D : M.Domain} (huv : M.MemberSubset U V)
    (hc : Rd_closure_d U C) (hd : Rd_closure_d V D) : M.MemberSubset C D :=
  (rd_closure_spec_l hM hc).2.2 D (rd_closure_spec_l hM hd).1
    (fun t ht => (rd_closure_spec_l hM hd).2.1 t (huv t ht))

end YesMetaZFC.SetTheory.InnerModel
