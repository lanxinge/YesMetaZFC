import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCandidate

/-! # 从原历史恢复继续分支的查询与候选

辅助走法的解码唯一性识别已发出记录中的 ℓ、t、κ、u 和三个内部元数。
原表读取同一个节点查询与 dcp 弹性；非空分支保留所选旧轮及原超过关系。
全程只解包已反射的真公式，不给工作层附加 ZF 模型性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_issued_query_l (ρ : Env M 46) (valid : Formula.satisfies ρ tg_issued0_m) :
    ∃ h x s B U D r m b q f,
      Fseq_end_d I (ρ.bound 0) (ρ.bound 20) h (ρ.bound 21) ∧
      (Fn0_d (ρ.bound 19) (ρ.bound 6) x ∧ ∀ i v, M.mem i (ρ.bound 19) →
        (Rd_entry_d i v x ↔ Tg_event_d I (ρ.bound 4) i (ρ.bound 3) h v)) ∧
      M.IsRestrictionOf I s x (ρ.bound 26) ∧
      Tg_query_data_d (ρ.bound 11) (ρ.bound 24) (ρ.bound 26) s (ρ.bound 23) B U D r m b q f ∧
      M.MemberSubset (ρ.bound 25) D ∧ M.mem f (ρ.bound 25) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 27, ρ.bound 28, ρ.bound 26,
        s, ρ.bound 23, r, m, b, q, f].get i, ρ.free⟩ : Env M 12) tg_query_row0_m ∧
      ((ρ.bound 19 = ρ.bound 1 ∧ M.mem (ρ.bound 6) B) ∨
        ∃ j a ℓ t τ u, M.SuccessorOf (ρ.bound 19) j ∧ Tg_event_d I (ρ.bound 4) j (ρ.bound 1) h a ∧
          Tg_aux_data_d a ℓ t τ u ∧ M.mem τ (ρ.bound 24)) ∧
      (ρ.bound 23 ≠ ρ.bound 1 → Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2,
        ρ.bound 4, ρ.bound 5, ρ.bound 19, h, ρ.bound 22, ρ.bound 23, ρ.bound 24, ρ.bound 26,
        ρ.bound 28, U, D, ρ.bound 25].get i, ρ.free⟩ : Env M 15) tg_continue0_m) ∧
      M.mem (ρ.bound 26) (ρ.bound 0) ∧ M.mem (ρ.bound 27) (ρ.bound 0) ∧ M.mem (ρ.bound 28) (ρ.bound 0) ∧
      ∃ χ : Env M 12, (∀ i : Fin 5, χ.bound (i.castAdd 7) =
        [ρ.bound 25, ρ.bound 28, ρ.bound 0, ρ.bound 24, ρ.bound 27].get i) ∧ Formula.satisfies χ tg_candidate0_m := by
  have state := (tg_issued_sat_l I hE ρ).mp valid
  have original := state.auxiliary
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind, tg_aux0_m, tg_aux_data_sat_l hE,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isRestriction_iff I, tg_query_data_sat_l hE, Formula.satisfies_subset_iff,
    tg_ee_data_sat_l hE, tg_elastic_sat_l I hE, Definitional.Term.eval_weaken] at original
  obtain ⟨h, endt, ℓ, t, κ, u, k, l, N, x, s, B, U, D, r, m, b, q, f, C, V, W, g₀, g₁, g₂, g₃,
    move, _, labels, first, last, digits, rest, request, row, sub, elastic, drop, node, growth, fork⟩ := original
  obtain ⟨eℓ, et, eκ, eu⟩ := move.unique_l state.move
  change ℓ = ρ.bound 22 at eℓ
  change t = ρ.bound 23 at et
  change κ = ρ.bound 24 at eκ
  change u = ρ.bound 25 at eu
  subst ℓ t κ u
  have ek : k = ρ.bound 26 := labels.domain_eq_l hE state.labels
  subst k
  have el : l = ρ.bound 27 := first.eq hE state.first
  subst l
  have eN : N = ρ.bound 28 := last.eq hE state.last
  subst N
  -- 同一表项的读取保留原节点常量；不会重新选择一份不同的查询。
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff] at tables
  have query := tables.1.2.2.2
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_query_data_sat_l hE, Formula.satisfies_isSuccessor_iff, tg_query_request_m,
    Formula.satisfies_bind, tg_query_base_m] at query
  simp only [tg_query_request_m, Formula.satisfies_bind] at request
  obtain ⟨l, N, first, last, _, _, _, base⟩ :=
    query (ρ.bound 24) state.bound (ρ.bound 26) s (ρ.bound 23) B U D r m b q f (by
      apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i) row
  have el : l = ρ.bound 27 := first.eq hE state.first
  subst l
  have eN : N = ρ.bound 28 := last.eq hE state.last
  subst N
  have facts := request
  simp only [tg_query_request0_m, Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff] at facts
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have omega := (Formula.satisfies_isOmega_iff ..).mp rules.1
  obtain ⟨l, succ, hl⟩ := omega.1.2 (ρ.bound 26) facts.2.1
  have eq : l = ρ.bound 27 := succ.eq hE state.first
  have finite : M.mem (ρ.bound 27) (ρ.bound 0) := eq ▸ hl
  obtain ⟨N, succN, hN⟩ := omega.1.2 (ρ.bound 27) finite
  have eqN : N = ρ.bound 28 := succN.eq hE state.last
  have finiteN : M.mem (ρ.bound 28) (ρ.bound 0) := eqN ▸ hN
  have language := tables.1.1
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isLimitOrdinal_iff, tg_ee_data_sat_l hE, ee_language_m, Formula.satisfies_bind] at language
  have language := language (ρ.bound 24) state.bound (ρ.bound 27) finite C V W g₀ g₁ g₂ g₃ facts.1 elastic
  simp only [tg_growth_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE, tg_aux_data_sat_l hE,
    Definitional.Term.eval_weaken] at growth
  simp only [tg_digits_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE, tg_event_sat_l I hE, Definitional.Term.eval_weaken] at digits
  refine ⟨h, x, s, B, U, D, r, m, b, q, f, endt, digits, rest, row, sub, node, ?_, growth, ?_,
    facts.2.1, finite, finiteN, ?_⟩
  · apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨?_, (Formula.satisfies_conj_iff ..).mpr ⟨state.first, state.last⟩⟩
    apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l (ρ := _) (η := _) ?_).mp base
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  · intro ne
    simp only [Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
      tg_continue_m, Formula.satisfies_bind] at fork
    have cont := fork.elim (fun reset => (ne reset.1).elim) And.right
    apply (Formula.closed_env_l tg_continue0_m tg_continue0_closed_l (ρ := _) (η := _) ?_).mp cont
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))) i
  · let χ : Env M 12 := ⟨fun i => [ρ.bound 25, ρ.bound 28, ρ.bound 0, ρ.bound 24, ρ.bound 27,
      C, V, W, g₀, g₁, g₂, g₃].get i, ρ.free⟩
    refine ⟨χ, ?_, (Formula.satisfies_conj_iff ..).mpr ⟨?_, (tg_elastic_sat_l I hE ..).mpr drop⟩⟩
    · intro i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
    · apply (Formula.satisfies_rename ..).mpr
      apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l (ρ := _) (η := _) ?_).mp language
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
