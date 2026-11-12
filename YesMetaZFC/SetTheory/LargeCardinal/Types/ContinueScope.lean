import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 真实继续输入中两份类型的极限秩界

原程序给出自然数元数与槽位；原超过关系给出真实类型及其查询域上界。
包含旧 κ 的极限 Vα 包含旧常量域、查询域、类型及完整名字域；包含当前 τ
的极限秩段包含当前常量域、查询域和整个候选。两份类型上界都来自实际实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tc_seed_scope_l {ω η C α B : M.Domain} (hω : M.IsOmega ω)
    (rankC : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 29) (hw : (ρ.bound 0).val = ω)
    (rank : V_d I α B) (limit : M.IsLimitOrdinal α) (member : M.mem (ρ.bound 1).val B)
    (seed : Formula.satisfies ρ tc_seed0_m) :
    M.mem (ρ.bound 3).val ω ∧ M.mem (ρ.bound 5).val B ∧
      M.mem (ρ.bound 6).val B ∧ M.mem (ρ.bound 7).val B ∧
      (∀ j : Fin 9, M.mem (ρ.bound ([14,16,21,22,23,24,25,26,27].get j)).val ω) ∧
      ∃ A, M.mem A B ∧ Tn_names_d (ρ.bound 3).val (ρ.bound 5).val A := by
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, program, language, _, _, _, _, _, exceeds, _⟩ := seed
  simp only [ts_program_m, Formula.satisfies_bind, ts_program0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at program
  obtain ⟨hn, hb, hz, _, h₀, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := program
  have hn : M.mem (ρ.bound 3).val ω := hw ▸ hn
  have hb : M.mem (ρ.bound 14).val ω := hw ▸ hb
  have hz : M.mem (ρ.bound 16).val ω := hw ▸ hz
  have natural {i : Fin 29} (h : (rt_model_l C nc).mem (ρ.bound i) (ρ.bound 14)) :
      M.mem (ρ.bound i).val ω := hω.transitive (ZF.modelsKP hZF) _ hb _ h
  have slots : ∀ j : Fin 9, M.mem (ρ.bound ([14,16,21,22,23,24,25,26,27].get j)).val ω :=
    Fin.cases hb (Fin.cases hz (Fin.cases (natural h₀) (Fin.cases (natural h₁)
      (Fin.cases (natural h₂) (Fin.cases (natural h₃) (Fin.cases (natural h₄)
        (Fin.cases (natural h₅) (Fin.cases (natural h₆) (fun j => Fin.elim0 j)))))))))
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  obtain ⟨domain, hκ, base, constants, _⟩ := language
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 1)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hκ)
  have hκα := ZF.v_ordinal_height_l hZF rank hκ.1 member
  have hκη := ZF.v_ordinal_height_l hZF rankC hκ.1 (ρ.bound 1).property
  obtain ⟨A₀, rA₀⟩ := ZF.v_exists_l I hZF hκ.1
  have hA₀ := ZF.v_mem_l I hZF rA₀ rankC hκη
  have base : Vr_d C (ρ.bound 1).val (ρ.bound 4).val :=
    (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp base
  have eq := vr_agree_l hZF fs.transitive (ρ.bound 4).property rA₀ (fs.transitive _ hA₀) base
  have full : V_d I (ρ.bound 1).val (ρ.bound 4).val := by rw [eq]; exact rA₀
  have constants : Formula.satisfies ρ (tt_constants0_m (.bound 1) (.bound 4) (.bound 5)) :=
    (tt_constants0_sat_l ext ..).mpr ((tt_constants0_sat_l ext ..).mp constants)
  have constants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 1) (.bound 4) (.bound 5)) ρ).mp constants)
  have hU : M.mem (ρ.bound 5).val B := tt_constants_rank_l hZF rank limit hκα full constants
  have hwB : M.mem ω B := v_subset_mem_l I rank member (hω.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  simp only [ee_domain_pack_m, Formula.satisfies_bind, ee_domain_pack0_m, Formula.satisfies_conj_iff] at domain
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ (.bound 0) (.bound 3) (.bound 5) (.bound 6) hw).mp domain.2.1
  have pool : Tt_pool_d I ω (ρ.bound 3).val (ρ.bound 5).val (ρ.bound 6).val := ⟨A, E, names, seq, product⟩
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hn hU
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff] at exceeds
  obtain ⟨_, _, η₀, Y, c, R, s, _, _, realized, _⟩ := exceeds
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at realized
  have truth := realized.2.2.2.2.2.2
  simp only [tt_truth_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at truth
  have sub : M.MemberSubset (ρ.bound 7).val (ρ.bound 6).val := fun x hx =>
    ((truth ⟨x, fs.transitive _ (ρ.bound 7).property x hx⟩).mp hx).1
  exact ⟨hn, hU, hD, v_subset_mem_l I rank hD sub, slots,
    A, names.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hn hU, names⟩

/-- 当前候选的真实实现也给出查询域上界；包含 τ 的极限秩段因此包含整个候选。 -/
theorem tc_current_scope_l {ω η C α B : M.Domain} (hω : M.IsOmega ω)
    (rankC : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 29) (hw : (ρ.bound 0).val = ω)
    (rank : V_d I α B) (limit : M.IsLimitOrdinal α) (member : M.mem (ρ.bound 8).val B)
    (seed : Formula.satisfies ρ tc_seed0_m) :
    M.mem (ρ.bound 9).val ω ∧ M.mem (ρ.bound 11).val B ∧
      M.mem (ρ.bound 12).val B ∧ M.mem (ρ.bound 13).val B := by
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, hτ, _, base, constants, _, exceeds, _⟩ := seed
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 8)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hτ)
  have hτα := ZF.v_ordinal_height_l hZF rank hτ.1 member
  have hτη := ZF.v_ordinal_height_l hZF rankC hτ.1 (ρ.bound 8).property
  obtain ⟨A, rA⟩ := ZF.v_exists_l I hZF hτ.1
  have hA := ZF.v_mem_l I hZF rA rankC hτη
  have base : Vr_d C (ρ.bound 8).val (ρ.bound 10).val :=
    (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp base
  have eq := vr_agree_l hZF fs.transitive (ρ.bound 10).property rA (fs.transitive _ hA) base
  have full : V_d I (ρ.bound 8).val (ρ.bound 10).val := by rw [eq]; exact rA
  have constants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 8) (.bound 10) (.bound 11)) ρ).mp constants)
  have hU : M.mem (ρ.bound 11).val B := tt_constants_rank_l hZF rank limit hτα full constants
  have hwB : M.mem ω B := v_subset_mem_l I rank member (hω.subset_limitOrdinal (ZF.modelsKP hZF) hτ)
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff] at exceeds
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, actual⟩ := exceeds
  simp only [ts_at_m, Formula.satisfies_bind, ts_at0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff] at actual
  obtain ⟨_, _, _, _, _, _, _, _, _, realized, _⟩ := actual
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at realized
  have hn : M.mem (ρ.bound 9).val ω := hw ▸ realized.2.1
  obtain ⟨A₀, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc _ _ _ _ _ (by exact hw)).mp realized.2.2.2.2.2.1
  have pool : Tt_pool_d I ω (ρ.bound 9).val (ρ.bound 11).val (ρ.bound 12).val := ⟨A₀, E, names, seq, product⟩
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hn hU
  have truth := realized.2.2.2.2.2.2
  simp only [tt_truth_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at truth
  have sub : M.MemberSubset (ρ.bound 13).val (ρ.bound 12).val := fun x hx =>
    ((truth ⟨x, fs.transitive _ (ρ.bound 13).property x hx⟩).mp hx).1
  exact ⟨hn, hU, hD, v_subset_mem_l I rank hD sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
