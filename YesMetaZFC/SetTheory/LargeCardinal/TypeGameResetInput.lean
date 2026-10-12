import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControl

/-! # 原重置走法自动成为更新输入

空标签列强制元数为零。固定两张语言表识别同一 Vκ 及其常量域，原完整
重置类型与原 dcp 弹性随即给出更新输入；程序从开局时的实际表中读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.reset_input_l {p : Tg_params_d M.Domain} {X n h a ℓ κ u : M.Domain}
    (setup : Tg_setup_d hZFC p X) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (aux : Tg_aux_d hZF p n h a) (data : Tg_aux_data_d a ℓ p.e κ u) :
    ∃ v : Fin 38 → M.Domain,
      Formula.satisfies (⟨v, fun _ => p.ω⟩ : Env M 38) tg_seed0_m ∧
      (∀ i : Fin 5, v (i.castAdd 33) = [p.ω, p.e, p.δ, p.S, p.ν].get i) ∧
      v 6 = p.e ∧ v 23 = v 5 ∧ v 24 = p.e ∧ v 25 = p.e ∧ v 26 = p.e ∧
      Tg_aux_data_d a ℓ (v 25) (v 5) (v 18) ∧
      Tg_ee_data_d p.E (v 5) (v 7) (v 14) (v 15) (v 16) ⟨v 27, v 28, v 29, v 30⟩ ∧
      Tg_program_data_d p.P (v 7) (v 20) (v 22) (Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33)
        (Fin.cases (v 34) (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))) ∧
      (n = p.e → M.mem p.A (v 14)) := by
  obtain ⟨ℓ₀, t, κ₀, u₀, k, l, N, x, s, B, U, D, r₀, m, b₀, q, f, C, V, W, g₀, g₁, g₂, g₃,
    parsed, hk, ft, hl, hN, _, _, request, query, _, ee, elastic, _, growth, branch⟩ := aux
  obtain ⟨rfl, rfl, rfl, rfl⟩ := parsed.unique_l data
  have ke : k = p.e := hZF.1.eq_of_same_members k p.e (fun i => iff_of_false
    (fun hi => (ft.2.1 i hi).elim fun y hy => hy.2.elim fun z hz => setup.empty z hz.2) (setup.empty i))
  subst k
  obtain ⟨α, Y, c, R, r, height, rank, model, type, first, last⟩ :=
    branch.elim And.right (fun no => (no.1 rfl).elim)
  obtain ⟨l', N', hl', hN', target, _, _, _⟩ := setup.queries.read_l hZFC hk request query
  have el := hl'.eq hZF.1 hl
  subst l'
  have eN := hN'.eq hZF.1 hN
  subst N'
  have hlω := setup.omega.transitive hZF N target.finite l hN.predecessor_mem
  have language := setup.elastic.elim fun _ table => table.read_l hZFC hk hlω request.1 ee
  have eB := ZF.v_unique_l I hZF target.rank language.rank
  subst C
  have eU := hZF.1.eq_of_same_members U V (fun z => (target.constants z).trans (language.constants z).symm)
  subst V
  obtain ⟨v, drop, elastic⟩ := elastic
  obtain ⟨H, _, programs, _⟩ := setup.programs
  obtain ⟨b, z, σ, program, pdata, prog⟩ := programs.get_l hZFC hlω
  have set : Sg_set_d I p.e l r p.e := by
    intro x
    refine iff_of_false (setup.empty x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((hl i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))
  have node := (tg_node_empty_l I hZF.1 setup.empty).mpr root
  let v' : Fin 38 → M.Domain := fun i =>
    [p.ω, p.e, p.δ, p.S, p.ν, κ₀, p.e, l, N, α, Y, c, R, r, B, U, W, D, u₀, v,
      b, program, z, κ₀, p.e, p.e, p.e, g₀, g₁, g₂, g₃, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have slots : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies (⟨v', fun _ => p.ω⟩ : Env M 38) tg_seed0_m := by
    simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff,
      Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff,
      woodin_sat_l I hZF.1, tg_low_sat_l hZF, Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1,
      smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), ee_language_sat_l hZFC,
      td_dcp_sat_l I hZF.1, ee_elastic_sat_l, rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1,
      tg_node_sat_l I hZF.1, ts_program_sat_l hZF, tt_eval_cases_l, tg_bound_raw_sat_l I hZF.1]
    obtain ⟨hδν, Y₀, rank₀, hS⟩ := setup.low.read_l hZF setup.limit.1
    exact ⟨setup.omega, setup.empty, num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty),
      woodin, setup.low, root, hk, hl, hN, height, rank, model, type, language, drop, elastic,
      first, last, set, node, slots.symm ▸ prog, hk, v_ordinal_l I rank₀, hδν, Y₀, rank₀, hS⟩
  refine ⟨v', valid, ?_, rfl, rfl, rfl, rfl, rfl, data, ee, slots.symm ▸ pdata, ?_⟩
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · intro zero
    rcases growth with ⟨_, hA⟩ | ⟨j, _, _, _, _, _, succ, _⟩
    · exact hA
    · exact (setup.empty j (zero ▸ succ.predecessor_mem)).elim

end YesMetaZFC.SetTheory.LargeCardinal
