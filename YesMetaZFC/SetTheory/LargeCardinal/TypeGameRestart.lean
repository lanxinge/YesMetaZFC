import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCandidate
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRound
import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramTransfer

/-! # 恢复节点后在同一反射层重新启动

旧树及其低层界、候选的原弹性、恢复出的完整实现与原程序直接组成下一轮。
这里只重排同一个模型中的见证，不要求反射层满足 ZF，也不增添反射句子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_restart_env_d (ρ : Env M 54) (χ : Env M 12) (ε : Env M 29) (π : Env M 12)
    (v : M.Domain) : Env M 38 :=
  ⟨fun i => [ρ.bound 16, ρ.bound 17, ρ.bound 18, ρ.bound 19, ρ.bound 20, χ.bound 3,
    ρ.bound 23, ρ.bound 24, χ.bound 1, ε.bound 27, ε.bound 6, ε.bound 5, ε.bound 4,
    ε.bound 3, χ.bound 5, χ.bound 6, χ.bound 7, ε.bound 14, χ.bound 0, v,
    π.bound 2, π.bound 3, π.bound 4, ρ.bound 15, ε.bound 15, ε.bound 16, ε.bound 2,
    χ.bound 8, χ.bound 9, χ.bound 10, χ.bound 11,
    π.bound 5, π.bound 6, π.bound 7, π.bound 8, π.bound 9, π.bound 10, π.bound 11].get i, ρ.free⟩

/-- 一张图的实际恢复记录给出下一次更新的完整输入。 -/
theorem tg_restart_l (ρ : Env M 54) (χ : Env M 12) (ε : Env M 29) (π : Env M 12)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (recovered : Formula.satisfies ε tc_recovered0_m) (program : Formula.satisfies π ts_program0_m)
    -- 恢复记录中的 ω,e,k,l,n,U,δ,S,ν,u 逐项对应原对象。
    (same : ∀ i : Fin 10, ε.bound ([7, 8, 10, 11, 12, 13, 23, 24, 25, 28].get i) =
      [ρ.bound 16, ρ.bound 17, ρ.bound 23, ρ.bound 24, χ.bound 1, χ.bound 6,
        ρ.bound 18, ρ.bound 19, ρ.bound 20, χ.bound 0].get i)
    (hw : χ.bound 2 = ρ.bound 16) (hl : χ.bound 4 = ρ.bound 24)
    (pw : π.bound 0 = ρ.bound 16) (pn : π.bound 1 = ρ.bound 24)
    (below : M.mem (χ.bound 3) (ρ.bound 15)) :
    ∃ v, Formula.satisfies (tg_restart_env_d ρ χ ε π v) tg_seed0_m := by
  obtain ⟨seed, round⟩ := (Formula.satisfies_conj_iff ..).mp old
  let ρs := Env.reindex ρ (fun i : Fin 38 =>
    i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  have seed : Formula.satisfies ρs tg_seed0_m := (Formula.satisfies_rename ..).mp seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at seed
  obtain ⟨omega, empty, heω, woodin, low, root, _, _, succ, _, _, _, _, _, _, _, _, _, _, _, _, _, bound⟩ := seed
  -- δ 的序数性只从旧低层界读取；κ<κ' <δ 给出新候选的正确范围。
  have bounded := bound
  simp only [tg_bound_raw_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_mem_iff] at bounded
  have ord : M.IsOrdinal (ρ.bound 18) := bounded.1.mem bounded.2.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at round
  have hκδ := ord.transitive (ρ.bound 15) round.2.2.1 (χ.bound 3) below
  obtain ⟨language, elastic⟩ := (Formula.satisfies_conj_iff ..).mp candidate
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at elastic
  obtain ⟨v, drop, elastic⟩ := elastic
  let ξ := tg_restart_env_d ρ χ ε π v
  have nr := recovered
  simp only [tc_recovered0_m, tc_recovered_m, Formula.satisfies_conj_iff] at nr
  obtain ⟨rank, model, realized, _, _, height, first, last, set, node, _⟩ := nr
  -- 新高度仍为 ν+1；完整实现、两端角色和单点延长来自同一次图恢复。
  have move {a b n} (φ : Formula 1 n) (hc : φ.FreeClosed) (r : Env M a) (s : Env M b)
      (f : Fin n → Term a) (g : Fin n → Term b) (h : ∀ i, (f i).eval r = (g i).eval s) :=
    Formula.bind_congr_l φ hc r s f g h
  refine ⟨v, ?_⟩
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  refine ⟨?_, ?_, heω, ?_, ?_, root, hκδ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, round.2.2.1, ?_⟩
  · exact (move (Formula.isOmega (.bound 0) : Formula 1 1) (Formula.isOmega_freeClosed _ rfl) ρs ξ
      (fun _ => .bound 0) (fun _ => .bound 0) (fun _ => rfl)).mp omega
  · exact (move (Formula.isEmpty (.bound 0) : Formula 1 1) (Formula.isEmpty_freeClosed _ rfl) ρs ξ
      (fun _ => .bound 1) (fun _ => .bound 1) (fun _ => rfl)).mp empty
  · exact (move (woodin0_m kpair_convention_l) woodin0_closed_l ρs ξ
      (fun _ => .bound 2) (fun _ => .bound 2) (fun _ => rfl)).mp woodin
  · apply (move tg_low0_m tg_low0_closed_l ρs ξ (fun i => [Term.bound 0, Term.bound 1, Term.bound 2, Term.bound 3, Term.bound 4].get i)
      (fun i => [Term.bound 0, Term.bound 1, Term.bound 2, Term.bound 3, Term.bound 4].get i) ?_).mp low
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · exact (move (Formula.isSuccessor (.bound 0) (.bound 1) : Formula 1 2) (by simp -implicitDefEqProofs) ρs ξ
      (fun i => [Term.bound 8, Term.bound 7].get i) (fun i => [Term.bound 7, Term.bound 6].get i)
      (fun i => Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i)).mp succ
  · have shape := (Formula.satisfies_conj_iff ..).mp drop |>.1
    apply (move (Formula.isSuccessor (.bound 0) (.bound 1) : Formula 1 2) (by simp -implicitDefEqProofs) (χ.push v) ξ
      (fun i => [Term.bound 2, Term.bound 5].get i) (fun i => [Term.bound 8, Term.bound 7].get i) ?_).mp shape
    intro i
    exact Fin.cases rfl (Fin.cases hl (fun j => Fin.elim0 j)) i
  · apply (move (Formula.isSuccessor (.bound 0) (.bound 1) : Formula 1 2) (by simp -implicitDefEqProofs) ε ξ
      (fun i => [Term.bound 27, Term.bound 25].get i) (fun i => [Term.bound 9, Term.bound 4].get i) ?_).mp height
    intro i
    exact Fin.cases rfl (Fin.cases (same 8) (fun j => Fin.elim0 j)) i
  · exact (move (v_m kpair_convention_l (.bound 0) (.bound 1) : Formula 1 2) (by simp -implicitDefEqProofs) ε ξ
      (fun i => [Term.bound 27, Term.bound 6].get i) (fun i => [Term.bound 9, Term.bound 10].get i)
      (fun i => Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i)).mp rank
  · apply (move (smem_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) : Formula 1 3)
      (by simp -implicitDefEqProofs) ε ξ (fun i => [Term.bound 5, Term.bound 6, Term.bound 4].get i)
      (fun i => [Term.bound 11, Term.bound 10, Term.bound 12].get i) ?_).mp model
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  · apply (move tt_realized0_m tt_realized0_closed_l ε ξ
      (fun i => [Term.bound 7, Term.bound 5, Term.bound 6, Term.bound 4, Term.bound 12,
        Term.bound 3, Term.bound 23, Term.bound 13, Term.bound 14, Term.bound 28].get i)
      (fun i => [Term.bound 0, Term.bound 11, Term.bound 10, Term.bound 12, Term.bound 8,
        Term.bound 13, Term.bound 2, Term.bound 15, Term.bound 17, Term.bound 18].get i) ?_).mp realized
    intro i
    exact Fin.cases (same 0) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases (same 4)
      (Fin.cases rfl (Fin.cases (same 6) (Fin.cases (same 5) (Fin.cases rfl
        (Fin.cases (same 9) (fun j => Fin.elim0 j)))))))))) i
  · have lang : Formula.satisfies (Env.reindex χ (fun i : Fin 10 => i.succ.succ)) ee_language0_m :=
      (Formula.satisfies_rename ..).mp language
    apply (Formula.satisfies_bind ξ
      (fun i : Fin 10 => [Term.bound 0, Term.bound 5, Term.bound 7, Term.bound 14, Term.bound 15,
        Term.bound 16, Term.bound 27, Term.bound 28, Term.bound 29, Term.bound 30].get i) ee_language0_m).mpr
    apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l ?_).mp lang
    funext i
    exact Fin.cases hw (Fin.cases rfl (Fin.cases hl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  · apply (move (td_dcp_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) : Formula 1 5)
      (by simp -implicitDefEqProofs) (χ.push v) ξ (fun i => [Term.bound 5, Term.bound 2, Term.bound 8, Term.bound 1, Term.bound 0].get i)
      (fun i => [Term.bound 7, Term.bound 8, Term.bound 16, Term.bound 18, Term.bound 19].get i) ?_).mp drop
    intro i
    exact Fin.cases hl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · apply (move (ee_elastic_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) : Formula 1 5)
      (by simp -implicitDefEqProofs) (χ.push v) ξ (fun i => [Term.bound 9, Term.bound 10, Term.bound 11, Term.bound 12, Term.bound 0].get i)
      (fun i => [Term.bound 27, Term.bound 28, Term.bound 29, Term.bound 30, Term.bound 19].get i) ?_).mp elastic
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · apply (move (rd_entry0_m (.bound 0) (.bound 1) (.bound 2) : Formula 1 3) (by simp -implicitDefEqProofs) ε ξ
      (fun i => [Term.bound 8, Term.bound 24, Term.bound 3].get i)
      (fun i => [Term.bound 1, Term.bound 3, Term.bound 13].get i) ?_).mp first
    intro i
    exact Fin.cases (same 1) (Fin.cases (same 7) (Fin.cases rfl (fun j => Fin.elim0 j))) i
  · apply (move (rd_entry0_m (.bound 0) (.bound 1) (.bound 2) : Formula 1 3) (by simp -implicitDefEqProofs) ε ξ
      (fun i => [Term.bound 11, Term.bound 25, Term.bound 3].get i)
      (fun i => [Term.bound 7, Term.bound 4, Term.bound 13].get i) ?_).mp last
    intro i
    exact Fin.cases (same 3) (Fin.cases (same 8) (Fin.cases rfl (fun j => Fin.elim0 j))) i
  · apply (move (sg_set_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3) : Formula 1 4)
      (by simp -implicitDefEqProofs) ε ξ (fun i => [Term.bound 8, Term.bound 11, Term.bound 3, Term.bound 2].get i)
      (fun i => [Term.bound 1, Term.bound 7, Term.bound 13, Term.bound 26].get i) ?_).mp set
    intro i
    exact Fin.cases (same 1) (Fin.cases (same 3) (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
  · apply (move (tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) : Formula 1 5)
      (by simp -implicitDefEqProofs) ε ξ (fun i => [Term.bound 10, Term.bound 24, Term.bound 15, Term.bound 16, Term.bound 2].get i)
      (fun i => [Term.bound 6, Term.bound 3, Term.bound 24, Term.bound 25, Term.bound 26].get i) ?_).mp node
    intro i
    exact Fin.cases (same 2) (Fin.cases (same 7) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · apply (Formula.satisfies_bind ξ (fun i : Fin 12 => [Term.bound 0, Term.bound 7, Term.bound 20,
      Term.bound 21, Term.bound 22, Term.bound 31, Term.bound 32, Term.bound 33, Term.bound 34,
      Term.bound 35, Term.bound 36, Term.bound 37].get i) ts_program0_m).mpr
    apply (Formula.closed_env_l ts_program0_m ts_program0_closed_l ?_).mp program
    funext i
    exact Fin.cases pw (Fin.cases pn (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  · apply (move (tg_bound_raw_m (.bound 0) (.bound 1) (.bound 2) : Formula 1 3)
      (by simp -implicitDefEqProofs) ρs ξ (fun i => [Term.bound 2, Term.bound 3, Term.bound 4].get i)
      (fun i => [Term.bound 2, Term.bound 3, Term.bound 4].get i) ?_).mp bound
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原程序在目标内重新读取后，恢复节点立即触发同一上下文的下一轮回答。 -/
theorem Tg_context_d.restart_l {ω X η C κ K R b z : M.Domain} {σ : Fin 7 → M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R)
    (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (χ : Env (rt_model_l C nc) 12) (ε : Env (rt_model_l C nc) 29)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (recovered : Formula.satisfies ε tc_recovered0_m)
    (same : ∀ i : Fin 10, ε.bound ([7, 8, 10, 11, 12, 13, 23, 24, 25, 28].get i) =
      [ρ.bound 16, ρ.bound 17, ρ.bound 23, ρ.bound 24, χ.bound 1, χ.bound 6,
        ρ.bound 18, ρ.bound 19, ρ.bound 20, χ.bound 0].get i)
    (hw : χ.bound 2 = ρ.bound 16) (hl : χ.bound 4 = ρ.bound 24) (ωρ : (ρ.bound 16).val = ω)
    (below : M.mem (χ.bound 3).val (ρ.bound 15).val)
    (program : Ts_program_in_d ω (ρ.bound 24).val b z σ C) :
    ∃ π : Env (rt_model_l C nc) 12,
      (∀ i : Fin 11, (π.bound ([0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11].get i)).val =
        [ω, (ρ.bound 24).val, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i) ∧
      ∃ v : (rt_model_l C nc).Domain,
        Formula.satisfies (tg_restart_env_d ρ χ ε π v) tg_seed0_m ∧
        ∃ a : Fin 16 → (rt_model_l C nc).Domain,
          Formula.satisfies (tg_round_env_d (tg_restart_env_d ρ χ ε π v) a) tg_round0_m := by
  have fs := (context.read_l hZF source).1
  obtain ⟨c, S, model⟩ := smdl_membership_l I hZF ⟨ω, context.omega⟩
  let p : Fin 11 → M.Domain := fun i => [ω, (ρ.bound 24).val, b, z,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  let ν : Env (rt_model_l C nc) 11 := ⟨fun i => ⟨p i, program.1 i⟩, fun _ => ⟨ω, context.omega⟩⟩
  have numeric := (sc_relative_sat_l I model fs.transitive nc ts_numeric0_m ts_numeric0_closed_l
    ν ((⟨p, fun _ => ω⟩ : Env M 11).push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mp program.2
  simp only [ts_numeric0_m, Formula.satisfies_exists_iff] at numeric
  obtain ⟨a, numeric⟩ := numeric
  let f : Fin 12 → Term 12 := fun i => [Term.bound 1, Term.bound 2, Term.bound 3, Term.bound 0,
    Term.bound 4, Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9,
    Term.bound 10, Term.bound 11].get i
  let π := Definitional.Env.substitute (ν.push a) f
  have prog : Formula.satisfies π ts_program0_m := (Formula.satisfies_bind (ν.push a) f ts_program0_m).mp numeric
  obtain ⟨v, seed⟩ := tg_restart_l ρ χ ε π old candidate recovered prog same hw hl
    (Subtype.ext ωρ.symm) (Subtype.ext rfl) below
  obtain ⟨a', round⟩ := tg_successor_read_l _ seed (context.renew_l hZF source nc _ seed)
  refine ⟨π, ?_, v, seed, a', round⟩
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
