import YesMetaZFC.SetTheory.LargeCardinal.TypeGameHistorySelect
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLanguageTransfer

/-! # 从同一旧轮和原继续规则装配伸展输入

标签图的定义域确定旧长度；两次后继确定旧回答元数，并与当前原程序元数相等。
共同秩段搬运完整弹性语言，秩层、常量域和查询域的唯一性识别原超过关系的
低端。最终输入的每一项都来自实际记录、原策略表或原继续规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X R μ K η C Y S μ' K' η' D : M.Domain}
  (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
  (nd : Nonempty {x // M.mem x D}) (ι : Env (rt_model_l D nd) 46)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.continue_seed_l {B T r c d π σ C₀ L W : M.Domain}
    (context : Tg_context_d ω X η C) (current : Tg_context_d ω Y η' D)
    (owner : Ep_source_d hZF ω μ K X R) (source : Ep_source_d hZF ω μ' K' Y S)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ) (hwB : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hτW : M.mem (p 15) W) (hWD : M.mem W D)
    (hw : p 16 = ω) (round : Formula.satisfies ρ tg_round0_m)
    (hw' : (ι.bound 0).val = ω) (issued : Formula.satisfies ι tg_issued0_m) (ne : ι.bound 23 ≠ ι.bound 1)
    (trace : Tg_trace_d ω D (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val
      (ι.bound 22).val (ι.bound 20).val (p 41) (p 15) (p 11)) :
    ∃ ε : Env (rt_model_l D nd) 28, Formula.satisfies ε tc_seed0_m ∧
      (∀ i : Fin 10, (ε.bound ([0, 1, 3, 4, 5, 6, 17, 18, 19, 20].get i)).val =
        p ([16, 15, 24, 14, 13, 12, 6, 5, 4, 3].get i)) ∧
      (ε.bound 7).val = p 11 ∧ ε.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ε.bound ([0, 2, 8, 9, 13, 14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
        ι.bound ([0, 5, 24, 28, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)) := by
  have fs := (context.read_l hZF owner).1
  have ft := (current.read_l hZF source).1
  let J := rt_pair_l ft.transitive nd hZF.1 ft.pair
  have ext := rt_model_ext_l hZF.1 ft.transitive nd
  have state := (tg_issued_sat_l J ext ι).mp issued
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, _, _, _, _, first₀, last₀, _, _, _, _, _, _, _, _, _, _, node, _⟩ := seed
  have first₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp first₀)
  have last₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp last₀)
  simp only [tg_node_m, Formula.satisfies_conj_iff, tg_graph_m] at node
  have domain : M.IsDomainOf I (p 22) (p 41) := (rt_domain_formula_l fs.transitive nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    _ (.bound 6) (.bound 25)).mp node.2.1.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, language, _, elastic, _⟩ := data
  let f : Fin 10 → Term 54 := fun i => [.bound 16, .bound 15, .bound 24, .bound 14, .bound 13,
    .bound 12, .bound 6, .bound 5, .bound 4, .bound 3].get i
  have language : Formula.satisfies (Definitional.Env.substitute ρ f) ee_language0_m :=
    (Formula.satisfies_bind ρ f ee_language0_m).mp language
  obtain ⟨_, _, nd', θ, same, language⟩ := context.language_peer_l hZF nc _ current owner source bt mb mx my
    j k hwB iC iD hW rank hW' rank' hL hwW hτW hWD hw language
  have θω : θ.bound 0 = ι.bound 0 := Subtype.ext ((same 0).trans (hw.trans hw'.symm))
  obtain ⟨h, _, _, B', U, Q, _, _, _, _, _, endt, _, _, _, _, _, _, _, fork, _, _, _, _, _, _, newLanguage⟩ :=
    tg_issued_query_l J ext ι issued
  let χ : Env (rt_model_l D nd) 15 := ⟨fun i => [ι.bound 0, ι.bound 1, ι.bound 2, ι.bound 4, ι.bound 5,
    ι.bound 19, h, ι.bound 22, ι.bound 23, ι.bound 24, ι.bound 26, ι.bound 28, U, Q, ι.bound 25].get i, ι.free⟩
  have cont : Formula.satisfies χ tg_continue0_m := fork ne
  simp only [tg_continue0_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, tg_event_sat_l J ext, tg_aux_data_sat_l ext, kpair0_sat_l ext,
    fn0_sat_l ext, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff J] at cont
  obtain ⟨_, v, z, l₀, t₀, κ₀, u₀, τ, w, a, l, m, B₀, V, P,
    aux, move, answer, pair, labels, sk, _, sl, sm, limit, base, constants, pool, exceeds⟩ := cont
  obtain ⟨_, _, _, n', t', z', en, ht, oldPair, traced⟩ :=
    trace.read_l hZF ft.transitive nd (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 20)
  have en : n' = ι.bound 22 := Subtype.ext en
  subst n'
  obtain ⟨⟨v', l', κ', u', oldAux, oldMove⟩, oldAnswer⟩ := (tg_round_event_sat_l J ext ..).mp traced
  have ev := tg_control_event_unique_l J ext _ state.control state.history (aux.end_l endt) oldAux
  have tEq : t₀.val = p 41 := (congrArg Subtype.val (move.unique_l (ev.symm ▸ oldMove)).2.1).trans ht
  have ez := tg_control_event_unique_l J ext _ state.control state.history (answer.end_l endt) oldAnswer
  have pairM := (kpair0_sat_l hZF.1 ..).mp ((rt_model_delta_l ft.transitive nd (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
    (⟨fun i => [z, τ, w].get i, fun _ => z⟩ : Env (rt_model_l D nd) 3)).mp ((kpair0_sat_l ext ..).mpr pair))
  have eq := kpair_injective_l M pairM ((congrArg Subtype.val ez).symm ▸ oldPair)
  have τEq : τ.val = p 15 := eq.1
  have wEq : w.val = p 11 := eq.2
  have θτ : θ.bound 1 = τ := Subtype.ext ((same 1).trans τEq.symm)
  have fn : Fn0_d a.val (ι.bound 0).val t₀.val := (fn0_sat_l hZF.1 ..).mp ((rt_model_delta_l ft.transitive nd (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
    (⟨fun i => [a, ι.bound 0, t₀].get i, fun _ => a⟩ : Env (rt_model_l D nd) 3)).mp ((fn0_sat_l ext ..).mpr labels))
  have aEq : a.val = p 22 := (fn0_function_l (ZF.modelsKP hZF) fn).2.1.eq hZF.1 (tEq.symm ▸ domain)
  have lEq : l.val = p 23 := ((rt_successor_l ft.transitive nd hZF.1 l a).mp sl).eq hZF.1 (aEq.symm ▸ first₀)
  have mEq : m.val = p 24 := ((rt_successor_l ft.transitive nd hZF.1 m l).mp sm).eq hZF.1 (lEq.symm ▸ last₀)
  have lk : l = ι.bound 26 := sl.eq ext sk
  have mEq' : m = ι.bound 27 := (lk ▸ sm).eq ext state.first
  have θm : θ.bound 2 = m := Subtype.ext ((same 2).trans mEq.symm)
  let ν := χ.push v |>.push z |>.push l₀ |>.push t₀ |>.push κ₀ |>.push u₀ |>.push τ |>.push w
    |>.push a |>.push l |>.push m |>.push B₀ |>.push V |>.push P
  have language' := language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language'
  have vr := (vr_sat_l (ZF.modelsKP hZF) ft.transitive nd ν (.bound 7) (.bound 2)).mp base
  have vr' := (vr_sat_l (ZF.modelsKP hZF) ft.transitive nd θ (.bound 1) (.bound 3)).mp language'.2.2.1
  have θB : θ.bound 3 = B₀ := Subtype.ext (Vr_d.unique_l hZF ft.transitive (θ.bound 3).property B₀.property
    (congrArg Subtype.val θτ ▸ vr') vr)
  have cons := (tt_constants0_sat_l ext ..).mp constants
  have cons' := (tt_constants0_sat_l ext ..).mp language'.2.2.2.1
  have θV : θ.bound 4 = V := ext.eq_of_same_members _ _ (fun x =>
    (cons' x).trans ((or_congr (Iff.of_eq (congrArg ((rt_model_l D nd).mem x) θB))
      (Iff.of_eq (congrArg (fun y => x = y) θτ))).trans (cons x).symm))
  have oldPool := (ft.pool_sat_l (ZF.modelsKP hZF) nd ν (.bound 14) (.bound 3) (.bound 1) (.bound 0) hw').mp pool
  have pool' := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp language'.1).2).1
  have pool' := (ft.pool_sat_l (ZF.modelsKP hZF) nd θ (.bound 0) (.bound 2) (.bound 4) (.bound 5)
    ((same 0).trans hw)).mp pool'
  obtain ⟨A₀, E₀, _, _, names₀, seq₀, prod₀⟩ := oldPool
  obtain ⟨A₁, E₁, _, _, names₁, seq₁, prod₁⟩ := pool'
  have θP : θ.bound 5 = P := Subtype.ext ((show Tt_pool_d I ω (θ.bound 2).val (θ.bound 4).val (θ.bound 5).val from
    ⟨A₁, E₁, names₁, seq₁, prod₁⟩).unique_l hZF.1 I
      ((congrArg Subtype.val θm).symm ▸ (congrArg Subtype.val θV).symm ▸ ⟨A₀, E₀, names₀, seq₀, prod₀⟩))
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff] at tables
  have programs := tables.1.2.1
  simp only [Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, tg_program_data_sat_l ext,
    Formula.satisfies_exists_iff, ts_program_m, Formula.satisfies_bind] at programs
  obtain ⟨b, program⟩ := programs (ι.bound 27) (ι.bound 36) (ι.bound 37) (ι.bound 38) (ι.bound 39)
    (ι.bound 40) (ι.bound 41) (ι.bound 42) (ι.bound 43) (ι.bound 44) state.program
  let ε : Env (rt_model_l D nd) 28 := ⟨fun i => [ι.bound 0, τ, ι.bound 5, m, B₀, V, P, w,
    ι.bound 24, ι.bound 28, B', U, Q, ι.bound 25, ι.bound 36, b, ι.bound 37,
    θ.bound 6, θ.bound 7, θ.bound 8, θ.bound 9, ι.bound 38, ι.bound 39, ι.bound 40,
    ι.bound 41, ι.bound 42, ι.bound 43, ι.bound 44].get i, ι.free⟩
  refine ⟨ε, ?_, ?_, wEq, mEq', ?_⟩
  · simp only [tc_seed0_m, Formula.satisfies_conj_iff]
    have rules := control.2.2.1
    simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
    simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at newLanguage
    refine ⟨rules.1, ?_, ?_, newLanguage.2.2.2.1, state.bound, newLanguage.2.2.2.2.1,
      newLanguage.2.2.2.2.2.1, ?_, ?_⟩
    · simp only [ts_program_m, Formula.satisfies_bind]
      apply (Formula.closed_env_l ts_program0_m ts_program0_closed_l (ρ := _) (η := _) ?_).mp program
      funext i
      exact Fin.cases rfl (Fin.cases mEq'.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
    · simp only [ee_language_m, Formula.satisfies_bind]
      apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l (ρ := θ) (η := _) ?_).mp language
      funext i
      exact Fin.cases θω (Fin.cases θτ (Fin.cases θm (Fin.cases θB (Fin.cases θV
        (Fin.cases θP (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
    · simp only [ee_elastic_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at elastic ⊢
      change (M.mem (θ.bound 6).val w.val ∧ M.mem (θ.bound 7).val w.val) ∧
        M.mem (θ.bound 8).val w.val ∧ M.mem (θ.bound 9).val w.val
      rw [wEq, same 6, same 7, same 8, same 9]
      exact elastic
    · simp only [tx_exceeds_m, Formula.satisfies_bind] at exceeds ⊢
      apply (Formula.closed_env_l tx_exceeds0_m tx_exceeds0_closed_l (ρ := _) (η := _) ?_).mp exceeds
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  · intro i
    exact Fin.cases (hw'.trans hw.symm) (Fin.cases τEq (Fin.cases mEq
      (Fin.cases ((congrArg Subtype.val θB).symm.trans (same 3))
      (Fin.cases ((congrArg Subtype.val θV).symm.trans (same 4))
      (Fin.cases ((congrArg Subtype.val θP).symm.trans (same 5))
      (Fin.cases (same 6) (Fin.cases (same 7) (Fin.cases (same 8) (Fin.cases (same 9)
        (fun j => Fin.elim0 j)))))))))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
