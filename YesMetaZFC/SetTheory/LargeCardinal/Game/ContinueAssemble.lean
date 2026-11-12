import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype

/-! # 当前原结构内装配继续输入

已经搬运到当前层的语言、类型、标签图和两个后继，与同一原策略历史
中的实际事件汇合。事件单值性确定候选和类型，图定义域确定旧元数，
最后原表项与超过公式组成完整二十九项输入。当前结构可以使用原关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_continue_assemble_l {ω C k₀ l₀ : M.Domain}
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ι : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ι tg_issued0_m)
    (hw : (ι.bound 0).val = ω) (ne : ι.bound 23 ≠ ι.bound 1)
    (θ : Env (rt_model_l C nc) 10) (language : Formula.satisfies θ ee_language0_m)
    (same : θ.bound 0 = ι.bound 0) (u t z χ₀ : (rt_model_l C nc).Domain)
    (elastic : Formula.satisfies (θ.push u) (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest))
    (labels : Fn0_d k₀ ω t.val) (first : M.SuccessorOf l₀ k₀) (last : M.SuccessorOf (θ.bound 2).val l₀)
    (event : Tg_round_event_d (rt_pair_l fs.transitive nc hZF.1 fs.pair)
      (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 22) (ι.bound 20) t z)
    (pair : KPair_d M z.val (θ.bound 1).val u.val) (hχ : M.mem χ₀.val (ι.bound 5).val) :
    ∃ ε : Env (rt_model_l C nc) 29, Formula.satisfies ε tc_seed0_m ∧
      (∀ j : Fin 10, ε.bound ([0,1,3,4,5,6,17,18,19,20].get j) = θ.bound j) ∧
      ε.bound 7 = u ∧ ε.bound 3 = ι.bound 27 ∧
      (∀ j : Fin 14, ε.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get j) =
        ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get j)) ∧
      M.MemberSubset t.val (ι.bound 23).val ∧ ε.bound 28 = χ₀ := by
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  obtain ⟨h, _, _, B', U, Q, _, _, _, _, _, endt, _, _, _, _, _, _, _, fork, _, _, _, _, _, _, newLanguage⟩ :=
    tg_issued_query_l J ext ι issued
  let χ : Env (rt_model_l C nc) 15 := ⟨fun i => [ι.bound 0, ι.bound 1, ι.bound 2, ι.bound 4, ι.bound 5,
    ι.bound 19, h, ι.bound 22, ι.bound 23, ι.bound 24, ι.bound 26, ι.bound 28, U, Q, ι.bound 25].get i, ι.free⟩
  have cont : Formula.satisfies χ tg_continue0_m := fork ne
  simp only [tg_continue0_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, tg_event_sat_l J ext, tg_aux_data_sat_l ext, kpair0_sat_l ext,
    fn0_sat_l ext, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff J] at cont
  obtain ⟨_, v, z₀, l, t₀, κ, u₀, τ, w, a, b, m, B₀, V, P,
    aux, move, answer, cp, tags, sk, restriction, sl, sm, limit, base, constants, pool, exceeds⟩ := cont
  obtain ⟨⟨v', l', κ', u', oldAux, oldMove⟩, oldAnswer⟩ := event
  have ev := tg_control_event_unique_l J ext _ state.control state.history (aux.end_l endt) oldAux
  have et : t₀ = t := (move.unique_l (ev.symm ▸ oldMove)).2.1
  have etv := congrArg Subtype.val et
  have sub : M.MemberSubset t.val (ι.bound 23).val := by
    have rest := (rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair t₀ (ι.bound 23) a).mp restriction
    intro p hp
    obtain ⟨i, x, code⟩ := rest.1 p (etv.symm ▸ hp)
    obtain ⟨q, cq, hq⟩ := ((rest.2 i x).mp ⟨p, code, etv.symm ▸ hp⟩).2
    exact kpair_unique_l M hZF.1 cq code ▸ hq
  have ez := tg_control_event_unique_l J ext _ state.control state.history (answer.end_l endt) oldAnswer
  have cpM := (kpair0_sat_l hZF.1 ..).mp ((rt_model_delta_l fs.transitive nc
    (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
    (⟨fun i => [z₀, τ, w].get i, fun _ => z₀⟩ : Env (rt_model_l C nc) 3)).mp ((kpair0_sat_l ext ..).mpr cp))
  have eq := kpair_injective_l M cpM ((congrArg Subtype.val ez).symm ▸ pair)
  have θτ : θ.bound 1 = τ := Subtype.ext eq.1.symm
  have wu : w = u := Subtype.ext eq.2
  have tagsM : Fn0_d a.val ω t₀.val := hw ▸ (fn0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun i => [a, ι.bound 0, t₀].get i, fun _ => a⟩ : Env (rt_model_l C nc) 3)).mp ((fn0_sat_l ext ..).mpr tags))
  have ea : a.val = k₀ := (fn0_function_l (ZF.modelsKP hZF) tagsM).2.1.eq hZF.1
    (etv.symm ▸ (fn0_function_l (ZF.modelsKP hZF) labels).2.1)
  have eb : b.val = l₀ := ((rt_successor_l fs.transitive nc hZF.1 b a).mp sl).eq hZF.1 (ea.symm ▸ first)
  have em : m.val = (θ.bound 2).val := ((rt_successor_l fs.transitive nc hZF.1 m b).mp sm).eq hZF.1 (eb.symm ▸ last)
  have bm : b = ι.bound 26 := sl.eq ext sk
  have mi : m = ι.bound 27 := (bm ▸ sm).eq ext state.first
  have θm : θ.bound 2 = m := Subtype.ext em.symm
  let ν := χ.push v |>.push z₀ |>.push l |>.push t₀ |>.push κ |>.push u₀ |>.push τ |>.push w
    |>.push a |>.push b |>.push m |>.push B₀ |>.push V |>.push P
  have language' := language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language'
  have vr := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ν (.bound 7) (.bound 2)).mp base
  have vr' := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc θ (.bound 1) (.bound 3)).mp language'.2.2.1
  have θB : θ.bound 3 = B₀ := Subtype.ext (Vr_d.unique_l hZF fs.transitive (θ.bound 3).property B₀.property
    (congrArg Subtype.val θτ ▸ vr') vr)
  have cons := (tt_constants0_sat_l ext ..).mp constants
  have cons' := (tt_constants0_sat_l ext ..).mp language'.2.2.2.1
  have θV : θ.bound 4 = V := ext.eq_of_same_members _ _ (fun x =>
    (cons' x).trans ((or_congr (Iff.of_eq (congrArg ((rt_model_l C nc).mem x) θB))
      (Iff.of_eq (congrArg (fun y => x = y) θτ))).trans (cons x).symm))
  have oldPool := (fs.pool_sat_l (ZF.modelsKP hZF) nc ν (.bound 14) (.bound 3) (.bound 1) (.bound 0) hw).mp pool
  have pool' := ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp language'.1).2).1
  have hwθ : (θ.bound 0).val = ω := (congrArg Subtype.val same).trans hw
  have pool' := (fs.pool_sat_l (ZF.modelsKP hZF) nc θ (.bound 0) (.bound 2) (.bound 4) (.bound 5) hwθ).mp pool'
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
  obtain ⟨b₁, program⟩ := programs (ι.bound 27) (ι.bound 36) (ι.bound 37) (ι.bound 38) (ι.bound 39)
    (ι.bound 40) (ι.bound 41) (ι.bound 42) (ι.bound 43) (ι.bound 44) state.program
  let ε : Env (rt_model_l C nc) 29 := ⟨fun i => [ι.bound 0, τ, ι.bound 5, m, B₀, V, P, w,
    ι.bound 24, ι.bound 28, B', U, Q, ι.bound 25, ι.bound 36, b₁, ι.bound 37,
    θ.bound 6, θ.bound 7, θ.bound 8, θ.bound 9, ι.bound 38, ι.bound 39, ι.bound 40,
    ι.bound 41, ι.bound 42, ι.bound 43, ι.bound 44, χ₀].get i, ι.free⟩
  refine ⟨ε, ?_, ?_, wu, mi, ?_, sub, rfl⟩
  · simp only [tc_seed0_m, Formula.satisfies_conj_iff]
    have rules := control.2.2.1
    simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
    simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at newLanguage
    refine ⟨rules.1, ?_, ?_, newLanguage.2.2.2.1, state.bound, newLanguage.2.2.2.2.1,
      newLanguage.2.2.2.2.2.1, ?_, ?_, hχ⟩
    · simp only [ts_program_m, Formula.satisfies_bind]
      apply (Formula.closed_env_l ts_program0_m ts_program0_closed_l (ρ := _) (η := _) ?_).mp program
      funext i
      exact Fin.cases rfl (Fin.cases mi.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
    · simp only [ee_language_m, Formula.satisfies_bind]
      apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l (ρ := θ) (η := _) ?_).mp language
      funext i
      exact Fin.cases same (Fin.cases θτ (Fin.cases θm (Fin.cases θB (Fin.cases θV
        (Fin.cases θP (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
    · simp only [ee_elastic_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at elastic ⊢
      change (M.mem (θ.bound 6).val w.val ∧ M.mem (θ.bound 7).val w.val) ∧
        M.mem (θ.bound 8).val w.val ∧ M.mem (θ.bound 9).val w.val
      rw [wu]
      exact elastic
    · simp only [tx_exceeds_m, Formula.satisfies_bind] at exceeds ⊢
      apply (Formula.closed_env_l tx_exceeds0_m tx_exceeds0_closed_l (ρ := _) (η := _) ?_).mp exceeds
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  · intro i
    exact Fin.cases same.symm (Fin.cases θτ.symm (Fin.cases θm.symm (Fin.cases θB.symm
      (Fin.cases θV.symm (Fin.cases θP.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
