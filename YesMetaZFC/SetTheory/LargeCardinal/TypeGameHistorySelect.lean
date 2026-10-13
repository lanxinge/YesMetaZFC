import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastEvents

/-! # 规则 (6) 实际选中同一旧轮

非空请求自身给出较早轮号。按该轮号读取完整存档，再由原时钟的事件单值性
识别规则 (6) 中的旧标签、旧域和旧类型；原超过公式保留在当前反射层内。
这里不假定新类型有额外实现，也不对当前层附加 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原合法请求自动选择旧完整源，历史中的旧回答与该源的存档逐字相同。 -/
theorem Tg_past_events_d.continue_l {ω H X b Q C : M.Domain}
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m) (ne : ρ.bound 23 ≠ ρ.bound 1)
    (past : Tg_past_d hZF ω (ρ.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (events : Tg_past_events_d ω H C (ρ.bound 4).val (ρ.bound 1).val (ρ.bound 2).val (ρ.bound 20).val) :
    ∃ h U D : (rt_model_l C nc).Domain,
      Fseq_end_d J (ρ.bound 0) (ρ.bound 20) h (ρ.bound 21) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2, ρ.bound 4, ρ.bound 5,
        ρ.bound 19, h, ρ.bound 22, ρ.bound 23, ρ.bound 24, ρ.bound 26, ρ.bound 28, U, D, ρ.bound 25].get i,
        ρ.free⟩ : Env (rt_model_l C nc) 15) tg_continue0_m ∧
      ∃ i Y R μ K η C₀ L V q d,
        Tg_past_at_d H (ρ.bound 22).val i Y R μ K η C₀ L V q ∧ Rd_entry_d i d Q ∧ Smem_d I d Y R ∧
        Tg_saved_d hZF ω Y R μ K η C₀ L V q ∧ M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b ∧
        ∃ nc₀ : Nonempty {x // M.mem x C₀}, ∃ σ : Env (rt_model_l C₀ nc₀) 54,
          Tg_saved_code_d ω V q (fun j => (σ.bound j).val) ∧ Formula.satisfies σ tg_round0_m ∧
          (σ.bound 16).val = ω ∧
          ∀ v l t κ u z τ w : (rt_model_l C nc).Domain,
            Tg_event_d J (ρ.bound 4) (ρ.bound 22) (ρ.bound 1) h v → Tg_aux_data_d v l t κ u →
            Tg_event_d J (ρ.bound 4) (ρ.bound 22) (ρ.bound 2) h z → KPair_d (rt_model_l C nc) z τ w →
            t.val = (σ.bound 41).val ∧ τ.val = (σ.bound 15).val ∧ w.val = (σ.bound 11).val := by
  have ext := rt_model_ext_l hZF.1 trans nc
  have state := (tg_issued_sat_l J ext ρ).mp valid
  obtain ⟨h, _, _, _, U, D, _, _, _, _, _, endt, _, _, _, _, _, _, _, fork, _⟩ := tg_issued_query_l J ext ρ valid
  have cont := fork ne
  have index : M.mem (ρ.bound 22).val (ρ.bound 19).val := ((Formula.satisfies_conj_iff ..).mp cont).1
  obtain ⟨i, Y, R, μ, K, η, C₀, L, V, q, d, row, node, model, saved, member, rank, bound⟩ := past.select_l hZF links index
  let nc₀ : Nonempty {x // M.mem x C₀} := ⟨⟨ω, saved.context.omega⟩⟩
  obtain ⟨σ, code, round, sameω, _⟩ := saved.read_l hZF nc₀
  obtain ⟨s, code', trace⟩ := events _ _ _ _ _ _ _ _ _ _ _ row
  have eq := rt_tuple_inj_l code' code
  have et : s 41 = (σ.bound 41).val := congrFun eq 43
  have eτ : s 15 = (σ.bound 15).val := congrFun eq 17
  have ew : s 11 = (σ.bound 11).val := congrFun eq 13
  obtain ⟨_, _, _, n', t', z', en, ht, pair, traced⟩ :=
    trace.read_l hZF trans nc (ρ.bound 4) (ρ.bound 1) (ρ.bound 2) (ρ.bound 20)
  have en : n' = ρ.bound 22 := Subtype.ext en
  subst n'
  have traced := (tg_round_event_sat_l J ext ..).mp traced
  obtain ⟨⟨v', l', κ', u', aux, data⟩, answer⟩ := traced
  refine ⟨h, U, D, endt, cont, i, Y, R, μ, K, η, C₀, L, V, q, d, row, node, model,
    saved, member, rank, bound, nc₀, σ, code, round, sameω, ?_⟩
  intro v l t κ u z τ w oldAux oldData oldAnswer oldPair
  have ev := tg_control_event_unique_l J ext _ state.control state.history (oldAux.end_l endt) aux
  have label : t = t' := (oldData.unique_l (ev.symm ▸ data)).2.1
  have ez := tg_control_event_unique_l J ext _ state.control state.history (oldAnswer.end_l endt) answer
  have oldPair := (kpair0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l trans nc (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun j => [z, τ, w].get j, fun _ => z⟩ : Env (rt_model_l C nc) 3)).mp ((kpair0_sat_l ext ..).mpr oldPair))
  have domains := kpair_injective_l M oldPair ((congrArg Subtype.val ez).symm ▸ pair)
  exact ⟨(congrArg Subtype.val label).trans (ht.trans et), domains.1.trans eτ, domains.2.trans ew⟩

end YesMetaZFC.SetTheory.LargeCardinal
