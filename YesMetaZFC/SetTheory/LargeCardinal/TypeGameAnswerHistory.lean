import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerTable
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedAnswer
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyReflect
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePositionNext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTrace

/-! # 跨模型回答实际推进原策略历史

完整回答保留在产生它的模型中，历史保留在施加扩展器后的模型中。
共同秩段和共同根图核对后继模型的原查询表，随后在该模型内构造回答的
有序对并追加历史。原控制记录随后处理实数落子、增加轮号并给出下一辅助
记录；工作模型的 ZF 模型性和新回答的合法性均由已有证书取代。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X R μ K η C : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "slots" => (Fin.cases (p 47) (Fin.cases (p 48) (Fin.cases (p 49)
  (Fin.cases (p 50) (Fin.cases (p 51) (Fin.cases (p 52) (fun _ => p 53)))))))

theorem Tg_context_d.answer_history_l {Y S μ' K' η' D B T r c d π σ C₀ γ Z L W : M.Domain}
    (context : Tg_context_d ω X η C) (current : Tg_context_d ω Y η' D)
    (owner : Ep_source_d hZF ω μ K X R) (source : Ep_source_d hZF ω μ' K' Y S)
    (hierarchy : Sc_hierarchy_d Y)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d γ Z X π) (target : Tg_anchor_d γ Z Y σ)
    (hγ : M.IsLimitOrdinal γ) (hwZ : M.mem ω Z)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hτW : M.mem (p 15) W)
    (nd : Nonempty {x // M.mem x D}) (θ : Env (rt_model_l D nd) 46)
    (issued : Formula.satisfies θ tg_issued0_m) (hw : p 16 = ω)
    (same : ∀ i : Fin 14, (θ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val =
      p ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53].get i))
    (below : M.mem (p 15) (θ.bound 5).val) (round : Formula.satisfies ρ tg_round0_m)
    (reply : Tg_reply_d I ω (p 23) (p 24) (θ.bound 24).val (p 15) (θ.bound 30).val (θ.bound 31).val
      (p 12) (θ.bound 25).val (p 11) (p 36) slots (p 38) ⟨p 2, p 1, p 0⟩) :
    ∃ v t q : (rt_model_l D nd).Domain, KPair_d M v.val (p 15) (p 11) ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ (θ.bound 19) t q) (tg_position0_m 2) ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, t, θ.bound 20, v].get i, fun _ => v⟩ :
        Env (rt_model_l D nd) 4) (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      Tg_trace_d ω D (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 19).val t.val (θ.bound 23).val (p 15) (p 11) ∧
      let ψ := tg_position_env_d
        (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 19) (θ.bound 19) t q
      ∀ x, (rt_model_l D nd).mem x (ψ.bound 6) → ∃ v' t' j' n',
        (rt_model_l D nd).mem v' (ψ.bound 6) ∧
        (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
        (¬ Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
          Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
        Formula.satisfies (⟨fun i => [ψ.bound 0, t', ψ.bound 20, v'].get i, fun _ => v'⟩ : Env (rt_model_l D nd) 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
        (rt_model_l D nd).SuccessorOf n' (ψ.bound 19) ∧
        Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3), fun _ => ψ.bound 0⟩ n' t' j')
          (tg_position0_m 0) ∧
        ∃ ε : Env (rt_model_l D nd) 46, (∀ i : Fin 19, ε.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
          ε.bound 19 = n' ∧ Formula.satisfies ε tg_issued0_m ∧ Rd_entry_d t' (ε.bound 21) (ψ.bound 17) ∧
          Formula.satisfies (⟨fun i => [ψ.bound 0, ε.bound 20, t', ε.bound 21].get i, fun _ => ε.bound 21⟩ :
            Env (rt_model_l D nd) 4)
            (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
          (rt_model_l D nd).mem (θ.bound 24) (ε.bound 24) ∧
          M.MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
          Tg_trace_d ω D (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 19).val
            (ε.bound 20).val (θ.bound 23).val (p 15) (p 11) := by
  have fs := (current.read_l hZF source).1
  let J := rt_pair_l fs.transitive nd hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nd
  have state := (tg_issued_sat_l J ext θ).mp issued
  let χ : Env (rt_model_l D nd) 19 := ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩
  have ωθ : (θ.bound 0).val = ω := (same 0).trans hw
  have copy := reply
  obtain ⟨_, u, _, sub, _⟩ := copy
  obtain ⟨hτκ, _, z, query, _⟩ := sub
  let τ : (rt_model_l D nd).Domain := ⟨p 15, fs.transitive _ (θ.bound 24).property _ hτκ⟩
  let w : (rt_model_l D nd).Domain := ⟨p 11, fs.transitive _ (θ.bound 30).property _ query.constants.1⟩
  obtain ⟨B', U', D', r', m', b', f', q', _, _, row, _, _, _, _, _, valid⟩ :=
    context.answer_table_l hZF nc ρ current owner source hierarchy bt mb mx my j k iC iD anchor target
      hγ hwZ hW rank hW' rank' hL hτW nd χ state.control hw ωθ (same 1) τ (θ.bound 26)
      rfl (same 2) below round reply
  let ε : Env (rt_model_l D nd) 22 := ⟨fun i => [θ.bound 0, θ.bound 27, θ.bound 28, θ.bound 24, τ,
    θ.bound 30, θ.bound 31, D', θ.bound 25, w, θ.bound 36, θ.bound 37, r', b', f',
    θ.bound 38, θ.bound 39, θ.bound 40, θ.bound 41, θ.bound 42, θ.bound 43, θ.bound 44].get i,
    fun _ => θ.bound 0⟩
  let s : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have slotEq : (fun i => ((s i).eval ε).val) = slots := by
    funext i
    exact Fin.cases (same 7) (Fin.cases (same 8) (Fin.cases (same 9) (Fin.cases (same 10)
      (Fin.cases (same 11) (Fin.cases (same 12) (Fin.cases (same 13) (fun a => Fin.elim0 a))))))) i
  have legal : Formula.satisfies ε tg_reply0_m := by
    apply current.reply_l hZF source nd ε (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12)
      (.bound 13) (.bound 14) s
    rw [slotEq]
    change Tg_reply_d I (θ.bound 0).val (θ.bound 27).val (θ.bound 28).val (θ.bound 24).val (p 15)
      (θ.bound 30).val (θ.bound 31).val D'.val (θ.bound 25).val (p 11) (θ.bound 36).val slots
      (θ.bound 37).val ⟨r'.val, b'.val, f'.val⟩
    rw [ωθ, (show (θ.bound 27).val = p 23 from same 3),
      (show (θ.bound 28).val = p 24 from same 4), (show (θ.bound 36).val = p 36 from same 5),
      (show (θ.bound 37).val = p 38 from same 6)]
    exact valid
  -- 同一请求在后继层有实际秩层见证；由原表项得到完整回答并追加策略历史。
  have seed := (Formula.satisfies_conj_iff ..).mp round |>.1
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_rename, Formula.satisfies_conj_iff] at seed
  have empty := (Formula.satisfies_isEmpty_iff ..).mp seed.2.1
  have zero (x : M.Domain) (hx : M.mem x (θ.bound 1).val) : False := by
    have hx' : M.mem x (p 17) := same 1 ▸ hx
    exact empty ⟨x, (context.read_l hZF owner).1.transitive _ (ρ.bound 17).property x hx'⟩ hx'
  have data := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _⟩ := data
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  have limit := (rt_limit_l (context.read_l hZF owner).1.transitive nc (ZF.modelsKP hZF) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.2.2.1)
  have hn : M.mem (p 24) ω := hw ▸ language.1
  have hlast := (rt_successor_l fs.transitive nd hZF.1 (θ.bound 28) (θ.bound 27)).mp state.last
  have hfirst := (rt_successor_l fs.transitive nd hZF.1 (θ.bound 27) (θ.bound 26)).mp state.first
  have finite : M.mem (θ.bound 26).val ω := source.omega.transitive hZF _
    (source.omega.transitive hZF _ ((same 4).symm ▸ hn) _ hlast.predecessor_mem) _ hfirst.predecessor_mem
  have request := current.query_request_l hZF source hierarchy nd τ (θ.bound 26) (θ.bound 1) limit finite zero
  have request : Formula.satisfies (⟨fun i => [θ.bound 0, τ, θ.bound 26, θ.bound 1, θ.bound 1].get i,
      fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 5) tg_query_request0_m := by
    apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
    funext i
    exact Fin.cases (Subtype.ext ωθ.symm) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun a => Fin.elim0 a))))) i
  obtain ⟨v, t, q, pair, _, endt, hq, _, fn, position, clock, event⟩ :=
    tg_issued_answer_l J ext θ issued (τ := τ) (w := w) below request row legal
  have pair' := (rt_model_delta_l fs.transitive nd (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
    (⟨fun i => [v, τ, w].get i, fun _ => v⟩ : Env (rt_model_l D nd) 3)).mp
    ((kpair0_sat_l ext ..).mpr pair)
  have next := tg_position_build_l J ext 2 χ (θ.bound 19) t q state.control state.round hq fn position clock
  have trace : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) t (θ.bound 23) v :=
    ⟨⟨θ.bound 21, θ.bound 22, θ.bound 24, θ.bound 25, state.event.end_l endt, state.move⟩, event⟩
  have labels : Fn0_d (θ.bound 26).val ω (θ.bound 23).val := ωθ ▸
    (fn0_sat_l hZF.1 ..).mp ((rt_model_delta_l fs.transitive nd (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun i => [θ.bound 26, θ.bound 0, θ.bound 23].get i, fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 3)).mp
        ((fn0_sat_l ext ..).mpr state.labels))
  have traced := tg_trace_build_l hZF fs.transitive nd (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19)
    t (θ.bound 23) v finite labels ((kpair0_sat_l hZF.1 ..).mp pair') ((tg_round_event_sat_l J ext ..).mpr trace)
  refine ⟨v, t, q, (kpair0_sat_l hZF.1 ..).mp pair', next,
    (fseq_end_sat_l J ext ..).mpr endt, traced, ?_⟩
  dsimp only
  intro x hx
  obtain ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux⟩ :=
    tg_position_next_l J ext _ next x hx
  have digit' := (fseq_end_sat_l J ext ..).mp digit
  have aux' := (fseq_end_sat_l J ext ..).mp aux
  have keep : (rt_model_l D nd).MemberSubset t (ε.bound 20) :=
    fun s hs => aux'.subset_l J s (digit'.subset_l J s hs)
  have keep' : (rt_model_l D nd).MemberSubset (θ.bound 20) (ε.bound 20) :=
    fun s hs => keep s (endt.subset_l J s hs)
  have same' : ∀ i : Fin 19, ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27) := by
    intro i
    exact (head i).trans (by simp only [tg_position_env_d, Fin.addCases_left, χ])
  have succ' : (rt_model_l D nd).SuccessorOf (ε.bound 19) (θ.bound 19) := num.symm ▸ succ
  have keepM : M.MemberSubset t.val (ε.bound 20).val :=
    fun s hs => keep ⟨s, fs.transitive t.val t.property s hs⟩ hs
  have keepM' : M.MemberSubset (θ.bound 20).val (ε.bound 20).val :=
    fun s hs => keep' ⟨s, fs.transitive _ (θ.bound 20).property s hs⟩ hs
  exact ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    tg_issued_growth_l J ext θ ε issued issued' same' succ' keep', keepM',
    traced.mono_l hZF fs.transitive nd J (θ.bound 4) (θ.bound 1) (θ.bound 2) t (ε.bound 20) keepM⟩

end YesMetaZFC.SetTheory.LargeCardinal
