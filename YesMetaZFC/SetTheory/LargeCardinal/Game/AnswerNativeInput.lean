import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerAdvance
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundParity
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedView
import YesMetaZFC.SetTheory.LargeCardinal.Game.RequestState
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyReflect
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord
import YesMetaZFC.SetTheory.LargeCardinal.Game.TraceImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical

/-! # 原关系模型实际产生回答事件与下一请求

原查询表项和完整回答直接交给同一控制记录。返回回答后的原事件，
并对每个实际实数落子返回下一请求、严格增长的历史及保留的原事件。
轮号、标签、候选和类型全部使用该原模型自己的对象码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
/-- 固定本次真实落子，保留完整下一请求、历史增长及全部旧事件。 -/
def Tg_answer_move_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C}) (w η Ω z m χ γ Bγ Cᵣ S₀ Ac sc g : M.Domain) (s : Tg_archive_row_d M.Domain)
    (f : Tg_archive_frame_d M.Domain)
    (θ : Env (rt_model_l C nc) 46) (τ u t q x : (rt_model_l C nc).Domain) : Prop :=
  let N₀ := smdl_structure_l I (R := R) nx
  let P := rt_model_l C nc
  let ψ := tg_position_env_d
    (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env P 19) (θ.bound 19) t q
  ∃ v' t' j' n', P.mem v' (ψ.bound 6) ∧
  (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
  (¬ Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
    Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
  Formula.satisfies (⟨fun i => [ψ.bound 0, t', ψ.bound 20, v'].get i, fun _ => v'⟩ : Env P 4)
    (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
  P.SuccessorOf n' (ψ.bound 19) ∧
  Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3), fun _ => ψ.bound 0⟩ n' t' j')
    (tg_position0_m 0) ∧
  ∃ ε : Env P 46, (∀ i : Fin 19, ε.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
    ε.bound 19 = n' ∧ Formula.satisfies ε tg_issued0_m ∧ Rd_entry_d t' (ε.bound 21) (ψ.bound 17) ∧
    Formula.satisfies (⟨fun i => [ψ.bound 0, ε.bound 20, t', ε.bound 21].get i, fun _ => ε.bound 21⟩ : Env P 4)
      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
    P.mem (θ.bound 24) (ε.bound 24) ∧ M.PairMember I χ (ε.bound 24).val.val R ∧
    It_lower_d I γ N R (ε.bound 24).val.val ∧
    N₀.MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
    (θ.bound 20).val ≠ (ε.bound 20).val ∧
    Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
      (θ.bound 19).val.val (ε.bound 20).val.val (θ.bound 23).val.val τ.val.val u.val.val ∧
    Tg_saved_view_d I s.X s.R s.w s.U s.q γ g N R w C.val (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m (ε.bound 20).val.val ∧
    (∀ n s κ y : N₀.Domain,
      Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        n.val (θ.bound 20).val.val s.val κ.val y.val →
      Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        n.val (ε.bound 20).val.val s.val κ.val y.val) ∧
    ∃ m', M.SuccessorOf m' m ∧
      Tg_round_index_d I Ω z nx (ε.bound 0).val (ε.bound 19).val m' ∧
      ∃ r, Rt_tuple_d s.values_d r ∧
      ∀ H, M.IsSequenceOfLength I H m →
        ∃ H', M.IsSequenceOfLength I H' m' ∧
          (∀ l s, M.PairMember I l s H' ↔ M.PairMember I l s H ∨ l = m ∧ s = r) ∧
          (Tg_archive_views_d I Ω γ Bγ Cᵣ H N R Ac sc w C.val (θ.bound 4).val.val
            (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (θ.bound 20).val.val →
            Tg_archive_views_d I Ω γ Bγ Cᵣ H' N R Ac sc w C.val (θ.bound 4).val.val
              (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (ε.bound 20).val.val) ∧
          (Tg_archive_links_d I f H → Tg_archive_links_d I f H') ∧
          (Tg_archive_names_d I S₀ H → Tg_archive_names_d I S₀ H') ∧
          (Tg_archive_views_d I Ω γ Bγ Cᵣ H N R Ac sc w C.val (θ.bound 4).val.val
            (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (θ.bound 20).val.val →
            Tg_archive_links_d I f H →
            ∀ k, M.PairMember I k (ε.bound 19).val.val R →
              ∃ l r, M.mem l m' ∧ M.PairMember I l k z ∧ M.PairMember I l r H' ∧
                Tg_archive_entry_d I Ω γ Bγ Cᵣ N R Ac sc w C.val (θ.bound 4).val.val
                  (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (ε.bound 20).val.val l r ∧
                ∀ s : Tg_archive_row_d M.Domain, Rt_tuple_d s.values_d r → s.link_d f) ∧
          (Tg_archive_views_d I Ω γ Bγ Cᵣ H N R Ac sc w C.val (θ.bound 4).val.val
            (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (θ.bound 20).val.val →
            Tg_archive_links_d I f H →
            Tg_archive_names_d I S₀ H →
            ∃ r', Tg_request_state_d I Ω γ Bγ Cᵣ S₀ N R w η C.val Ac sc χ z m' H' r' f
              (fun i => (ε.bound i).val.val))

/-- 实际回答事件与所有后续落子，逐次保留同一完整结果。 -/
def Tg_answer_result_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C}) (w η Ω z m χ γ Bγ Cᵣ S₀ Ac sc g p : M.Domain) (s : Tg_archive_row_d M.Domain)
    (f : Tg_archive_frame_d M.Domain)
    (θ : Env (rt_model_l C nc) 46) (τ u : (rt_model_l C nc).Domain) : Prop :=
  let N₀ := smdl_structure_l I (R := R) nx
  let P := rt_model_l C nc
    ∃ v t q : P.Domain, KPair_d N₀ v.val τ.val u.val ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ (θ.bound 19) t q) (tg_position0_m 2) ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, t, θ.bound 20, v].get i, fun _ => v⟩ : Env P 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        (θ.bound 19).val.val t.val.val (θ.bound 23).val.val τ.val.val u.val.val ∧
      Tg_saved_view_d I s.X s.R s.w s.U s.q γ g N R w C.val (θ.bound 4).val.val
        (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m t.val.val ∧
      let ψ := tg_position_env_d
        (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env P 19) (θ.bound 19) t q
      (∀ x, P.mem x (ψ.bound 6) →
        Tg_answer_move_d I nx C nc w η Ω z m χ γ Bγ Cᵣ S₀ Ac sc g s f θ τ u t q x) ∧
      ∀ A, M.mem A Bγ → M.PairMember I A (θ.bound 6).val.val p →
        ∀ x, M.mem x A → ∃ a : P.Domain, M.PairMember I x a.val.val p ∧
          Tg_answer_move_d I nx C nc w η Ω z m χ γ Bγ Cᵣ S₀ Ac sc g s f θ τ u t q a

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.answer_native_l {N R w η C : M.Domain}
    (context : Tg_context_d I w N R η C) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := R) nx
    let C₀ : N₀.Domain := ⟨C, context.member⟩
    ∀ _hN : N₀.Models KP, ∀ nc : Nonempty {x : N₀.Domain // N₀.mem x C₀},
    let P := rt_model_l (M := N₀) C₀ nc
    ∀ θ : Env P 46, Formula.satisfies θ tg_issued0_m → (θ.bound 0).val.val = w →
    ∀ Ω z m₀, Tg_round_index_d I Ω z nx ⟨w,context.omega_mem⟩ (θ.bound 19).val m₀ →
    ∀ χ : N₀.Domain, N₀.IsOrdinal χ → N₀.MemberSubset χ (θ.bound 24).val →
    ∀ τ u B U D r m b f q : P.Domain,
    N₀.mem τ.val (θ.bound 5).val →
    Formula.satisfies (⟨fun i => [θ.bound 0, τ, θ.bound 26, θ.bound 1, θ.bound 1].get i,
      fun _ => θ.bound 0⟩ : Env P 5) tg_query_request0_m →
    Tg_query_data_d (θ.bound 11) τ (θ.bound 26) (θ.bound 1) (θ.bound 1) B U D r m b f q →
    Formula.satisfies (⟨fun i => [θ.bound 0, θ.bound 27, θ.bound 28, θ.bound 24, τ,
      θ.bound 30, θ.bound 31, D, θ.bound 25, u, θ.bound 36, θ.bound 37, r, b, f,
      θ.bound 38, θ.bound 39, θ.bound 40, θ.bound 41, θ.bound 42, θ.bound 43, θ.bound 44].get i,
      fun _ => θ.bound 0⟩ : Env P 22) tg_reply0_m →
    ∀ γ Bγ Cᵣ S₀ Ac sc g p, M.IsSetFunction I p → Tg_anchor_d I γ Bγ N R p →
    M.PairMember I S₀ (θ.bound 7).val.val p →
    ∀ s : Tg_archive_row_d M.Domain, ∀ f : Tg_archive_frame_d M.Domain,
    It_lower_d I γ N R (θ.bound 24).val.val →
    It_map_d f.G f.o f.n p →
    s.link_d f →
    Tg_saved_name_d I S₀ s.X s.R s.w s.U s.q s.p →
    Smdl_d I s.c s.X s.R → Tg_saved_d I s.w s.X s.R s.η s.C s.L s.U s.q →
    (∃ z₀, Rr_layer_d I Ω s.X s.R s.w z₀) →
    Tg_basis_d I γ Bγ Cᵣ s.w s.X s.R s.C s.p →
    (∃ l φ V Γ, Ic_agree_d I s.X s.R s.A s.π N R Ac sc s.L l φ s.U V Γ g) →
    ∀ o : Fin 54 → M.Domain, Tg_saved_code_d s.X s.R s.w s.U s.q o →
    It_lower_d I γ s.X s.R (o 15) →
    M.PairMember I (o 41) (θ.bound 23).val.val g →
    M.PairMember I (o 15) τ.val.val g → M.PairMember I (o 11) u.val.val g →
    (∃ s, M.PairMember I (o 40) s g ∧
      Tg_play_d I N R C (θ.bound 4).val.val (θ.bound 3).val.val (θ.bound 20).val.val s) →
    Tg_answer_result_d I nx C₀ nc w η Ω z m₀ χ.val γ Bγ Cᵣ S₀ Ac sc g p s f θ τ u := by
  intro N₀ C₀ hN nc P θ issued hw Ω z m₀ index χ ordinalχ lowerχ τ u B U D r m b f q below request query reply
    γ Bγ Cᵣ S₀ Ac sc g p function anchor treeName s frame currentLower rootMap sourceLink sourceName
    model saved numbers₀ sourceRoot common o code lower label domain type short
  let w₀ : N₀.Domain := ⟨w, context.omega_mem⟩
  have fs := context.finite_l nx hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  have same : (θ.bound 0).val = w₀ := Subtype.ext hw
  have finite : N₀.mem (θ.bound 26).val w₀ := by
    have data := request
    simp only [tg_query_request0_m, Formula.satisfies_conj_iff] at data
    exact same ▸ (Formula.satisfies_mem_iff ..).mp data.2.1
  have state := (tg_issued_sat_l J ext θ).mp issued
  have labels : Fn0_d (M := N₀) (θ.bound 26).val w₀ (θ.bound 23).val := by
    rw [← same]
    exact (fn0_sat_l hN.1 ..).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
        (⟨fun i => [θ.bound 26, θ.bound 0, θ.bound 23].get i, fun _ => θ.bound 0⟩ : Env P 3)).mp
        ((fn0_sat_l ext ..).mpr state.labels))
  obtain ⟨v, t, q, pair, next, endt, trace, advance⟩ :=
    tg_answer_advance_l hN fs nc θ issued below request query reply
  have record (h : P.Domain)
      (event : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v) :
      Tg_trace_d I N R w C (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        (θ.bound 19).val.val h.val.val (θ.bound 23).val.val τ.val.val u.val.val := by
    exact (tg_trace_native_l I nx w₀ C₀ (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val
      (θ.bound 19).val h.val (θ.bound 23).val τ.val u.val).mpr
      (tg_trace0_build_l hN.1 fs.transitive nc (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v
        finite labels pair ((tg_round_event_sat_l J ext ..).mpr event))
  have archive (h : P.Domain)
      (event : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v)
      (keep : N₀.MemberSubset (θ.bound 20).val h.val) :
      Tg_saved_view_d I s.X s.R s.w s.U s.q γ g N R w C (θ.bound 4).val.val
        (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m₀ h.val.val := by
    obtain ⟨s,is,play⟩ := short
    exact ⟨o,code,lower,(θ.bound 19).val.val,(θ.bound 23).val.val,τ.val.val,u.val.val,
      index.point,label,domain,type,record h event,s,is,
      play.native_mono_l I nx hN.1 C₀ fs.transitive nc J
        (θ.bound 4) (θ.bound 3) (θ.bound 20) h keep⟩
  suffices moves : ∀ x : P.Domain, P.mem x (θ.bound 6) →
      Tg_answer_move_d I nx C₀ nc w η Ω z m₀ χ.val γ Bγ Cᵣ S₀ Ac sc g s frame θ τ u t q x by
    have keep : N₀.MemberSubset (θ.bound 20).val t.val := fun s hs =>
      ((fseq_end_sat_l J ext ..).mp endt).subset_l J
        ⟨s,fs.transitive _ (θ.bound 20).property s hs⟩ hs
    refine ⟨v,t,q,pair,next,endt,record t trace,archive t trace keep,moves,?_⟩
    intro A hA hAa x hx
    obtain ⟨_,_,_,b,_,layer,_,fixed⟩ := anchor
    obtain ⟨a₀,_,hAa₀⟩ := layer.injection.1.2.2 A hA
    have equal : a₀ = (θ.bound 6).val.val := function.2 A a₀ (θ.bound 6).val.val
      (fixed A a₀ hAa₀) hAa
    obtain ⟨y,hy,hxy⟩ := layer.injection.1.2.2 x (layer.transitive A hA x hx)
    have member : N₀.mem ⟨y,hy⟩ (θ.bound 6).val :=
      Eq.mp (congrArg (fun b => M.PairMember I y b R) equal)
        ((layer.predecessors A a₀ hAa₀ y).mpr ⟨x,hx,hxy⟩)
    let a : P.Domain := ⟨⟨y,hy⟩,fs.transitive (θ.bound 6).val (θ.bound 6).property ⟨y,hy⟩ member⟩
    exact ⟨a,fixed x y hxy,moves a member⟩
  intro x hx
  obtain ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    growth, keep, proper, trace⟩ := advance x hx
  -- χ≤当前候选，而真实下一请求严格增大候选，故 χ 严格低于下一候选。
  let η₀ : N₀.Domain := ⟨η,context.height⟩
  have rankC := (rr_rank_native_l I nx hN η₀ C₀).mp ((rr_rank_truth_l I).mpr context.rank)
  have limitC : N₀.IsLimitOrdinal η₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => η₀)).mp context.limit)
  obtain ⟨boundε,regularε⟩ := tg_issued_control_l hN rankC limitC fs nc ε issued'
  have nextBound : N₀.mem χ (ε.bound 24).val :=
    ordinal_down_l hN ordinalχ (regularε.isCardinal.1.mem boundε) lowerχ growth
  have nextLower : It_lower_d I γ N R (ε.bound 24).val.val := by
    obtain ⟨a,s,layer,down⟩ := currentLower
    refine ⟨a,s,layer,fun x hx => ?_⟩
    obtain ⟨b,_,bx⟩ := (layer.image x).mp hx
    exact (regularε.isCardinal.1.mem boundε).transitive (θ.bound 24).val growth
      ⟨x,layer.injection.1.output_mem_of_pairMember bx⟩ (down x hx)
  -- 下一请求保存为同一原模型中的真实记录码，后续读取无需重新构造走法。
  obtain ⟨rε,recordε,valuesε⟩ := rf_record_save_l I nx hN.1 tg_issued0_m tg_issued0_closed_l
    C₀ fs.transitive fs.pair nc ε issued'
  -- 实际外部后继追加本轮完整原行，原结点与根图、工作图随记录一起保存。
  obtain ⟨m',hm',nextIndex,imageIndex,append⟩ := index.next n'.val
    ((rt_successor_l fs.transitive nc hN.1 n' (θ.bound 19)).mp succ)
  have imageIndex : M.PairMember I m' (ε.bound 19).val.val z := by
    rw [num]
    exact imageIndex
  have sameω : (ε.bound 0).val.val = w :=
    (congrArg (fun a => a.val.val) (head 0)).trans hw
  have numbers : Rr_layer_d I Ω N R (ε.bound 0).val.val z :=
    Eq.mpr (congrArg (fun a => Rr_layer_d I Ω N R a z) sameω) index.numbers
  obtain ⟨m'',future⟩ := tg_round_index_l I (ZF.modelsKP hZF) index.omega nx hN.1
    (ε.bound 0).val (ε.bound 19).val numbers ((numbers.image _).mpr ⟨m',hm',imageIndex⟩)
  have eq := numbers.injection.2 m'' m' (ε.bound 19).val.val future.point imageIndex
  subst m''
  obtain ⟨r₀,code₀⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) s.values_d
  have preserve (n s κ y : N₀.Domain)
      (old : Tg_trace_d I N R w C (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        n.val (θ.bound 20).val.val s.val κ.val y.val) :=
    old.native_mono_l I nx hN.1 w₀ C₀ fs.transitive nc J
      (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 20) (ε.bound 20) n s κ y keep
  refine ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    growth,nextBound,nextLower,keep,proper,record (ε.bound 20) trace,archive (ε.bound 20) trace keep,
    preserve,m',nextIndex,future,r₀,code₀,?_⟩
  intro H seq
  obtain ⟨H',seq',entries⟩ := append H seq r₀
  have updated (old : Tg_archive_views_d I Ω γ Bγ Cᵣ H N R Ac sc w C (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (θ.bound 20).val.val) :
      Tg_archive_views_d I Ω γ Bγ Cᵣ H' N R Ac sc w C (θ.bound 4).val.val
        (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (ε.bound 20).val.val := by
    intro l r hr
    rcases (entries l r).mp hr with hr | ⟨rfl,rfl⟩
    · obtain ⟨s,cs,ms,ss,ns,rs,l₀,φ,V,Γ,g₀,common₀,v,cv,low,n,t,κ,u,ix,it,iκ,iu,event,s₀,is₀,play⟩ := old l r hr
      have members := event.elim fun m _ => m
      exact ⟨s,cs,ms,ss,ns,rs,l₀,φ,V,Γ,g₀,common₀,v,cv,low,n,t,κ,u,ix,it,iκ,iu,
        preserve ⟨n,members 5⟩ ⟨t,members 7⟩ ⟨κ,members 8⟩ ⟨u,members 9⟩ event,s₀,is₀,
        play.native_mono_l I nx hN.1 C₀ fs.transitive nc J
          (θ.bound 4) (θ.bound 3) (θ.bound 20) (ε.bound 20) keep⟩
    · obtain ⟨l,φ,V,Γ,common⟩ := common
      exact ⟨s,code₀,model,saved,numbers₀,sourceRoot,l,φ,V,Γ,g,common,archive (ε.bound 20) trace keep⟩
  have linked (old : Tg_archive_links_d I frame H) : Tg_archive_links_d I frame H' :=
    old.push_l I code₀ sourceLink entries
  have named (old : Tg_archive_names_d I S₀ H) : Tg_archive_names_d I S₀ H' :=
    old.push_l I code₀ sourceName entries
  refine ⟨H',seq',entries,updated,linked,named,?_,?_⟩
  · intro old roots k hk
    obtain ⟨l,r,hl,point,entry⟩ := future.select H' seq' k hk
    exact ⟨l,r,hl,point,entry,updated old l r entry,fun s code => linked roots l r s entry code⟩
  · intro old roots names
    have e₇ : (ε.bound 7).val.val = (θ.bound 7).val.val := congrArg (fun x => x.val.val) (head 7)
    refine ⟨rε.val,context,recordε,valuesε,sameω,index.omega,index.numbers,future.finite,
      future.point,seq',linked roots,named names,
      ⟨p,rootMap,Eq.mpr (congrArg (fun S => M.PairMember I S₀ S p) e₇) treeName⟩,?_,nextLower,nextBound⟩
    have e₄ : (ε.bound 4).val.val = (θ.bound 4).val.val := congrArg (fun x => x.val.val) (head 4)
    have e₁ : (ε.bound 1).val.val = (θ.bound 1).val.val := congrArg (fun x => x.val.val) (head 1)
    have e₂ : (ε.bound 2).val.val = (θ.bound 2).val.val := congrArg (fun x => x.val.val) (head 2)
    have e₃ : (ε.bound 3).val.val = (θ.bound 3).val.val := congrArg (fun x => x.val.val) (head 3)
    rw [e₄,e₁,e₂,e₃]
    exact updated old

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所属模型内把完整回答送回实际控制层

极限秩层直接回收投影和名字域，不要求反射层满足 ZF。
同一秩历史构造回答的合法查询键，随后读取原控制表的全域性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u

/-- 同一目标反射层中的请求、完整回答、原表项及实际回答事件延伸。 -/
def Tg_answer_step_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    -- Y/S 是旧当前模型；t/g 是同一完整池及共同图，j 是原边，q₀ 是旧根图。
    -- A/π 与 A'/π' 是两侧复制，全部根坐标沿同一原边搬运。
    (c X R t g j q₀ χ w η C Y S s A π A' π' κ Ω z γ Bγ Cᵣ S₀ : M.Domain)
    (r₀ : Tg_archive_row_d M.Domain)
    (f f' : Tg_archive_frame_d M.Domain)
    (v : Fin 46 → M.Domain) (p : Fin 22 → M.Domain) : Prop :=
  r₀.link_d f' ∧ (∀ H, Tg_archive_links_d I f H → Tg_archive_links_d I f' H) ∧
  ∃ target : Smdl_d I c X R, Rf_ext_d I X R ∧ ∃ w' η' C',
    M.PairMember I w w' j ∧ M.PairMember I η η' j ∧ M.PairMember I C C' j ∧
  ∃ context : Tg_context_d I w' X R η' C',
  ∃ p', It_map_d f'.G f'.o f'.n p' ∧ M.IsSetFunction I p' ∧ M.IsSetInjective I p' ∧
    Tg_basis_d I γ Bγ Cᵣ w' X R C' p' ∧
  ∃ nc : Nonempty {x : (smdl_structure_l I (R := R) target.2.1).Domain //
    (smdl_structure_l I (R := R) target.2.1).mem x ⟨C', context.member⟩},
  ∃ ι : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C', context.member⟩ nc) 46,
  ∃ ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C', context.member⟩ nc) 22,
    (∀ i, M.PairMember I (v i) (ι.bound i).val.val j) ∧
    (∀ a b c, M.PairMember I a b q₀ → M.PairMember I b c j → M.PairMember I a c p') ∧
    Formula.satisfies ι tg_issued0_m ∧
    (ι.bound 0).val.val = w' ∧ It_lower_d I γ X R (ι.bound 24).val.val ∧
    M.PairMember I χ (ι.bound 5).val.val R ∧ M.PairMember I χ C' R ∧
    (∀ i, M.PairMember I (p i) (ρ.bound i).val.val t) ∧ Formula.satisfies ρ tg_reply0_m ∧
    M.PairMember I s (ι.bound 23).val.val t ∧
    M.PairMember I s (ι.bound 23).val.val g ∧
    M.PairMember I (p 4) (ρ.bound 4).val.val g ∧ M.PairMember I (p 9) (ρ.bound 9).val.val g ∧
    Tg_reply_link_d Eq ι.bound ρ.bound ∧
    M.PairMember I (ρ.bound 4).val.val (ι.bound 5).val.val R ∧
    Formula.satisfies (⟨fun i => [ι.bound 0,ρ.bound 4,ι.bound 26,ι.bound 1,ι.bound 1].get i,
      ι.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C', context.member⟩ nc) 5)
      tg_query_request0_m ∧
    ∃ B U D r m b h q,
      D = ρ.bound 7 ∧
      Tg_query_data_d (ι.bound 11) (ρ.bound 4) (ι.bound 26) (ι.bound 1) (ι.bound 1) B U D r m b h q ∧
      M.PairMember I r.val.val (ρ.bound 9).val.val R ∧
      M.PairMember I b.val.val (ρ.bound 9).val.val R ∧
      M.PairMember I h.val.val (ρ.bound 9).val.val R ∧
      Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 27,ι.bound 28,ρ.bound 4,B,U,D,r,b,h].get i,
        ι.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C', context.member⟩ nc) 11)
        tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 27,ι.bound 28,ι.bound 26,ι.bound 1,ι.bound 1,r,m,b,h,q].get i,
        ι.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C', context.member⟩ nc) 12)
        tg_query_row0_m ∧
    ∃ z' m₀, Rr_layer_d I Ω Y S w z ∧ M.PairMember I m₀ (v 19) z ∧
      Tg_round_index_d I Ω z' target.2.1 ⟨w',context.omega_mem⟩ (ι.bound 19).val m₀ ∧
      (∀ k L s, M.mem L Bγ → M.MemberSubset k Ω →
        Tg_prefix_d I k L Y S C (v 4) (v 3) (v 20) z q₀ s →
        Tg_prefix_d I k L X R C' (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val z' p' s) ∧
      (∀ u i, Formula.satisfies (tg_position_env_d
        ⟨fun k => ι.bound (k.castAdd 27),fun _ => ι.bound 0⟩ (ι.bound 19) u i)
          (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) ↔
        Descriptive.Gm_even_d I Ω m₀) ∧
      Tg_answer_result_d I target.2.1 ⟨C',context.member⟩ nc w' η' Ω z' m₀ χ
        γ Bγ Cᵣ S₀ A' π' g p' r₀ f' ι (ρ.bound 4) (ρ.bound 9) ∧
      Tg_trace_image_d I Y S w C (v 4) (v 1) (v 2) (v 3) (v 20) X R w' C'
        (ι.bound 4).val.val (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val (ι.bound 20).val.val j z z' ∧
      Tg_archive_trace_d I Y S A π w C (v 4) (v 1) (v 2) (v 3) (v 20) X R A' π' w' C'
        (ι.bound 4).val.val (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val (ι.bound 20).val.val j κ z z' ∧
      ∀ H b, Ic_bound_d I f.H f.Q Y S π f.n b → M.PairMember I b κ S →
        Tg_archive_links_d I f H → Tg_archive_views_d I Ω γ Bγ Cᵣ H Y S A π w C (v 4) (v 1) (v 2) (v 3) z (v 20) →
        Tg_archive_views_d I Ω γ Bγ Cᵣ H X R A' π' w' C' (ι.bound 4).val.val
          (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val z' (ι.bound 20).val.val

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 保留同一个回答，仅采用当前实际查询表中的三个代码。 -/
def tg_reply_table_env_d {N : Structure.{u}} (ρ : Env N 22) (r b h : N.Domain) : Env N 22 :=
  ⟨fun i => [ρ.bound 0,ρ.bound 1,ρ.bound 2,ρ.bound 3,ρ.bound 4,ρ.bound 5,ρ.bound 6,ρ.bound 7,
    ρ.bound 8,ρ.bound 9,ρ.bound 10,ρ.bound 11,r,b,h,
    ρ.bound 15,ρ.bound 16,ρ.bound 17,ρ.bound 18,ρ.bound 19,ρ.bound 20,ρ.bound 21].get i,ρ.free⟩

theorem tg_reply_rank_reflect_l {ω η C : M.Domain} (hω : M.IsOmega ω)
    (rank : V_d I η C) (limit : M.IsLimitOrdinal η) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 22)
    (hl : M.mem (ρ.bound 1).val ω)
    (valid : Formula.satisfies (image_env_l Subtype.val ρ) tg_reply0_m) :
    Formula.satisfies ρ tg_reply0_m := by
  let slots : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have data := (tg_reply_sat_l (ZF.modelsKP hZF) (image_env_l Subtype.val ρ)
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
    (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) slots).mp valid
  obtain ⟨subset, v, drop, subtype, hr, hq, hh⟩ := data
  have hv : M.mem v C := v_subset_mem_l I rank (ρ.bound 6).property
    (fun x hx => ((drop.2 x).mp hx).1)
  obtain ⟨A, names⟩ := tn_names_exists_l hZF (ρ.bound 1).val (ρ.bound 5).val
  have hA := names.rank_mem_l (ZF.modelsKP hZF) hω rank limit fs.omega_mem hl (ρ.bound 5).property
  let v₀ : (rt_model_l C nc).Domain := ⟨v, hv⟩
  have sub : Formula.satisfies ρ (Formula.subset (.bound 9) (.bound 7)) :=
    (rt_model_delta_l fs.transitive nc (.atom ..) ρ).mpr ((Formula.satisfies_subset_iff ..).mpr subset)
  simp only [tg_reply0_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  refine ⟨sub, v₀, ?_, ?_, hr, hq, hh⟩
  · apply (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
      (ρ.push v₀) (.bound 2) (.bound 3) (.bound 7) (.bound 9) .newest).mpr
    exact drop
  · apply ts_subtype_reflect_l (ZF.modelsKP hZF) fs.transitive nc (ρ.push v₀)
      (.bound 0 : Term 22).weaken (.bound 1 : Term 22).weaken (.bound 3 : Term 22).weaken
      (.bound 4 : Term 22).weaken (.bound 2 : Term 22).weaken (.bound 5 : Term 22).weaken
      (.bound 9 : Term 22).weaken (.bound 10 : Term 22).weaken (.bound 11 : Term 22).weaken
      .newest (fun i => (slots i).weaken) hA names
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
      @eval_image_env_l (rt_model_l C nc) M Subtype.val] using subtype

/-- 回答高度属于实际反射层时，完整秩历史和常量域给出原查询表的合法键。 -/
theorem tg_query_request_rank_l {ω η C : M.Domain} (hω : M.IsOmega ω)
    (rank : V_d I η C) (limit : M.IsLimitOrdinal η) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (τ k e : (rt_model_l C nc).Domain)
    (hτ : M.IsLimitOrdinal τ.val) (hk : M.mem k.val ω) (he : ∀ x, ¬ M.mem x e.val) :
    Formula.satisfies (⟨fun i => [⟨ω, fs.omega_mem⟩,τ,k,e,e].get i,
      fun _ => ⟨ω, fs.omega_mem⟩⟩ : Env (rt_model_l C nc) 5) tg_query_request0_m := by
  have hτη := ZF.v_ordinal_height_l hZF rank hτ.1 τ.property
  obtain ⟨B, U, rB, hUC, constants⟩ := tt_constants_exists_l hZF rank limit hτη
  have hBC := ZF.v_mem_l I hZF rB rank hτη
  obtain ⟨D, f, hD, hf, history, _⟩ := vr_source_l hZF rank limit hτη rB
  have relative : Vr_d C τ.val B := ⟨D, f, hD, hf, fun x _ => history x⟩
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e.val from he)
  have heB := KP.v_ordinal_subset_l (ZF.modelsKP hZF) rB e.val
    (hω.subset_limitOrdinal (ZF.modelsKP hZF) hτ e.val heω)
  let ρ : Env (rt_model_l C nc) 5 := ⟨fun i => [⟨ω, fs.omega_mem⟩,τ,k,e,e].get i,
    fun _ => ⟨ω, fs.omega_mem⟩⟩
  simp only [tg_query_request0_m, Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff]
  refine ⟨(rt_limit_l fs.transitive nc (ZF.modelsKP hZF) τ).mpr hτ, hk, ⟨B,hBC⟩, ⟨U,hUC⟩, ?_, ?_,
    (constants e.val).mpr (Or.inl heB), (constants e.val).mpr (Or.inl heB)⟩
  · exact (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ((ρ.push ⟨B,hBC⟩).push ⟨U,hUC⟩)
      (.bound 3) (.bound 1)).mpr relative
  · apply (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 3) (.bound 1) (.bound 0))
      ((ρ.push ⟨B,hBC⟩).push ⟨U,hUC⟩)).mpr
    exact (tt_constants0_sat_l hZF.1 ..).mpr constants

/-- 表中三个原查询已经核验为真时，完整规则 (7) 使用这些代码仍在同一反射层成立。 -/
theorem tg_reply_table_l {ω η C : M.Domain} (hω : M.IsOmega ω)
    (rank : V_d I η C) (limit : M.IsLimitOrdinal η) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 22)
    (hl : M.mem (ρ.bound 1).val ω) (reply : Formula.satisfies ρ tg_reply0_m)
    (r b h : (rt_model_l C nc).Domain)
    (hr : M.mem r.val (ρ.bound 9).val) (hb : M.mem b.val (ρ.bound 9).val)
    (hh : M.mem h.val (ρ.bound 9).val) :
    Formula.satisfies (tg_reply_table_env_d ρ r b h) tg_reply0_m := by
  let slots : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have actual := tg_reply_source_l (ZF.modelsKP hZF) fs.transitive nc fs.pair ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
    (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) slots reply
  obtain ⟨sub,v,drop,subtype,_,_,_⟩ := actual
  let θ := tg_reply_table_env_d ρ r b h
  let ε : Env M 22 := image_env_l Subtype.val θ
  have values : (fun i => (slots i).eval ε) = (fun i => ((slots i).eval ρ).val) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies ε tg_reply0_m := by
    apply (tg_reply_sat_l (ZF.modelsKP hZF) ε (.bound 0) (.bound 1) (.bound 2) (.bound 3)
      (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11)
      (.bound 12) (.bound 13) (.bound 14) slots).mpr
    rw [values]
    exact ⟨sub,v,drop,subtype,hr,hb,hh⟩
  exact tg_reply_rank_reflect_l hZF hω rank limit fs nc θ hl valid

/-- 已搬运回答与请求在同一原模型中对齐后，实际回到该请求的控制层并读取查询表。 -/
theorem tg_answer_input_l {ω η C : M.Domain} (hω : M.IsOmega ω)
    (rank : V_d I η C) (limit : M.IsLimitOrdinal η) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46) (ρ : Env M 22)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω)
    (reply : Formula.satisfies ρ tg_reply0_m)
    (same : Tg_reply_link_d Eq (fun i => (ι.bound i).val) ρ.bound)
    (hQ : M.mem (ρ.bound 7) C) (hn : M.mem (ρ.bound 1) ω) (hτ : M.IsLimitOrdinal (ρ.bound 4)) :
    ∃ θ : Env (rt_model_l C nc) 22, (∀ i, (θ.bound i).val = ρ.bound i) ∧
      Formula.satisfies θ tg_reply0_m ∧ Tg_reply_link_d Eq ι.bound θ.bound ∧
      M.mem (θ.bound 4).val (ι.bound 5).val ∧
      Formula.satisfies (⟨fun i => [ι.bound 0,θ.bound 4,ι.bound 26,ι.bound 1,ι.bound 1].get i,
        ι.free⟩ : Env (rt_model_l C nc) 5) tg_query_request0_m ∧
      ∃ B U D r m b h q,
        Tg_query_data_d (ι.bound 11) (θ.bound 4) (ι.bound 26) (ι.bound 1) (ι.bound 1) B U D r m b h q ∧
        Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 27,ι.bound 28,θ.bound 4,B,U,D,r,b,h].get i,
          ι.free⟩ : Env (rt_model_l C nc) 11) tg_reply_language0_m ∧
        Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 27,ι.bound 28,ι.bound 26,ι.bound 1,ι.bound 1,r,m,b,h,q].get i,
          ι.free⟩ : Env (rt_model_l C nc) 12) tg_query_row0_m := by
  have hKP := ZF.modelsKP hZF
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  have inC i : M.mem (ρ.bound ([0,1,2,3,5,6,8,10,11,15,16,17,18,19,20,21].get i)) C :=
    same i ▸ (ι.bound ([0,27,28,24,30,31,25,36,37,38,39,40,41,42,43,44].get i)).property
  let slots : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have actual := (tg_reply_sat_l hKP ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11)
    (.bound 12) (.bound 13) (.bound 14) slots).mp reply
  obtain ⟨_, _, _, ⟨bound, _, _, query, _⟩, hr, hb, hh⟩ := actual
  have small x (hx : M.mem x (ρ.bound 5)) := fs.transitive _ (inC 4) x hx
  have hwC := small _ query.constants.1
  have members : ∀ i, M.mem (ρ.bound i) C := by
    simp only [Fin.forall_fin_succ]
    exact ⟨inC 0, inC 1, inC 2, inC 3, small _ query.constants.2.2.2.1,
      inC 4, inC 5, hQ, inC 6, hwC, inC 7, inC 8,
      fs.transitive _ hwC _ hr, fs.transitive _ hwC _ hb, fs.transitive _ hwC _ hh,
      inC 9, inC 10, inC 11, inC 12, inC 13, inC 14, inC 15, fun i => Fin.elim0 i⟩
  let θ : Env (rt_model_l C nc) 22 := ⟨fun i => ⟨ρ.bound i, members i⟩, fun _ => ⟨ρ.bound 0, members 0⟩⟩
  have reflected := tg_reply_rank_reflect_l hZF hω rank limit fs nc θ hn
    ((Formula.closed_env_l tg_reply0_m tg_reply0_closed_l (ρ := ρ) (η := image_env_l Subtype.val θ) rfl).mp reply)
  obtain ⟨below, regular⟩ := tg_issued_control_l hKP rank limit fs nc ι issued
  have hτκ : M.mem (ρ.bound 4) (ι.bound 24).val :=
    Eq.mp (congrArg (M.mem (ρ.bound 4)) (same 3).symm) bound
  have hτδ := regular.isCardinal.1.transitive _ below _ hτκ
  have hnι : M.mem (ι.bound 27).val ω := Eq.mp (congrArg (fun x => M.mem x ω) (same 1).symm) hn
  have finite := hω.transitive hKP _ hnι _ state.first.predecessor_mem
  have rules := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at rules
  have rules := rules.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have empty : ∀ x, ¬ M.mem x (ι.bound 1).val := fun x hx =>
    (Formula.satisfies_isEmpty_iff ..).mp rules.2.1
      ⟨x, fs.transitive _ (ι.bound 1).property x hx⟩ hx
  have request := tg_query_request_rank_l hZF hω rank limit fs nc
    (θ.bound 4) (ι.bound 26) (ι.bound 1) hτ finite empty
  let key : Env (rt_model_l C nc) 5 :=
    ⟨fun i => [ι.bound 0,θ.bound 4,ι.bound 26,ι.bound 1,ι.bound 1].get i, ι.free⟩
  let raw : Env (rt_model_l C nc) 5 :=
    ⟨fun i => [⟨ω,fs.omega_mem⟩,θ.bound 4,ι.bound 26,ι.bound 1,ι.bound 1].get i, fun _ => ⟨ω,fs.omega_mem⟩⟩
  have truth : Formula.satisfies key tg_query_request0_m :=
    (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := raw) (η := key)
      (funext (Fin.cases (Subtype.ext hw.symm)
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))).mp request
  let control : Env (rt_model_l C nc) 19 := ⟨fun i => ι.bound (i.castAdd 27), ι.free⟩
  have controlTruth : Formula.satisfies control tg_control0_m :=
    (Formula.closed_env_l tg_control0_m tg_control0_closed_l
      (ρ := (⟨fun i => ι.bound (i.castAdd 27), fun _ => ι.bound 0⟩ : Env (rt_model_l C nc) 19))
      (η := control) rfl).mp state.control
  obtain ⟨B,U,D,r,m,b,h,q,l,n,table,sl,sn,language,queries⟩ :=
    tg_control_query_l ext control key controlTruth rfl hτδ truth
  have eql := sl.eq ext state.first
  have eqn := sn.eq ext (eql.symm ▸ state.last)
  subst l n
  exact ⟨θ, fun _ => rfl, reflected, fun i => Subtype.ext (same i), hτδ, truth,
    B,U,D,r,m,b,h,q,table,language,queries⟩

end YesMetaZFC.SetTheory.LargeCardinal
