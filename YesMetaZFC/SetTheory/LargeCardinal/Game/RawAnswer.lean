import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerAdvance
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord

/-! # 原回答、实际落子与完整下一请求

同一次回答的事件和短图进入十一项原档案。落子后保留旧列所选共同图、
根交换方块及根切片，再追加本轮真实行并保存下一请求码。
当前支撑只须不超过候选；严格的下一界来自原输入规则的实际增长。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u

/-- 给定原生合法输入产生的实际落子、十一项追加和完整下一请求。 -/
def Tg_raw_answer_move_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C})
    (w η Ω z m χ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g : M.Domain)
    (s : Tg_raw_archive_row_d M.Domain) (frame : Tg_raw_archive_frame_d M.Domain)
    (θ : Env (rt_model_l C nc) 46) (τ u t q x : (rt_model_l C nc).Domain) : Prop :=
  let N₀ := smdl_structure_l I (R := R) nx
  let P := rt_model_l C nc
  let ψ := tg_position_env_d
    (⟨fun i => θ.bound (i.castAdd 27),fun _ => θ.bound 0⟩ : Env P 19) (θ.bound 19) t q
  ∃ v' t' j' n', P.mem v' (ψ.bound 6) ∧
    (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
    (¬ Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
      Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
    Formula.satisfies (⟨fun i => [ψ.bound 0,t',ψ.bound 20,v'].get i,fun _ => v'⟩ : Env P 4)
      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
    P.SuccessorOf n' (ψ.bound 19) ∧
    Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3),fun _ => ψ.bound 0⟩ n' t' j')
      (tg_position0_m 0) ∧
    ∃ ε : Env P 46, (∀ i : Fin 19, ε.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
      ε.bound 19 = n' ∧ Formula.satisfies ε tg_issued0_m ∧ Rd_entry_d t' (ε.bound 21) (ψ.bound 17) ∧
      Formula.satisfies (⟨fun i => [ψ.bound 0,ε.bound 20,t',ε.bound 21].get i,fun _ => ε.bound 21⟩ : Env P 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      P.mem (θ.bound 24) (ε.bound 24) ∧ N₀.MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
      (θ.bound 20).val ≠ (ε.bound 20).val ∧
      Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        (θ.bound 19).val.val (ε.bound 20).val.val (θ.bound 23).val.val τ.val.val u.val.val ∧
      Tg_raw_saved_view_d I s.X s.R s.w s.U s.q g N R w C.val (θ.bound 4).val.val
        (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m (ε.bound 20).val.val ∧
      ∃ m' H' r' r, M.SuccessorOf m' m ∧
        Tg_round_index_d I Ω z nx (ε.bound 0).val (ε.bound 19).val m' ∧
        Rt_tuple_d s.values_d r ∧
        (∀ l a, M.PairMember I l a H' ↔ M.PairMember I l a H ∨ l = m ∧ a = r) ∧
        Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C.val χ z m' H' r' p frame
          (fun i => (ε.bound i).val.val)

/-- 同一次回答位置及每个原生合法输入的完整后继。 -/
def Tg_raw_answer_result_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C})
    (w η Ω z m χ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g : M.Domain)
    (s : Tg_raw_archive_row_d M.Domain) (frame : Tg_raw_archive_frame_d M.Domain)
    (θ : Env (rt_model_l C nc) 46) (τ u : (rt_model_l C nc).Domain) : Prop :=
  let N₀ := smdl_structure_l I (R := R) nx
  let P := rt_model_l C nc
  ∃ v t q : P.Domain, KPair_d N₀ v.val τ.val u.val ∧
    Formula.satisfies (tg_position_env_d
      ⟨fun i => θ.bound (i.castAdd 27),fun _ => θ.bound 0⟩ (θ.bound 19) t q) (tg_position0_m 2) ∧
    Formula.satisfies (⟨fun i => [θ.bound 0,t,θ.bound 20,v].get i,fun _ => v⟩ : Env P 4)
      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
    Tg_trace_d I N R w C.val (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
      (θ.bound 19).val.val t.val.val (θ.bound 23).val.val τ.val.val u.val.val ∧
    Tg_raw_saved_view_d I s.X s.R s.w s.U s.q g N R w C.val (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m t.val.val ∧
    let ψ := tg_position_env_d
      (⟨fun i => θ.bound (i.castAdd 27),fun _ => θ.bound 0⟩ : Env P 19) (θ.bound 19) t q
    ∀ x, P.mem x (ψ.bound 6) →
      Tg_raw_answer_move_d I nx C nc w η Ω z m χ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g s frame θ τ u t q x

variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem Tg_context_d.answer_raw_l {N R w η C : M.Domain}
    (context : Tg_context_d I w N R η C) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := R) nx
    let Cn : N₀.Domain := ⟨C,context.member⟩
    ∀ _hN : N₀.Models KP, ∀ nc : Nonempty {x : N₀.Domain // N₀.mem x Cn},
    let P := rt_model_l Cn nc
    ∀ θ : Env P 46, Formula.satisfies θ tg_issued0_m → (θ.bound 0).val.val = w →
    ∀ Ω z m₀, Tg_round_index_d I Ω z nx ⟨w,context.omega_mem⟩ (θ.bound 19).val m₀ →
    ∀ χ : N₀.Domain, N₀.MemberSubset χ (θ.bound 24).val →
    ∀ τ u B U D r m b f q : P.Domain,
    N₀.mem τ.val (θ.bound 5).val →
    Formula.satisfies (⟨fun i => [θ.bound 0,τ,θ.bound 26,θ.bound 1,θ.bound 1].get i,
      fun _ => θ.bound 0⟩ : Env P 5) tg_query_request0_m →
    Tg_query_data_d (θ.bound 11) τ (θ.bound 26) (θ.bound 1) (θ.bound 1) B U D r m b f q →
    Formula.satisfies (⟨fun i => [θ.bound 0,θ.bound 27,θ.bound 28,θ.bound 24,τ,
      θ.bound 30,θ.bound 31,D,θ.bound 25,u,θ.bound 36,θ.bound 37,r,b,f,
      θ.bound 38,θ.bound 39,θ.bound 40,θ.bound 41,θ.bound 42,θ.bound 43,θ.bound 44].get i,
      fun _ => θ.bound 0⟩ : Env P 22) tg_reply0_m →
    ∀ X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p g V Γ, ∀ s : Tg_raw_archive_row_d M.Domain,
    ∀ frame : Tg_raw_archive_frame_d M.Domain,
    It_map_d frame.G frame.o frame.n p →
    Rd_entry_d S₀ (θ.bound 7).val.val p → Rd_entry_d A₀ (θ.bound 6).val.val p →
    s.link_d frame → Tg_saved_name_d I S₀ s.X s.R s.w s.U s.q s.p →
    Smdl_d I s.c s.X s.R → Tg_saved_d I s.w s.X s.R s.η s.C s.L s.U s.q →
    (∃ z₀, Rr_layer_d I Ω s.X s.R s.w z₀) →
    Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ s.X s.R s.w s.C s.U s.q s.p →
    Tg_raw_cofinal_d I s.w s.X s.R s.L →
    Ic_common_d I s.X s.R N R s.L χ.val s.U V Γ g → Tg_root_square_d D₀ s.p p g →
    ∀ o : Fin 54 → M.Domain, Tg_saved_code_d s.X s.R s.w s.U s.q o →
    Rd_entry_d (o 41) (θ.bound 23).val.val g →
    Rd_entry_d (o 15) τ.val.val g → Rd_entry_d (o 11) u.val.val g →
    (∃ a, Rd_entry_d (o 40) a g ∧
      Tg_play_d I N R C (θ.bound 4).val.val (θ.bound 3).val.val (θ.bound 20).val.val a) →
    ∀ γ Vγ tγ, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C p γ Vγ tγ →
    Rd_entry_d w Vγ R → (∀ x, Rd_entry_d x γ R → Rd_entry_d x (θ.bound 24).val.val R) →
    ∀ H, M.IsSequenceOfLength I H m₀ →
    Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p H N R χ.val w C (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (θ.bound 20).val.val →
    Tg_raw_archive_links_d I frame H →
    Tg_raw_answer_result_d I nx Cn nc w η Ω z m₀ χ.val X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p H g s frame θ τ u := by
  intro N₀ Cn hN nc P θ issued hw Ω z m₀ index χ lowerχ τ u B U D r m b f q below request query reply
    X₀ R₀ γ₀ D₀ C₀ A₀ S₀ p g V Γ s frame rootMap treeName alphabet sourceLink sourceName
    model saved numbers₀ sourceBase sourceCofinal common roots o code label domain type short
    γ Vγ tγ slice omegaSlice lowerγ H seq old oldLinks
  let w₀ : N₀.Domain := ⟨w,context.omega_mem⟩
  have fs := context.finite_l nx hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  have same : (θ.bound 0).val = w₀ := Subtype.ext hw
  have finite : N₀.mem (θ.bound 26).val w₀ := by
    have data := request
    simp only [tg_query_request0_m,Formula.satisfies_conj_iff] at data
    exact same ▸ (Formula.satisfies_mem_iff ..).mp data.2.1
  have state := (tg_issued_sat_l J ext θ).mp issued
  have labels : Fn0_d (M := N₀) (θ.bound 26).val w₀ (θ.bound 23).val := by
    rw [← same]
    exact (fn0_sat_l hN.1 ..).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
        (⟨fun i => [θ.bound 26,θ.bound 0,θ.bound 23].get i,fun _ => θ.bound 0⟩ : Env P 3)).mp
        ((fn0_sat_l ext ..).mpr state.labels))
  have rankχ := (rr_rank_native_l I nx hN χ ⟨V,common.right_rank.2.1⟩).mp common.right_rank
  have ordinalχ := v_ordinal_l (kp_pair_l hN) rankχ
  have rawOrdinal : Rr_truth_d I N R (KP.ord0_m .newest) (fun _ : Fin 1 => χ.val) :=
    (rr_truth_native_l I nx (KP.ord0_m .newest) (by simp -implicitDefEqProofs) (fun _ : Fin 1 => χ)).mpr
      ((KP.ord0_sat_l hN _ .newest).mpr ordinalχ)
  obtain ⟨v,t,q,pair,next,endt,trace,advance⟩ :=
    tg_answer_advance_l hN fs nc θ issued below request query reply
  have record (h : P.Domain)
      (event : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v) :
      Tg_trace_d I N R w C (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        (θ.bound 19).val.val h.val.val (θ.bound 23).val.val τ.val.val u.val.val :=
    (tg_trace_native_l I nx w₀ Cn (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val
      (θ.bound 19).val h.val (θ.bound 23).val τ.val u.val).mpr
      (tg_trace0_build_l hN.1 fs.transitive nc (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v
        finite labels pair ((tg_round_event_sat_l J ext ..).mpr event))
  have archive (h : P.Domain)
      (event : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v)
      (keep : N₀.MemberSubset (θ.bound 20).val h.val) :
      Tg_raw_saved_view_d I s.X s.R s.w s.U s.q g N R w C (θ.bound 4).val.val
        (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z m₀ h.val.val := by
    obtain ⟨a,ia,play⟩ := short
    exact ⟨o,code,(θ.bound 19).val.val,(θ.bound 23).val.val,τ.val.val,u.val.val,
      index.point,label,domain,type,record h event,a,ia,
      play.native_mono_l I nx hN.1 Cn fs.transitive nc J
        (θ.bound 4) (θ.bound 3) (θ.bound 20) h keep⟩
  have keepAnswer : N₀.MemberSubset (θ.bound 20).val t.val := fun a ha =>
    ((fseq_end_sat_l J ext ..).mp endt).subset_l J
      ⟨a,fs.transitive _ (θ.bound 20).property a ha⟩ ha
  refine ⟨v,t,q,pair,next,endt,record t trace,archive t trace keepAnswer,?_⟩
  dsimp only
  intro x hx
  obtain ⟨v',t',j',n',hv,even,odd,digit,succ,start,ε,head,num,issued',value,aux,
    growth,keep,proper,trace⟩ := advance x hx
  let η₀ : N₀.Domain := ⟨η,context.height⟩
  have rankC := (rr_rank_native_l I nx hN η₀ Cn).mp ((rr_rank_truth_l I).mpr context.rank)
  have limitC : N₀.IsLimitOrdinal η₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => η₀)).mp context.limit)
  obtain ⟨boundε,regularε⟩ := tg_issued_control_l hN rankC limitC fs nc ε issued'
  have ordinalε := regularε.isCardinal.1.mem boundε
  have nextBound : N₀.mem χ (ε.bound 24).val := ordinal_down_l hN ordinalχ ordinalε lowerχ growth
  have nextSlice : ∀ x, Rd_entry_d x γ R → Rd_entry_d x (ε.bound 24).val.val R := by
    intro x hx
    obtain ⟨a,_,_,ax⟩ := (slice.endpoint.2.2 x).mp hx
    exact ordinalε.transitive (θ.bound 24).val growth
      ⟨x,slice.injection.1.output_mem_of_pairMember ax⟩ (lowerγ x hx)
  -- 记录、数字后继与十一项追加都使用本次实际 ε。
  obtain ⟨rε,recordε,valuesε⟩ := rf_record_save_l I nx hN.1 tg_issued0_m tg_issued0_closed_l
    Cn fs.transitive fs.pair nc ε issued'
  obtain ⟨m',hm',successor,imageIndex,append⟩ := index.next n'.val
    ((rt_successor_l fs.transitive nc hN.1 n' (θ.bound 19)).mp succ)
  have imageIndex : M.PairMember I m' (ε.bound 19).val.val z := num.symm ▸ imageIndex
  have sameHead (i : Fin 19) : (ε.bound (i.castAdd 27)).val.val = (θ.bound (i.castAdd 27)).val.val :=
    congrArg (fun a => a.val.val) ((head i).trans (by simp only [tg_position_env_d,Fin.addCases_left]))
  have sameω : (ε.bound 0).val.val = w := (sameHead 0).trans hw
  have numbers : Rr_layer_d I Ω N R (ε.bound 0).val.val z :=
    Eq.mpr (congrArg (fun a => Rr_layer_d I Ω N R a z) sameω) index.numbers
  obtain ⟨m'',future⟩ := tg_round_index_l I hKP index.omega nx hN.1
    (ε.bound 0).val (ε.bound 19).val numbers ((numbers.image _).mpr ⟨m',hm',imageIndex⟩)
  have eq := numbers.injection.2 m'' m' (ε.bound 19).val.val future.point imageIndex
  subst m''
  obtain ⟨r₀,code₀⟩ := s.tuple_l hKP
  obtain ⟨H',seq',entries⟩ := append H seq r₀
  have preserve (n a κ y : N₀.Domain)
      (event : Tg_trace_d I N R w C (θ.bound 4).val.val (θ.bound 1).val.val (θ.bound 2).val.val
        n.val (θ.bound 20).val.val a.val κ.val y.val) :=
    event.native_mono_l I nx hN.1 w₀ Cn fs.transitive nc J
      (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 20) (ε.bound 20) n a κ y keep
  have raised : Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p H N R χ.val w C (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (ε.bound 20).val.val := by
    intro k r hr
    obtain ⟨a,ca,ma,sa,na,namea,basea,cofinala,l,Va,Γa,ga,commona,uppera,rootsa,
      v,cv,n,t,κ,u,ix,it,iκ,iu,event,s₀,is₀,play⟩ := old k r hr
    have members := event.elim fun m _ => m
    exact ⟨a,ca,ma,sa,na,namea,basea,cofinala,l,Va,Γa,ga,commona,uppera,rootsa,
      v,cv,n,t,κ,u,ix,it,iκ,iu,
      preserve ⟨n,members 5⟩ ⟨t,members 7⟩ ⟨κ,members 8⟩ ⟨u,members 9⟩ event,s₀,is₀,
      play.native_mono_l I nx hN.1 Cn fs.transitive nc J
        (θ.bound 4) (θ.bound 3) (θ.bound 20) (ε.bound 20) keep⟩
  have fresh : Tg_raw_archive_entry_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N R χ.val w C (θ.bound 4).val.val
      (θ.bound 1).val.val (θ.bound 2).val.val (θ.bound 3).val.val z (ε.bound 20).val.val m₀ r₀ :=
    ⟨s,code₀,model,saved,numbers₀,sourceName,sourceBase,sourceCofinal,χ.val,V,Γ,g,common,Or.inr rfl,roots,
      archive (ε.bound 20) trace keep⟩
  have updated := Tg_raw_archive_views_d.push_l I raised fresh entries
  have linked := Tg_raw_archive_links_d.push_l I oldLinks code₀ sourceLink entries
  have requestε : Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ.val z m' H' rε.val p frame
      (fun i => (ε.bound i).val.val) := by
    refine ⟨context,recordε,valuesε,sameω,index.omega,index.numbers,hm',imageIndex,seq',linked,
      rootMap,?_,?_,?_,rawOrdinal,nextBound,γ,Vγ,tγ,slice,omegaSlice,nextSlice⟩
    · exact Eq.mpr (congrArg (fun a => Rd_entry_d S₀ a p) (sameHead 7)) treeName
    · exact Eq.mpr (congrArg (fun a => Rd_entry_d A₀ a p) (sameHead 6)) alphabet
    · rw [show (ε.bound 4).val.val = (θ.bound 4).val.val from sameHead 4,
        show (ε.bound 1).val.val = (θ.bound 1).val.val from sameHead 1,
        show (ε.bound 2).val.val = (θ.bound 2).val.val from sameHead 2,
        show (ε.bound 3).val.val = (θ.bound 3).val.val from sameHead 3]
      exact updated
  exact ⟨v',t',j',n',hv,even,odd,digit,succ,start,ε,head,num,issued',value,aux,growth,keep,proper,
    record (ε.bound 20) trace,archive (ε.bound 20) trace keep,m',H',rε.val,r₀,
    successor,future,code₀,entries,requestε⟩

end YesMetaZFC.SetTheory.LargeCardinal
