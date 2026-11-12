import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep

/-! # 合法回答与下一实数落子中的档案维护

原控制记录产生实际追加历史。内部编码与源幂集计数产生新行的完整字母
枚举；原六十二槽及已对应的回答写入背景有限序列。下一实数阶段继续
保存全部旧事件和刚登记的新行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 对实际已落下请求的合法回答，同时追加历史和原回合档案集合。 -/
theorem Td_archive_d.answer_l
    {Ω c₀ X₀ Da m cN N R z χ cA A RA qA zA L l U V Δ g i D₀ q d H : M.Domain}
    (hΩ : M.IsOmega Ω) (hm : M.mem m Ω) (sequence : M.IsSequenceOfLength I Da m)
    (mn : Smdl_d I cN N R) (native : (smdl_structure_l I (R := R) mn.2.1).Models ZF)
    (ma : Smdl_d I cA A RA)
    (hA : (smdl_structure_l I (R := RA) ma.2.1).Models KP)
    (fromA : Smap_d I Ω c₀ cA X₀ A qA)
    (ρ : Env (smdl_structure_l I (R := RA) ma.2.1) 62)
    (round : Formula.satisfies ρ td_round0_m)
    (rootLow : ∀ a x, M.mem a D₀ → Rd_entry_d a x qA → Rd_entry_d x (ρ.bound 1).val RA)
    (lettersRoot : Rd_entry_d Ar (ρ.bound 50).val qA)
    (treeRoot : Rd_entry_d Sr (ρ.bound 22).val qA)
    (depth : Td_depth_d I Ω A RA (ρ.bound 47).val d H)
    (chosen : Td_pick_d I Ω d H (ρ.bound 49).val)
    (alphabetCode : Td_code_d I A RA (ρ.bound 22).val (ρ.bound 21).val)
    (powerCount : Pc_count_d I Ω A RA (ρ.bound 21).val)
    (supportBelow : Rd_entry_d L (ρ.bound 21).val RA)
    (numbers : Rr_layer_d I Ω A RA (ρ.bound 19).val zA)
    (below : Rd_entry_d (ρ.bound 0).val L RA)
    (small : Rr_small_d I A RA U) (cofinal : Tg_raw_cofinal_d I (ρ.bound 19).val A RA L)
    (common : Ic_common_d I A RA N R L l U V Δ g)
    (roots : Tg_root_square_d D₀ qA q g)
    (upper : Rd_entry_d l χ R ∨ l = χ)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m)
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ q)
    (index : Rd_entry_d m (ι.bound 19).val z)
    (b τ w : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (pair : KPair_d (smdl_structure_l I (R := R) mn.2.1) b τ w)
    (answer : Formula.satisfies
      (⟨fun k => [ι.bound 0,ι.bound 1,ι.bound 2,ι.bound 3,ι.bound 4,ι.bound 5,
        ι.bound 6,ι.bound 7,ι.bound 8,ι.bound 9,ι.bound 10,ι.bound 11,
        ι.bound 19,ι.bound 20,b].get k,ι.free⟩ :
          Env (smdl_structure_l I (R := R) mn.2.1) 15) td_answer0_m)
    (keys : ∀ k : Fin 3, Rd_entry_d (ρ.bound ([25,0,4].get k)).val
      ([ι.bound 23,τ,w].get k).val g)
    (real : ∃ s, Rd_entry_d (ρ.bound 44).val s g ∧
      Td_play_at_d I N R (ι.bound 4).val (ι.bound 2).val (ι.bound 20).val s) :
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let J := kp_pair_l (ZF.modelsKP native)
    ∃ t j : Nn.Domain, ∃ m' Da' r E,
      Fseq_end_d J (ι.bound 0) t (ι.bound 20) b ∧
      Nn.mem j (ι.bound 0) ∧ Nn.SuccessorOf j (ι.bound 46) ∧
      Fn0_d j (ι.bound 12) t ∧ Nn.mem t (ι.bound 18) ∧
      Nn.IsOrdinalDivision J j (ι.bound 4) (ι.bound 19) (ι.bound 3) ∧
      M.mem m' Ω ∧ M.SuccessorOf m' m ∧ M.IsSequenceOfLength I Da' m' ∧
      Rt_tuple_d (Td_archive_row_d.values_d
        ⟨fun k => (ρ.bound k).val,i,cA,A,RA,qA,L,U,zA,d,H,E⟩) r ∧
      (∀ n s, Rd_entry_d n s Da' ↔ Rd_entry_d n s Da ∨ n = m ∧ s = r) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' N R χ
        (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z t.val D₀ q := by
  intro Nn J
  have hN := ZF.modelsKP native
  have data := (td_issued_sat_l J hN.1 ι).mp issued
  obtain ⟨t,j,endt,hj,succ,fn,position,clock,event⟩ :=
    td_issued_answer_history_l native ι issued b answer
  have kept := old.mono_l I mn hN t.property
    (fun x hx hxH => endt.subset_l J (⟨x,hx⟩ : Nn.Domain) hxH)
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,alphabet,letter,_⟩ := seed
  have letter : Rd_entry_d (ρ.bound 49).val (ρ.bound 47).val RA :=
    (Formula.satisfies_mem_iff ..).mp letter
  have alphabet := (td_alphabet_sat_l hA.1 ..).mp alphabet
  obtain ⟨_,E,_,_,enumeration⟩ := alphabetCode.enum_l hZF ma.2.1 hA
    (ρ.bound 22) (ρ.bound 21) (ρ.bound 47) (ρ.bound 48) (ρ.bound 49) powerCount alphabet letter
  let s : Td_archive_row_d M.Domain := ⟨fun k => (ρ.bound k).val,i,cA,A,RA,qA,L,U,zA,d,H,E⟩
  have source : Td_archive_source_d I Ω c₀ X₀ Ar Sr D₀ s :=
    ⟨ma,fromA,(rr_truth_native_l I ma.2.1 td_round0_m td_round0_closed_l ρ.bound).mpr
      ((Formula.closed_env_l td_round0_m td_round0_closed_l (ρ := ρ)
        (η := ⟨ρ.bound,fun _ => ρ.bound 0⟩) rfl).mp round),
      numbers,below,small,cofinal,depth,enumeration,chosen,rootLow,lettersRoot,treeRoot,powerCount,supportBelow,
      alphabetCode⟩
  have trace : Td_trace_d J (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 19) t
      (ι.bound 23) τ w := ⟨ι.bound 21,ι.bound 22,ι.bound 24,ι.bound 25,b,
        data.event.end_l endt,data.payload.1,event,pair⟩
  let η : Env Nn 8 := ⟨fun k => [ι.bound 4,ι.bound 1,ι.bound 2,ι.bound 19,t,ι.bound 23,τ,w].get k,ι.free⟩
  obtain ⟨s',point,play⟩ := real
  have view : Td_archive_view_d I s.v g N R (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z t.val m :=
    ⟨(ι.bound 19).val,(ι.bound 23).val,τ.val,w.val,index,keys 0,keys 1,keys 2,
      (td_trace_native_l I mn.2.1 hN η).mpr trace,s',point,
      play.mono_l I mn hN t.property (fun x hx hy => endt.subset_l J ⟨x,hx⟩ hy)⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) s.values_d
  obtain ⟨m',sm,hm'⟩ := hΩ.1.2 m hm
  obtain ⟨Da',seq,graph⟩ := sequence.exists_append (ZF.modelsKP hZF) I
    (value := r) (hΩ.members_areOrdinals (ZF.modelsKP hZF) m' hm') sm
  refine ⟨t,j,m',Da',r,E,endt,hj,succ,fn,position,clock,hm',sm,seq,tuple,graph,?_⟩
  intro n r' hr
  rcases (graph n r').mp hr with hr | ⟨rfl,rfl⟩
  · exact kept n r' hr
  · exact ⟨s,tuple,source,l,V,Δ,g,common,upper,roots,view⟩

/-- 实数阶段的两种所有权都调用原控制，再自动保持完整档案。 -/
theorem Td_archive_d.digit_l
    {Ω c₀ X₀ Da cN N R χ z D₀ q : M.Domain}
    (mn : Smdl_d I cN N R) (native : (smdl_structure_l I (R := R) mn.2.1).Models ZF)
    (p : Tg_params_d (smdl_structure_l I (R := R) mn.2.1).Domain)
    {X F L G J σ C i n h : (smdl_structure_l I (R := R) mn.2.1).Domain}
    (rules : Td_rules_d native p X F L J)
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP native)) false p.ω p.e X F L G J σ C)
    (hi : (smdl_structure_l I (R := R) mn.2.1).mem i p.ω)
    (hn : (smdl_structure_l I (R := R) mn.2.1).mem n p.ω)
    (hh : (smdl_structure_l I (R := R) mn.2.1).mem h C)
    (fn : Fn0_d i X h) (div : (smdl_structure_l I (R := R) mn.2.1).IsOrdinalDivision
      (kp_pair_l (ZF.modelsKP native)) i p.c n p.b)
    (letters : (smdl_structure_l I (R := R) mn.2.1).MemberSubset p.A X)
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ p.c.val p.e.val p.a.val z h.val D₀ q)
    (x : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (hx : (smdl_structure_l I (R := R) mn.2.1).mem x p.A) :
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let K := kp_pair_l (ZF.modelsKP native)
    ∃ v t j m : Nn.Domain,
      Nn.mem v p.A ∧ (Gm_even_d K p.ω n → v = x) ∧
      (¬ Gm_even_d K p.ω n → Rd_entry_d h v σ) ∧
      Fseq_end_d K p.ω t h v ∧ Nn.mem j p.ω ∧ Nn.mem m p.ω ∧
      Nn.SuccessorOf j i ∧ Nn.SuccessorOf m n ∧ Fn0_d j X t ∧ Nn.mem t C ∧
      Nn.IsOrdinalDivision K j p.c m p.e ∧ Tg_event_d K p.c n p.b t v ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ p.c.val p.e.val p.a.val z t.val D₀ q := by
  intro Nn K
  have choose : ∃ v, Nn.mem v p.A ∧ (Gm_even_d K p.ω n → v = x) ∧
      (¬ Gm_even_d K p.ω n → Rd_entry_d h v σ) ∧ Tg_digit_end_d native p X C i n h v := by
    by_cases even : Gm_even_d K p.ω n
    · exact ⟨x,hx,fun _ => rfl,fun odd => (odd even).elim,
        rules.digit_l native control hi hn hh fn div even hx letters⟩
    · obtain ⟨v,hv,value,ending⟩ := rules.digit_strategy_l native control hi hn hh fn div even
      exact ⟨v,hv,fun he => (even he).elim,fun _ => value,ending⟩
  obtain ⟨v,hv,even,odd,t,j,m,endt,hj,hm,sj,sm,ft,ht,clock,event⟩ := choose
  exact ⟨v,t,j,m,hv,even,odd,endt,hj,hm,sj,sm,ft,ht,clock,event,
    old.mono_l I mn (ZF.modelsKP native) t.property
      (fun x hx hxH => endt.subset_l K (⟨x,hx⟩ : Nn.Domain) hxH)⟩

/-- 同一 II 策略产生下一辅助请求时，全部旧回合仍对应追加后的历史。 -/
theorem Td_archive_d.aux_l
    {Ω c₀ X₀ Da cN N R χ z D₀ q : M.Domain}
    (mn : Smdl_d I cN N R) (native : (smdl_structure_l I (R := R) mn.2.1).Models ZF)
    (p : Tg_params_d (smdl_structure_l I (R := R) mn.2.1).Domain)
    {X F L G J σ C i n h : (smdl_structure_l I (R := R) mn.2.1).Domain}
    (rules : Td_rules_d native p X F L J)
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP native)) false p.ω p.e X F L G J σ C)
    (hi : (smdl_structure_l I (R := R) mn.2.1).mem i p.ω)
    (hn : (smdl_structure_l I (R := R) mn.2.1).mem n p.ω)
    (hh : (smdl_structure_l I (R := R) mn.2.1).mem h C)
    (fn : Fn0_d i X h) (div : (smdl_structure_l I (R := R) mn.2.1).IsOrdinalDivision
      (kp_pair_l (ZF.modelsKP native)) i p.c n p.e)
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ p.c.val p.e.val p.a.val z h.val D₀ q) :
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let K := kp_pair_l (ZF.modelsKP native)
    ∃ a t j : Nn.Domain,
      Nn.mem a X ∧ Rd_entry_d h a σ ∧ Fseq_end_d K p.ω t h a ∧
      Nn.mem j p.ω ∧ Nn.SuccessorOf j i ∧ Fn0_d j X t ∧ Nn.mem t C ∧
      Nn.IsOrdinalDivision K j p.c n p.a ∧ Td_aux_d native p n h a ∧
      Tg_event_d K p.c n p.e t a ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ p.c.val p.e.val p.a.val z t.val D₀ q := by
  intro Nn K
  obtain ⟨a,t,j,ha,value,endt,hj,sj,ft,ht,clock,aux,event⟩ :=
    rules.aux_l native control hi hn hh fn div
  exact ⟨a,t,j,ha,value,endt,hj,sj,ft,ht,clock,aux,event,
    old.mono_l I mn (ZF.modelsKP native) t.property
      (fun x hx hxH => endt.subset_l K (⟨x,hx⟩ : Nn.Domain) hxH)⟩

/-- 非重置指针从完整档案函数实际选中旧行，轮号由完整数字图解码。 -/
theorem Td_archive_d.select_l
    {Ω c₀ X₀ Da m cN N R χ z D₀ q : M.Domain}
    (mn : Smdl_d I cN N R) (native : (smdl_structure_l I (R := R) mn.2.1).Models ZF)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m) (ne : ι.bound 23 ≠ ι.bound 1)
    (numbers : Rr_layer_d I Ω N R (ι.bound 0).val z)
    (sequence : M.IsSequenceOfLength I Da m) (index : Rd_entry_d m (ι.bound 19).val z)
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ q) :
    ∃ n r, M.mem n m ∧ Rd_entry_d n (ι.bound 22).val z ∧ Rd_entry_d n r Da ∧
      Td_archive_entry_d I Ω c₀ X₀ Ar Sr N R χ
        (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val n r D₀ q := by
  have hN := ZF.modelsKP native
  have data := (td_issued_sat_l (kp_pair_l hN) hN.1 ι).mp issued
  have auxiliary := data.auxiliary
  simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_end_sat_l (kp_pair_l hN) hN.1,td_aux_sat_l native] at auxiliary
  obtain ⟨h,_,aux⟩ := auxiliary
  obtain ⟨ℓ,k,κ,u,d,q,n',m',x,s,B,U,Du,Dw,pn,pm,pp,pb,ph,C,V,E,g₀,g₁,g₂,g₃,
    move,_,_,_,_,_,_,_,_,_,_,_,_,fork⟩ := aux
  obtain ⟨el,ek,eκ,eu⟩ := move.unique_l data.payload.1
  subst ℓ k κ u
  have earlier := (fork.resolve_left (fun h => ne h.1)).2.1
  obtain ⟨n,hn,idx⟩ := (numbers.predecessors m (ι.bound 19).val index (ι.bound 22).val).mp earlier
  obtain ⟨r,entry⟩ := (sequence.2.2 (n)).mp hn
  exact ⟨n,r,hn,idx,entry,old n r entry⟩

end YesMetaZFC.SetTheory.LargeCardinal
