import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepareRoot
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ReplyBase
import YesMetaZFC.SetTheory.LargeCardinal.Demand.OldView
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundRecovery

/-! # 同一原表项与 23 槽完整回答装配规则 7.1(6)

请求保留固定 A，查询码只读取已选 Q 行。源 q、N 与目标 m 独立保存，
完整回答真值和七个程序槽逐项进入原回答公式，不重新选择任何表项。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem td_answer_build_l (p : Tg_params_d M.Domain)
    {n h v a ℓ k κ u τ w d q N m B U E C V Du Dw pn pm pp pb ph b z : M.Domain}
    {ee : Ee_queries_d M} {σ : Fin 7 → M.Domain}
    (event : Tg_event_d I p.c n p.e h a) (move : Td_move_d a ℓ k κ u) (pair : KPair_d M v τ w)
    (arity : Td_arity_d I k d q N m)
    (elastic : Tg_ee_data_d p.E κ q B U E ee) (below : M.mem τ p.δ)
    (request : Formula.satisfies (⟨fun i => [p.ω,τ,k,p.e,p.A].get i,fun _ => p.ω⟩ : Env M 5) tg_query_request0_m)
    (query : Td_query_data_d p.Q τ k p.e p.A C V Du Dw pn pm pp pb ph)
    (program : Tg_program_data_d p.P q b z σ)
    (reply : Formula.satisfies (⟨fun i => [p.ω,q,N,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,
      σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i,fun _ => p.ω⟩ : Env M 23) td_reply0_m) :
    Formula.satisfies (⟨fun i => [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,n,h,v].get i,
      fun _ => p.ω⟩ : Env M 15) td_answer0_m := by
  simp only [td_answer0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    tg_event_sat_l I hE,td_move_sat_l hE,kpair0_sat_l hE,td_arity_sat_l I hE,
    tg_ee_data_sat_l hE,Formula.satisfies_mem_iff,tg_query_request_m,
    td_query_data_sat_l hE,tg_program_data_sat_l hE,td_reply_m,
    Formula.satisfies_bind,Definitional.Term.eval_weaken]
  refine ⟨a,ℓ,k,κ,u,τ,w,d,q,N,m,B,U,E,ee.largest,ee.domain,ee.inaccessible,ee.stretch,
    C,V,Du,Dw,pn,pm,pp,pb,ph,b,z,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6,
    event,move,pair,arity,elastic,below,?_,query,program,?_⟩
  · apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))) i
  · apply (Formula.closed_env_l td_reply0_m td_reply0_closed_l (ρ := _) (η := _) ?_).mp reply
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))))))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生 23 槽回答与已发请求的固定表装配

源语言及程序读取请求原载荷；目标池由 Q 行唯一性识别。
三个查询码可以改为原 Q 行的码，回答类型 w 及 subtype 见证保持不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_reply_link_d {α β : Type u} (R : α → β → Prop)
    (v : Fin 47 → α) (w : Fin 23 → β) : Prop :=
  ∀ i : Fin 17, R (v ([0,27,28,29,24,31,32,25,37,38,39,40,41,42,43,44,45].get i))
    (w ([0,1,2,3,4,6,7,9,11,12,16,17,18,19,20,21,22].get i))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从已发请求的同一 Q 表取行；回答池由完整池的唯一性识别。 -/
theorem td_issued_reply_row_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    {τ B V D : M.Domain} (below : M.mem τ (ι.bound 5)) (limit : M.IsLimitOrdinal τ)
    (rank : V_d I τ B) (constants : ∀ x, M.mem x V ↔ M.mem x B ∨ x = τ)
    (letters : M.mem (ι.bound 6) V) (pool : Tt_pool_d I (ι.bound 0) (ι.bound 29) V D) :
    Tg_query_request_d hZF (ι.bound 0) τ (ι.bound 23) (ι.bound 1) (ι.bound 6) ∧
    ∃ Du pn pm pp pb ph,
      Td_query_data_d (ι.bound 11) τ (ι.bound 23) (ι.bound 1) (ι.bound 6) B V Du D pn pm pp pb ph ∧
      Td_reply_base_d I (ι.bound 0) (ι.bound 6) (ι.bound 1) (ι.bound 23)
        (ι.bound 27) (ι.bound 28) (ι.bound 29) pp pb ph := by
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have rules := (td_rules_sat_l hZF ..).mp control.2.2.1
  have emptyω := num_mem_l hZF.1 rules.omega (show Num_d 0 (ι.bound 1) from rules.empty)
  have request : Tg_query_request_d hZF (ι.bound 0) τ (ι.bound 23) (ι.bound 1) (ι.bound 6) :=
    ⟨limit,state.payload.2.1,B,V,rank,constants,
      (tt_constants_finite_l hZF rules.omega emptyω limit rank constants).2,letters⟩
  have tables := control.1
  simp only [td_tables_m,Formula.satisfies_conj_iff] at tables
  have total := tables.2.1
  simp only [td_query_total_m,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,tg_query_request_sat_l hZF,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,rd_quad_sat_l hZF.1,rd_entry0_sat_l hZF.1,
    td_query_packet_sat_l hZF,Definitional.Term.eval_weaken] at total
  obtain ⟨x,row,key,entry,d,q,n,m,B',V',Du,D',pn,pm,pp,pb,ph,t,v,arity,code,codes,tail,
    rank',constants',_,pool',_,_,_,_,_,base⟩ :=
    total τ below (ι.bound 23) (ι.bound 1) request
  have old : Td_arity_d I (ι.bound 23) (ι.bound 26) (ι.bound 27) (ι.bound 28) (ι.bound 29) :=
    state.payload.2.2.2.1
  obtain ⟨rfl,rfl,rfl,rfl⟩ := arity.unique_l hZF old
  have eb := ZF.v_unique_l I hZF rank' rank
  subst B'
  have ev := hZF.1.eq_of_same_members V' V (fun z => (constants' z).trans (constants z).symm)
  subst V'
  have ed := pool'.unique_l hZF.1 I pool
  subst D'
  exact ⟨request,Du,pn,pm,pp,pb,ph,⟨x,row,t,v,key,entry,code,codes,tail⟩,base⟩

/-- 固定行的成员证据替换原三条码，实际构造合法回答对象及完整回答公式。 -/
theorem td_issued_answer_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    (η : Env M 23) (reply : Formula.satisfies η td_reply0_m)
    (links : Td_reply_link_d Eq ι.bound η.bound)
    {B V Du pn pm pp pb ph : M.Domain}
    (below : M.mem (η.bound 5) (ι.bound 5))
    (request : Tg_query_request_d hZF (ι.bound 0) (η.bound 5) (ι.bound 23) (ι.bound 1) (ι.bound 6))
    (row : Td_query_data_d (ι.bound 11) (η.bound 5) (ι.bound 23) (ι.bound 1) (ι.bound 6)
      B V Du (η.bound 8) pn pm pp pb ph)
    (members : M.mem pp (η.bound 10) ∧ M.mem pb (η.bound 10) ∧ M.mem ph (η.bound 10)) :
    ∃ b, KPair_d M b (η.bound 5) (η.bound 10) ∧
      Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 2,ι.bound 3,ι.bound 4,
        ι.bound 5,ι.bound 6,ι.bound 7,ι.bound 8,ι.bound 9,ι.bound 10,ι.bound 11,
        ι.bound 19,ι.bound 20,b].get i,ι.free⟩ : Env M 15) td_answer0_m := by
  have hKP := ZF.modelsKP hZF
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  obtain ⟨move,_,_,arity,_,_,_,_,_,ee,program⟩ := state.payload
  let σ : Fin 7 → M.Domain := Fin.cases (ι.bound 39) (Fin.cases (ι.bound 40)
    (Fin.cases (ι.bound 41) (Fin.cases (ι.bound 42) (Fin.cases (ι.bound 43)
      (Fin.cases (ι.bound 44) (fun _ => ι.bound 45))))))
  have slot : (Fin.cases (η.bound 16) (Fin.cases (η.bound 17) (Fin.cases (η.bound 18)
      (Fin.cases (η.bound 19) (Fin.cases (η.bound 20) (Fin.cases (η.bound 21) (fun _ => η.bound 22))))))) = σ := by
    funext i
    exact Fin.cases (links 10).symm (Fin.cases (links 11).symm (Fin.cases (links 12).symm
      (Fin.cases (links 13).symm (Fin.cases (links 14).symm
        (Fin.cases (links 15).symm (Fin.cases (links 16).symm (fun j => Fin.elim0 j))))))) i
  have data := reply
  simp only [td_reply0_m,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff,td_dcp_sat_l I hZF.1,ts_subtype_sat_l hKP,
    Formula.satisfies_mem_iff,Definitional.Term.eval_weaken,tt_eval_cases_l] at data
  have aligned : Td_reply_d I (ι.bound 0) (ι.bound 27) (ι.bound 28) (ι.bound 29) (ι.bound 24)
      (η.bound 5) (ι.bound 31) (ι.bound 32) (η.bound 8) (ι.bound 25) (η.bound 10)
      (ι.bound 37) (ι.bound 38) (η.bound 13) (η.bound 14) (η.bound 15) σ := by
    change Td_reply_d I (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4)
      (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) (η.bound 9) (η.bound 10)
      (η.bound 11) (η.bound 12) (η.bound 13) (η.bound 14) (η.bound 15) _ at data
    exact (links 0).symm ▸ (links 1).symm ▸ (links 2).symm ▸ (links 3).symm ▸
      (links 4).symm ▸ (links 5).symm ▸ (links 6).symm ▸ (links 7).symm ▸
      (links 8).symm ▸ (links 9).symm ▸ slot ▸ data
  obtain ⟨sub,v,drop,subtype,_⟩ := aligned
  obtain ⟨b,pair⟩ := (I).total (η.bound 5) (η.bound 10)
  have answer : Td_answer_d hZF (tg_control_params_d (fun i => ι.bound (i.castAdd 28)))
      (ι.bound 19) (ι.bound 20) b :=
    ⟨ι.bound 21,ι.bound 22,ι.bound 23,ι.bound 24,ι.bound 25,η.bound 5,η.bound 10,
      ι.bound 26,ι.bound 27,ι.bound 28,ι.bound 29,ι.bound 30,ι.bound 31,ι.bound 32,
      ι.bound 33,ι.bound 34,ι.bound 35,ι.bound 36,B,V,Du,η.bound 8,pn,pm,pp,pb,ph,
      ι.bound 37,ι.bound 38,ι.bound 39,ι.bound 40,ι.bound 41,ι.bound 42,ι.bound 43,ι.bound 44,ι.bound 45,
      state.event,move,pair,arity,ee,below,request,row,program,sub,v,drop,subtype,members⟩
  refine ⟨b,pair,?_⟩
  let ρ : Env M 15 := ⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 2,ι.bound 3,ι.bound 4,
    ι.bound 5,ι.bound 6,ι.bound 7,ι.bound 8,ι.bound 9,ι.bound 10,ι.bound 11,
    ι.bound 19,ι.bound 20,b].get i,ι.free⟩
  have result := (td_answer_sat_l hZF ρ
    ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,
      .bound 8,.bound 9,.bound 10,.bound 11⟩ (.bound 12) (.bound 13) (.bound 14)).mpr answer
  exact (Formula.closed_env_l td_answer0_m td_answer0_closed_l (by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))) i)).mp ((Formula.satisfies_bind ..).mp result)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定 Q 行的三条码进入同一个原回答

目标查询的小基底先给出共同根中的秩界。其完整语义沿共同根回到原轮，
扩大到原轮查询池后调用完整实现的比较定理，最后只沿同一个池图搬运成员。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_reply_members_l
    {Ω c₀ X₀ R₀ c X R d Y S j k Γ g γ₀ D₀ C₀ C γ K z D t : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Smdl_d I c₀ X₀ R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (zx : (smdl_structure_l I (R := R) mx.2.1).Models ZF)
    (zy : (smdl_structure_l I (R := S) my.2.1).Models ZF)
    (left : Smap_d I Ω c₀ c X₀ X j) (right : Smap_d I Ω c₀ d X₀ Y k)
    (target : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ Y S C k γ K z)
    (square : Tg_root_square_d D₀ j k g)
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 62)
    (round : Formula.satisfies ρ td_round0_m)
    (θ : Env (smdl_structure_l I (R := S) my.2.1) 10)
    (omega : (smdl_structure_l I (R := S) my.2.1).IsOmega (θ.bound 0))
    (finite : (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 6) (θ.bound 0))
    (low : ∀ i : Fin 7, Rd_entry_d (θ.bound (i.castAdd 3)).val K S)
    (base : Td_reply_base_d (kp_pair_l (ZF.modelsKP zy))
      (θ.bound 0) (θ.bound 1) (θ.bound 2) (θ.bound 3) (θ.bound 4) (θ.bound 5)
      (θ.bound 6) (θ.bound 7) (θ.bound 8) (θ.bound 9))
    (ft : M.IsSetInjectionFromTo I t D Y) (restrict : M.IsRestrictionOf I g t Γ)
    (pred : ∀ x y, Rd_entry_d x y t → ∀ a,
      Rd_entry_d a y S ↔ ∃ b, Rd_entry_d b x R ∧ Rd_entry_d b a t)
    (points : ∀ i : Fin 7, Rd_entry_d (ρ.bound ([19,50,20,25,27,28,9].get i)).val
      (θ.bound (i.castAdd 3)).val t)
    (w : (smdl_structure_l I (R := S) my.2.1).Domain)
    (iw : Rd_entry_d (ρ.bound 4).val w.val t) :
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 7) w ∧
      (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 8) w ∧
      (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 9) w := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  have hX := ZF.modelsKP zx
  have hY := ZF.modelsKP zy
  have rank := (rr_rank_native_l I my.2.1 hY
    ⟨γ,target.rank.1⟩ ⟨K,target.rank.2.1⟩).mp target.rank
  have limit : Yn.IsLimitOrdinal ⟨γ,target.rank.1⟩ :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp
      ((rr_truth_native_l I my.2.1 (Formula.isLimitOrdinal .newest)
        (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨γ,target.rank.1⟩)).mp target.limit)
  obtain ⟨hp,hb,hh⟩ := base.rank_l zy omega rank limit (low 0) (low 1) (low 3) finite
  have all : ∀ i, Rd_entry_d (θ.bound i).val K S :=
    Fin.cases (low 0) (Fin.cases (low 1) (Fin.cases (low 2) (Fin.cases (low 3)
      (Fin.cases (low 4) (Fin.cases (low 5) (Fin.cases (low 6)
        (Fin.cases hp (Fin.cases hb (Fin.cases hh (fun i => Fin.elim0 i))))))))))
  let φ : Formula 1 10 := td_reply_base_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
  obtain ⟨ψ,images,truth⟩ := target.model_back_l hZF square hΩ root mx my left right
    φ (by simp -implicitDefEqProofs [φ]) θ all
      ((td_reply_base_sat_l (kp_pair_l hY) hY ..).mpr base)
  have same (i : Fin 7) : ψ.bound (i.castAdd 3) = ρ.bound ([19,50,20,25,27,28,9].get i) :=
    Subtype.ext (ft.2 _ _ _ ((restrict.2 _ _).mp (images (i.castAdd 3))).2 (points i))
  have pulled := (td_reply_base_sat_l (kp_pair_l hX) hX ψ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)
    (.bound 7) (.bound 8) (.bound 9)).mp truth
  change Td_reply_base_d (kp_pair_l hX) (ψ.bound 0) (ψ.bound 1) (ψ.bound 2) (ψ.bound 3)
    (ψ.bound 4) (ψ.bound 5) (ψ.bound 6) (ψ.bound 7) (ψ.bound 8) (ψ.bound 9) at pulled
  have pulled : Td_reply_base_d (kp_pair_l hX) (ρ.bound 19) (ρ.bound 50) (ρ.bound 20)
      (ρ.bound 25) (ρ.bound 27) (ρ.bound 28) (ρ.bound 9) (ψ.bound 7) (ψ.bound 8) (ψ.bound 9) :=
    (show ψ.bound 0 = ρ.bound 19 from same 0) ▸ (show ψ.bound 1 = ρ.bound 50 from same 1) ▸
      (show ψ.bound 2 = ρ.bound 20 from same 2) ▸ (show ψ.bound 3 = ρ.bound 25 from same 3) ▸
      (show ψ.bound 4 = ρ.bound 27 from same 4) ▸ (show ψ.bound 5 = ρ.bound 28 from same 5) ▸
      (show ψ.bound 6 = ρ.bound 9 from same 6) ▸ pulled
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  have hw : Xn.IsOmega (ρ.bound 19) := (Formula.satisfies_isOmega_iff ..).mp seed.1
  have data := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at data
  obtain ⟨_,_,_,_,_,_,language,real,_,_,_,_,letters,request,_⟩ := data
  have real := (tt_realized_sat_l (kp_pair_l hX) hX ..).mp real
  have letters : Xn.mem (ρ.bound 50) (ρ.bound 2) := (Formula.satisfies_mem_iff ..).mp letters
  have request := (tg_query_request_sat_l zx ..).mp request
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have lim := (Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1
  have rank₀ := (v_sigma_sat_l hX ..).mp language.2.2.1
  have constants := (tt_constants0_sat_l hX.1 ..).mp language.2.2.2.1
  have naturals := tt_constants_finite_l zx hw request.2.1 lim rank₀ constants
  obtain ⟨pq,bq,hq⟩ := pulled.scope_l (kp_pair_l hX) hX real.pool naturals.1 letters naturals.2
  have compared := (Formula.satisfies_forallClosure_iff ρ.free _).mp
    (td_reply_compare_true_l zx ρ.free) ρ.bound
  have compared := (Formula.satisfies_imp_iff ..).mp compared round
  simp only [td_reply_compare0_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    td_pending_query_sat_l (kp_pair_l hX) hX,tg_bound_query_sat_l (kp_pair_l hX) hX,
    tg_height_query_sat_l (kp_pair_l hX) hX,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken] at compared
  have members := compared (ψ.bound 7) (ψ.bound 8) (ψ.bound 9) pq bq hq
  have carry (i : Fin 10) (hi : Xn.mem (ψ.bound i) (ρ.bound 4)) : Yn.mem (θ.bound i) w :=
    (pred _ _ iw _).mpr ⟨_,hi,((restrict.2 _ _).mp (images i)).2⟩
  exact ⟨carry 7 members.1,carry 8 members.2.1,carry 9 members.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定后继中的固定 Q 行与合法回答

原轮语言沿同一共同层产生目标常量域和回答池；完整池图将它们识别为
23 槽中的原对象。目标 Q 行只读取一次，其三条码回到原轮核验，再装配
合法回答，并返回登记原轮所需的三个共同图坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.demand_answer_l
    {Ω c₀ X₀ R₀ c X R d Y S j k L l U V Γ g D t wr zr zx zy γ₀ D₀ C₀ C γ K z : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ g)
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (left : Smap_d I Ω c₀ c X₀ X j) (right : Smap_d I Ω c₀ d X₀ Y k)
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 62)
    (round : Formula.satisfies ρ td_round0_m)
    (ι : Env (smdl_structure_l I (R := S) my.2.1) 47) (issued : Formula.satisfies ι td_issued0_m)
    (η : Env (smdl_structure_l I (R := S) my.2.1) 23) (reply : Formula.satisfies η td_reply0_m)
    (links : Td_reply_link_d Eq ι.bound η.bound)
    (sourceNumbers : Rr_layer_d I Ω X R (ρ.bound 19).val zx)
    (targetNumbers : Rr_layer_d I Ω Y S (ι.bound 0).val zy)
    (below : Rd_entry_d (ρ.bound 0).val L R)
    (ft : M.IsSetInjectionFromTo I t D Y) (restrict : M.IsRestrictionOf I g t Γ)
    (pred : ∀ x y, Rd_entry_d x y t → ∀ a,
      Rd_entry_d a y S ↔ ∃ b, Rd_entry_d b x R ∧ Rd_entry_d b a t)
    (points : ∀ i : Fin 5, Rd_entry_d (ρ.bound ([19,0,9,3,4].get i)).val
      (η.bound ([0,5,3,8,10].get i)).val t)
    (names : ∀ i : Fin 3, Rd_entry_d (ρ.bound ([20,25,50].get i)).val
      (ι.bound ([1,23,6].get i)).val t)
    (cap : ∀ x, Rd_entry_d x l S → Rd_entry_d x (η.bound 4).val S)
    (target : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ Y S C k γ K z)
    (square : Tg_root_square_d D₀ j k g)
    (omegaLow : Rd_entry_d (ι.bound 0).val K S) (lettersLow : Rd_entry_d (ι.bound 6).val K S) :
    ∃ b : (smdl_structure_l I (R := S) my.2.1).Domain,
      KPair_d (smdl_structure_l I (R := S) my.2.1) b (η.bound 5) (η.bound 10) ∧
      Formula.satisfies (⟨fun i => [ι.bound 0,ι.bound 1,ι.bound 2,ι.bound 3,ι.bound 4,
        ι.bound 5,ι.bound 6,ι.bound 7,ι.bound 8,ι.bound 9,ι.bound 10,ι.bound 11,
        ι.bound 19,ι.bound 20,b].get i,ι.free⟩ :
          Env (smdl_structure_l I (R := S) my.2.1) 15) td_answer0_m ∧
      (∀ i : Fin 3, Rd_entry_d (ρ.bound ([25,0,4].get i)).val
        ([ι.bound 23,η.bound 5,η.bound 10].get i).val g) := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  have groundX := (root.map_l hZF hΩ mx left).native_l I hZF hΩ
  have groundY := (root.map_l hZF hΩ my right).native_l I hZF hΩ
  have nativeX := ZFC.models_zf_l groundX
  have nativeY := ZFC.models_zf_l groundY
  have hX := ZF.modelsKP nativeX
  have hY := ZF.modelsKP nativeY
  have rank := (rr_rank_native_l I my.2.1 hY
    ⟨γ,target.rank.1⟩ ⟨K,target.rank.2.1⟩).mp target.rank
  obtain ⟨θ,w,a,d₀,q₀,n₀,language,_,_,arity,view⟩ := common.demand_view_l hZF hΩ root.model mx my
    nativeX groundY left right root.ext rootNumbers ρ round sourceNumbers targetNumbers below
  have atPool i := ((restrict.2 _ _).mp (view i)).2
  have ew : θ.bound 0 = ι.bound 0 :=
    (Subtype.ext (ft.1.1.2 _ _ _ (atPool 0) (points 0))).trans (links 0).symm
  have et : θ.bound 1 = η.bound 5 := Subtype.ext (ft.1.1.2 _ _ _ (atPool 1) (points 1))
  have em : θ.bound 2 = η.bound 3 := Subtype.ext (ft.1.1.2 _ _ _ (atPool 2) (points 2))
  have ep : θ.bound 5 = η.bound 8 := Subtype.ext (ft.1.1.2 _ _ _ (atPool 5) (points 3))
  have ek : a = ι.bound 23 := Subtype.ext (ft.1.1.2 _ _ _ (atPool 11) (names 1))
  have eu : w = η.bound 10 := Subtype.ext (ft.1.1.2 _ _ _ (atPool 10) (points 4))
  have state := (td_issued_sat_l (kp_pair_l hY) nativeY.1 ι).mp issued
  have actualArity : Td_arity_d (kp_pair_l hY) (ι.bound 23)
      (ι.bound 26) (ι.bound 27) (ι.bound 28) (ι.bound 29) := state.payload.2.2.2.1
  have alignedArity : Td_arity_d (kp_pair_l hY) (ι.bound 23) d₀ q₀ n₀ (θ.bound 2) := ek ▸ arity
  obtain ⟨_,eq,en,em'⟩ := alignedArity.unique_l nativeY actualArity
  have language := (ee_language0_sat_l groundY θ).mp language
  have omega : Yn.IsOmega (ι.bound 0) := targetNumbers.omega_l I (ZF.modelsKP hZF) hΩ nativeY.1
  have lim : Yn.IsLimitOrdinal (η.bound 5) := et ▸ language.limit
  have fullRank : V_d (kp_pair_l hY) (η.bound 5) (θ.bound 3) := et ▸ language.rank
  have constants : ∀ x, Yn.mem x (θ.bound 4) ↔ Yn.mem x (θ.bound 3) ∨ x = η.bound 5 :=
    et ▸ language.constants
  have pool : Tt_pool_d (kp_pair_l hY) (ι.bound 0) (ι.bound 29) (θ.bound 4) (η.bound 8) :=
    ew ▸ em' ▸ ep ▸ language.pool
  have rankU := (rr_rank_native_l I mx.2.1 hX ⟨L,common.left_rank.1⟩
    ⟨U,common.left_rank.2.1⟩).mp common.left_rank
  obtain ⟨rankA,hA⟩ := td_round_letters_l nativeX ρ round
  have hAU := (v_transitive_l (kp_pair_l hX) rankU)
    _ (ZF.v_mem_l (kp_pair_l hX) nativeX rankA rankU below) _ hA
  have pointA := (restrict.2 _ _).mpr ⟨(common.carrier _).mpr ⟨(ρ.bound 50).property,hAU⟩,names 2⟩
  have letters : Yn.mem (ι.bound 6) (θ.bound 4) := (constants _).mpr (Or.inl
    ((common.pred _ _ (view 3) _).mpr ⟨_,hA,pointA⟩))
  let lp : Yn.Domain := ⟨l,common.right_rank.1⟩
  have rankV := (rr_rank_native_l I my.2.1 hY lp ⟨V,common.right_rank.2.1⟩).mp common.right_rank
  have hτV : Yn.mem (η.bound 5) ⟨V,common.right_rank.2.1⟩ := by
    have image : Yn.mem (θ.bound 1) ⟨V,common.right_rank.2.1⟩ :=
      (common.image _).mpr ⟨_,common.injection.1.input_mem_of_pairMember (view 1),view 1⟩
    exact et ▸ image
  have hτl := KP.v_ordinal_height_l hY rankV lim.1 hτV
  have hτκ : Yn.mem (η.bound 5) (ι.bound 24) := (links 4).symm ▸ cap (η.bound 5).val hτl
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have geometry := control.2.2.2.2.2.2.2.2.2
  simp only [td_geometry_m,Formula.satisfies_conj_iff] at geometry
  have woodin := (woodin_sat_l (kp_pair_l hY) nativeY.1 ..).mp geometry.1
  obtain ⟨_,_,_,_,regular,_⟩ := woodin
  have hτδ := regular.isLimitOrdinal.1.transitive (ι.bound 24) state.payload.2.2.1 _ hτκ
  obtain ⟨request,Du,pn,pm,pp,pb,ph,row,base⟩ :=
    td_issued_reply_row_l nativeY ι issued hτδ lim fullRank constants letters pool
  let ψ : Env Yn 10 := ⟨fun i =>
    [ι.bound 0,ι.bound 6,ι.bound 1,ι.bound 23,ι.bound 27,ι.bound 28,ι.bound 29,pp,pb,ph].get i,ι.free⟩
  have rules := (td_rules_sat_l nativeY ..).mp control.2.2.1
  have he := num_mem_l nativeY.1 omega (show Num_d 0 (ι.bound 1) from rules.empty)
  have finite : ∀ i : Fin 5, Yn.mem (ι.bound ([1,23,27,28,29].get i)) (ι.bound 0) :=
    Fin.cases he (Fin.cases state.payload.2.1 (Fin.cases state.payload.2.2.2.2.2.1
      (Fin.cases state.payload.2.2.2.2.2.2.1 (Fin.cases state.payload.2.2.2.2.2.2.2.1
        (fun i => Fin.elim0 i)))))
  have low : ∀ i : Fin 7, Rd_entry_d (ψ.bound (i.castAdd 3)).val K S :=
    Fin.cases omegaLow (Fin.cases lettersLow (Fin.cases
      ((v_transitive_l (kp_pair_l hY) rank) _ omegaLow _ (finite 0)) (Fin.cases
        ((v_transitive_l (kp_pair_l hY) rank) _ omegaLow _ (finite 1)) (Fin.cases
          ((v_transitive_l (kp_pair_l hY) rank) _ omegaLow _ (finite 2)) (Fin.cases
            ((v_transitive_l (kp_pair_l hY) rank) _ omegaLow _ (finite 3)) (Fin.cases
              ((v_transitive_l (kp_pair_l hY) rank) _ omegaLow _ (finite 4)) (fun i => Fin.elim0 i)))))))
  have parameters : ∀ i : Fin 7, Rd_entry_d (ρ.bound ([19,50,20,25,27,28,9].get i)).val
      (ψ.bound (i.castAdd 3)).val t :=
    Fin.cases ((congrArg Subtype.val (links 0)).symm ▸ points 0) (Fin.cases (names 2)
      (Fin.cases (names 0) (Fin.cases (names 1) (Fin.cases (congrArg Subtype.val eq ▸ atPool 13)
        (Fin.cases (congrArg Subtype.val en ▸ atPool 14)
          (Fin.cases (congrArg Subtype.val em' ▸ atPool 2) (fun i => Fin.elim0 i)))))))
  have members := td_reply_members_l hZF hΩ root.model mx my nativeX nativeY left right
    target square ρ round ψ omega (finite 4) low base ft restrict pred parameters (η.bound 10) (points 4)
  obtain ⟨b,pair,answer⟩ := td_issued_answer_l nativeY ι issued η reply links hτδ request row members
  exact ⟨b,pair,answer,Fin.cases (congrArg Subtype.val ek ▸ view 11)
    (Fin.cases (congrArg Subtype.val et ▸ view 1) (Fin.cases (congrArg Subtype.val eu ▸ view 10)
      (fun i => Fin.elim0 i)))⟩

end YesMetaZFC.SetTheory.LargeCardinal
