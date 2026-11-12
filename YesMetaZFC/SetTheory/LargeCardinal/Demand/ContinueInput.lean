import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity
import YesMetaZFC.SetTheory.LargeCardinal.Demand.NodeProgram
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RealTrace

/-! # 最大序数查询的数值程序

程序的正确性只带 ω、零及自然数码。名字列把末位变量送到程序的零槽；
目标的完整类型负责提供列的合法性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_max_program_d (I : kpair_convention_l.Interpretation M) (ω e z : M.Domain) : Prop :=
  M.mem z ω ∧ ∀ ν X c R f α, V_d I ν X → Smem_d I c X R →
    M.IsSetFunctionFromTo I f ω X → Rd_entry_d e α f →
      (Sc_sat_d I ω c z f ↔ M.SuccessorOf ν α)

def td_max_program0_m : Formula 1 3 := set[3] ⟪
  ⌜(.bound 2 : Term 3)⌝ₛ ∈ ⌜(.bound 0 : Term 3)⌝ₛ ∧
  (∀ ν X c R f α, ⌜v_m kpair_convention_l⌝ₚ(ν,X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c,X,R) →
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f,⌜(.bound 0 : Term 3)⌝ₛ,X) →
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,α,f) →
    (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜(.bound 0 : Term 3)⌝ₛ,c,⌜(.bound 2 : Term 3)⌝ₛ,f) ↔
      ⌜Formula.isSuccessor⌝ₚ(ν,α)))⟫

theorem td_max_program0_closed_l : td_max_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_max_program0_m,Definitional.Formula.FreeClosed]

theorem td_max_program_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 3) : Formula.satisfies ρ td_max_program0_m ↔
      Td_max_program_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) := by
  simp only [td_max_program0_m,Td_max_program_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,v_sat_l I hE,smem_sat_l I,
    Formula.satisfies_isFunctionFromTo_iff I hE,rd_entry0_sat_l hE,
    Formula.satisfies_iff_iff,sc_sat_formula_l I hE,Formula.satisfies_isSuccessor_iff,
    Definitional.Term.eval_weaken]
  rfl

def Td_max_code_d (e l z p : M.Domain) : Prop :=
  ∃ C, KPair_d M p z C ∧ Rd_entry_d e l C

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_max_program_l {ω e : M.Domain} (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) :
    ∃ z, Td_max_program_d I ω e z := by
  obtain ⟨z,_,_,program⟩ := tt_program_l hZF hw (sv_max_m .newest) (by simp -implicitDefEqProofs)
  refine ⟨z,program.natural,fun ν X c R f α rank model fn value => ?_⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨α,fn.output_mem_of_pairMember value⟩⟩
  let a : (rt_model_l X nx).Domain := ⟨α,fn.output_mem_of_pairMember value⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => a,fun _ => a⟩
  let η : Env (smdl_structure_l I (R := R) model.1.2.1) 1 := ⟨ρ.bound,ρ.free⟩
  have read := (program.read c X R f model.1 η fn (fun i x hx => by
    have eq : x = e := num_unique_l hZF.1 hx
      (Fin.cases he (fun j => Fin.elim0 j) i)
    exact eq.symm ▸ value)).trans
      ((smem_formula_l I model nx (sv_max_m .newest) ρ).symm.trans (sv_max_sat_l ρ .newest))
  refine read.trans ⟨sv_max_successor_l hZF rank nx a,fun succ => ?_⟩
  have trans := v_transitive_l I rank
  have oa := (v_ordinal_l I rank).mem succ.predecessor_mem
  refine ⟨rt_ordinal_l trans nx a oa,fun b hb x hx => ?_⟩
  have ob := (rt_ordinal_iff_l trans nx (ZF.modelsKP hZF) b).mp hb
  exact ((succ b.val).mp (ZF.v_ordinal_height_l hZF rank ob b.property)).elim
    (fun lt => oa.transitive b.val lt x.val hx) (fun eq => (eq x.val).mp hx)

theorem Td_max_program_d.query_l {ω e z l n U D p : M.Domain}
    (hw : M.IsOmega ω) (program : Td_max_program_d I ω e z)
    (pool : Tt_pool_d I ω n U D) (hp : M.mem p D)
    (code : Td_max_code_d e l z p) : Tg_max_query_d I ω l n U D p := by
  obtain ⟨C,pair,entry⟩ := code
  obtain ⟨N,F,names,seq,prod⟩ := pool
  obtain ⟨z',hz,C',hC,cp⟩ := (prod p).mp hp
  obtain ⟨ez,eC⟩ := kpair_injective_l M cp pair
  subst z' C'
  obtain ⟨b,hb,column⟩ := (seq C).mp hC
  refine ⟨hp,fun ν X c R r δ T α rank model type last => ?_⟩
  obtain ⟨r₁,assign,fr₁⟩ := tn_assign_exists_l hZF
    (hw.members_areOrdinals (ZF.modelsKP hZF) n type.finite) type.tuple type.point type.constants names
      (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f,fill,ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value : Rd_entry_d e α f := (fill.2 e α).mpr
    ⟨hw.transitive (ZF.modelsKP hZF) b hb e (column.input_mem_of_pairMember entry),
      Or.inl ⟨column.input_mem_of_pairMember entry,(assign.2 e α).mpr ⟨l,entry,Or.inl last⟩⟩⟩
  exact (type.truth p).trans ((and_iff_right hp).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) pair hz hb column.2.1 assign fill).trans
      (program.2 ν X c R f α rank model ff value)))

theorem td_max_query_program_l {ω e l n U D : M.Domain} (hw : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hl : M.mem l n) (pool : Tt_pool_d I ω n U D) :
    ∃ z p, Td_max_program_d I ω e z ∧ Td_max_code_d e l z p ∧ Tg_max_query_d I ω l n U D p := by
  obtain ⟨z,program⟩ := td_max_program_l hZF hw he
  obtain ⟨p,hp,N,C,b,_,_,_,pair,entries⟩ := tt_code_l hZF hw pool program.1
    (fun _ : Fin 1 => e) (fun _ => l) (Fin.cases he (fun i => Fin.elim0 i)) (fun _ => Or.inl hl)
  have code : Td_max_code_d e l z p := ⟨C,pair,entries 0 e he⟩
  exact ⟨z,p,program,code,program.query_l hZF hw pool hp code⟩

theorem td_max_code_image_l (J : kpair_convention_l.Interpretation M) {N R P S Γ t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (hN : (smdl_structure_l J (R := R) nx).Models KP)
    (hP : (smdl_structure_l J (R := S) ny).Models KP)
    (Y : (smdl_structure_l J (R := R) nx).Domain)
    (trans : (smdl_structure_l J (R := R) nx).TransitiveSet Y)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember J x Y.val R)
    (ft : M.IsSetInjectionFromTo J t Γ P)
    (pred : ∀ x E, M.PairMember J x E t → ∀ y,
      M.PairMember J y E S ↔ ∃ a, M.PairMember J a x R ∧ M.PairMember J a y t)
    (ρ : Env (smdl_structure_l J (R := R) nx) 4)
    (η : Env (smdl_structure_l J (R := S) ny) 4)
    (points : ∀ i, M.PairMember J (ρ.bound i).val (η.bound i).val t)
    (code : Td_max_code_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)) :
    Td_max_code_d (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) := by
  obtain ⟨C,pair,entry⟩ := code
  have hp := ((carrier _).mp (ft.1.input_mem_of_pairMember (points 3))).2
  have hC := (pair.mem_l _ trans hp).2
  obtain ⟨c,hc,Cc⟩ := ft.1.2.2 C.val ((carrier _).mpr ⟨C.property,hC⟩)
  let C' : (smdl_structure_l J (R := S) ny).Domain := ⟨c,hc⟩
  let φ : Formula 1 5 := .conj (kpair0_m (.bound 4) (.bound 3) .newest)
    (rd_entry0_m (.bound 1) (.bound 2) .newest)
  have matrix : Formula.satisfies (ρ.push C) φ := by
    simp only [φ,Formula.satisfies_conj_iff,kpair0_sat_l hN.1,rd_entry0_sat_l hN.1]
    exact ⟨pair,entry⟩
  have moved := (rr_graph_delta_l J nx ny ⟨(ρ.bound 3).val,ft.1.input_mem_of_pairMember (points 3)⟩
    (fun x hx => ((carrier x).mp hx).1)
    (fun x y hx hy hxy => (carrier y).mpr ⟨hy,
      trans ⟨x,((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨y,hy⟩ hxy⟩)
    ft pred φ (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed])
    (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)) (ρ.push C) (η.push C')
    (Fin.cases Cc points)).mp matrix
  simp only [φ,Formula.satisfies_conj_iff,kpair0_sat_l hP.1,rd_entry0_sat_l hP.1] at moved
  exact ⟨C',moved⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原四十七槽请求实际生成二十九槽继续输入

旧回答的语言、弹性和事件由已存档轮提供。请求自己的继续规则确定
同一旧回答、节点长度和 exceeds；当前 Q 表提供候选常量域及完整池，
P 表解释原载荷中的程序。全部模型内部有限元数均由原加倍证书核对。
被回指回答的高度成员从原合法历史读取；当前 dcp 定义域和 exceeds
实际推出 max 成员，与原节点查询一起保留给第一后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_continue_input_l
    (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (θ : Env M 10) (language : Formula.satisfies θ ee_language0_m)
    (sameω : θ.bound 0 = ι.bound 0) (w χ : M.Domain)
    (elastic : Ee_elastic_d ⟨θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9⟩ w)
    {a b ℓ j κ u d q n : M.Domain}
    (request : Tg_event_d I (ι.bound 4) (ι.bound 22) (ι.bound 1) (ι.bound 20) a)
    (move : Td_move_d a ℓ j κ u)
    (answer : Tg_event_d I (ι.bound 4) (ι.bound 22) (ι.bound 2) (ι.bound 20) b)
    (pair : KPair_d M b (θ.bound 1) w)
    (arity : Td_arity_d I j d q n (θ.bound 2)) (hχ : M.mem χ (ι.bound 5)) :
    ∃ ρ : Env M 29, Formula.satisfies ρ tc_seed0_m ∧
      (∀ i : Fin 10, ρ.bound ([0,1,3,4,5,6,17,18,19,20].get i) = θ.bound i) ∧
      ρ.bound 7 = w ∧ ρ.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ρ.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get i) =
        ι.bound ([0,5,24,28,25,37,38,39,40,41,42,43,44,45].get i)) ∧
      ρ.bound 28 = χ ∧ M.SuccessorOf (ι.bound 23) j ∧ M.mem (ι.bound 22) (ι.bound 19) ∧
    ∃ s pn pm,
      Td_node_query_d I (ρ.bound 0) (ι.bound 1) (ρ.bound 9) (ι.bound 27)
        (ρ.bound 11) (ρ.bound 12) s (ι.bound 23) pn ∧
      Tg_max_query_d I (ρ.bound 0) (ι.bound 27) (ρ.bound 9) (ρ.bound 11) (ρ.bound 12) pm ∧
      M.mem pn (ρ.bound 13) ∧ M.mem pm (ρ.bound 13) ∧
    ∃ i j z p,
      M.mem (ι.bound 1) (ι.bound 27) ∧ M.mem (ι.bound 27) (ρ.bound 9) ∧
      M.mem i (ρ.bound 0) ∧ M.mem j (ρ.bound 0) ∧
      Td_node_program_d I (ρ.bound 0) (ι.bound 1) (ι.bound 27) i j z ∧
      Td_node_code_d (ρ.bound 9) i j z p s (ι.bound 23) ∧ M.mem p (ρ.bound 13) ∧
    ∃ zm qm, Td_max_program_d I (ρ.bound 0) (ι.bound 1) zm ∧
      Td_max_code_d (ι.bound 1) (ι.bound 27) zm qm ∧ M.mem qm (ρ.bound 13) ∧
    ∃ ψ : Env M 12, Formula.satisfies ψ tg_candidate0_m ∧
      (∀ i : Fin 5, ψ.bound ([0,1,2,3,4].get i) = ρ.bound ([13,9,0,8,3].get i)) ∧
      ψ.bound 6 = ι.bound 31 ∧ ψ.bound 7 = ι.bound 32 ∧ M.mem s (ρ.bound 11) ∧
      Td_play_d I (ι.bound 4) (ι.bound 2) (ι.bound 20) s := by
  have hKP := ZF.modelsKP hZF
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  let p := tg_control_params_d (fun i => ι.bound (i.castAdd 28))
  have rules : Td_rules_d hZF p (ι.bound 12) (ι.bound 13) (ι.bound 14) (ι.bound 16) :=
    (td_rules_sat_l hZF ..).mp control.2.2.1
  have payload := state.payload
  obtain ⟨parsed,hk,hκ,current,_,hq,_,_,limitκ,payloadEE,programRow⟩ := payload
  have auxiliary := state.auxiliary
  simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_end_sat_l I hZF.1,td_aux_sat_l hZF] at auxiliary
  obtain ⟨h,endt,aux⟩ := auxiliary
  change Td_aux_d hZF p (ι.bound 19) h (ι.bound 21) at aux
  obtain ⟨ℓ',k',κ',u',d',q',n',m',x,s,B,U,Du,Dw,pn,pm,pp,pb,ph,C,V,E,g₀,g₁,g₂,g₃,
    parsed',_,_,current',digits,short,queryRequest,queryRow,_,eeData,defined,nodeMember,_,fork⟩ := aux
  obtain ⟨el,ek,eκ,eu⟩ := parsed'.unique_l parsed
  subst ℓ' k' κ' u'
  obtain ⟨ed,eq,en,em⟩ := current'.unique_l hZF current
  subst d' q' n' m'
  have cont := (fork.resolve_left (fun h => ne h.1)).2
  obtain ⟨earlier,a',b',ℓ',j',κ',u',τ,T,d',q',n',m',B₀,V₀,W₀,
    request',move',answer',pair',step,arity',_,rankOld,constantsOld,poolOld,exceeds⟩ := cont
  obtain ⟨hc,_⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three state.time
  have oc := rules.omega.members_areOrdinals hKP (ι.bound 4) hc
  have fh := (fn0_function_l hKP state.history).1
  have ea := (request'.end_l endt).unique_l hZF oc fh request
  subst a'
  obtain ⟨el,ej,eκ,eu⟩ := move'.unique_l move
  subst ℓ' j' κ' u'
  have eb := (answer'.end_l endt).unique_l hZF oc fh answer
  subst b'
  obtain ⟨eτ,eT⟩ := kpair_injective_l M pair' pair
  subst τ T
  obtain ⟨ed,eq,en,em⟩ := arity'.unique_l hZF arity
  subst d' q' n' m'
  have nextArity : θ.bound 2 = ι.bound 27 := arity.next_l hZF rules.omega hk step current
  -- 旧回答的实际秩、常量域和查询池唯一，故 exceeds 使用同一旧类型。
  have lang := language
  simp only [ee_language0_m,Formula.satisfies_conj_iff] at lang
  have rankθ := (v_sigma_sat_l hKP ..).mp lang.2.2.1
  have constantsθ := (tt_constants0_sat_l hZF.1 ..).mp lang.2.2.2.1
  have eB := ZF.v_unique_l I hZF rankOld rankθ
  subst B₀
  have eV := hZF.1.eq_of_same_members V₀ (θ.bound 4)
    (fun x => (constantsOld x).trans (constantsθ x).symm)
  subst V₀
  have domain := lang.1
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,Formula.satisfies_conj_iff] at domain
  have poolθ : Tt_pool_d I (ι.bound 0) (θ.bound 2) (θ.bound 4) (θ.bound 5) :=
    sameω ▸ (tt_pool_sat_l I hKP ..).mp domain.2.1
  have eW := poolOld.unique_l hZF.1 I poolθ
  subst W₀
  obtain ⟨ph₀,heightQuery,heightMember⟩ := td_issued_height_l hZF ι issued
    request move answer pair arity earlier rankθ constantsθ poolθ
  -- 当前完整类型的池从原 Q 行读取；不能误用 q 元弹性池。
  have tables := control.1
  simp only [td_tables_m,Formula.satisfies_conj_iff] at tables
  have functionE := (Formula.satisfies_isFunction_iff I hZF.1 ..).mp tables.2.2.2.1
  have sameEE := eeData.unique_l hZF.1 functionE payloadEE
  have read := tables.1.2.2.2
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    tg_query_request_sat_l hZF,td_query_data_sat_l hZF.1] at read
  have row := read (ι.bound 24) hκ (ι.bound 23) s B U Du Dw pn pm pp pb ph queryRequest queryRow
  simp only [Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,td_arity_sat_l I hZF.1,
    v_sat_l I hZF.1,tt_constants0_sat_l hZF.1,tt_pool_sat_l I hKP,
    td_node_query_sat_l I hKP,tg_max_query_sat_l I hKP] at row
  obtain ⟨d',q',n',m',queryArity,rankCurrent,constantsCurrent,_,_,nodeQuery,maxQuery,_⟩ := row
  change Td_arity_d I (ι.bound 23) d' q' n' m' at queryArity
  obtain ⟨ed,eq,en,em⟩ := queryArity.unique_l hZF current
  subst d' q' n' m'
  have readLanguage := tables.1.1
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isLimitOrdinal_iff,tg_ee_data_sat_l hZF.1] at readLanguage
  have currentLanguage := readLanguage (ι.bound 24) hκ (ι.bound 27) hq C V E g₀ g₁ g₂ g₃ limitκ eeData
  have savedLanguage := currentLanguage
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at currentLanguage
  have currentDomain := (ee_domain_pack_sat_l hZF ..).mp currentLanguage.1
  have base := (v_sigma_sat_l hKP ..).mp currentLanguage.2.2.1
  have constants := (tt_constants0_sat_l hZF.1 ..).mp currentLanguage.2.2.2.1
  have eB : C = B := ZF.v_unique_l I hZF base rankCurrent
  subst C
  have eV : V = U := hZF.1.eq_of_same_members V U
    (fun x => (constants x).trans (constantsCurrent x).symm)
  subst V
  obtain ⟨v,drop,elasticCurrent⟩ := defined
  have maxMember := tg_exceeds_rigid_l hZF rules.omega arity.2.2.2.predecessor_mem
    current.2.2.1 currentDomain heightQuery maxQuery heightMember drop elasticCurrent.1 exceeds
  -- 两条节点码在同一完整实现中比较；新编译不改变原候选。
  have currentReal := exceeds
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,witness⟩ := currentReal
  obtain ⟨Y,c,R,r,_,_,_,rankY,modelY,type,_⟩ := witness
  obtain ⟨B',U',base',constants',hs,_⟩ := queryRequest.2.2
  have eB : B' = B := ZF.v_unique_l I hZF base' rankCurrent
  subst B'
  have eU : U' = U := hZF.1.eq_of_same_members U' U
    (fun x => (constants' x).trans (constantsCurrent x).symm)
  subst U'
  have played : Td_play_d I (ι.bound 4) (ι.bound 2) (ι.bound 20) s := by
    refine ⟨ι.bound 3,rules.two,?_⟩
    intro i y iy
    have value := ((short.2 i y).mp iy).2
    exact ((digits.2 i y (digits.1.bound_l value).1).mp value).end_l endt
  have naturals := tt_constants_finite_l hZF rules.omega hk limitκ rankCurrent constantsCurrent
  have heq := (rules.omega.members_areOrdinals hKP _ hq).empty_mem_of_nonempty hKP
    ⟨ι.bound 26,current.2.1.predecessor_mem⟩ rules.empty
  obtain ⟨is,ik,zn,pc,his,hik,nodeProgram,nodeCode,nodeCanonical⟩ :=
    td_node_query_program_l hZF rules.omega type.finite current.2.2.1.predecessor_mem
      heq type.pool hs naturals.2
  obtain ⟨S,_,root⟩ := type.tuple.2.1 (ι.bound 1) ((current.2.2.1 _).mpr (Or.inl heq))
  have canonicalMember := (nodeCanonical.2 c Y R r _ _ S modelY (v_transitive_l I rankY) type root).mpr
    ((nodeQuery.2 c Y R r _ _ S modelY (v_transitive_l I rankY) type root).mp nodeMember)
  obtain ⟨zm,qm,maxProgram,maxCode,maxCanonical⟩ := td_max_query_program_l hZF
    rules.omega rules.empty current.2.2.1.predecessor_mem type.pool
  obtain ⟨α,_,last⟩ := type.tuple.2.1 (ι.bound 27) current.2.2.1.predecessor_mem
  have canonicalMax := (maxCanonical.2 _ Y c R r _ _ α rankY modelY type last).mpr
    ((maxQuery.2 _ Y c R r _ _ α rankY modelY type last).mp maxMember)
  have programs := tables.1.2.1
  simp only [Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,tg_program_data_sat_l hZF.1,
    Formula.satisfies_exists_iff,ts_program_m,Formula.satisfies_bind] at programs
  obtain ⟨a₀,program⟩ := programs (ι.bound 27) (ι.bound 37) (ι.bound 38) (ι.bound 39) (ι.bound 40)
    (ι.bound 41) (ι.bound 42) (ι.bound 43) (ι.bound 44) (ι.bound 45) programRow
  let ρ : Env M 29 := ⟨fun i =>
    [ι.bound 0,θ.bound 1,ι.bound 5,θ.bound 2,θ.bound 3,θ.bound 4,θ.bound 5,w,
      ι.bound 24,ι.bound 28,B,U,Du,ι.bound 25,ι.bound 37,a₀,ι.bound 38,
      θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9,ι.bound 39,ι.bound 40,ι.bound 41,
      ι.bound 42,ι.bound 43,ι.bound 44,ι.bound 45,χ].get i,ι.free⟩
  have seed : Formula.satisfies ρ tc_seed0_m := by
    simp only [tc_seed0_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
      Formula.satisfies_isLimitOrdinal_iff,Formula.satisfies_mem_iff,v_sigma_sat_l hKP,
      tt_constants0_sat_l hZF.1,ee_elastic_sat_l,tx_exceeds_sat_l hZF]
    refine ⟨rules.omega,?_,?_,queryRequest.1,hκ,rankCurrent,constantsCurrent,elastic,?_,hχ⟩
    · simp only [ts_program_m,Formula.satisfies_bind]
      apply (Formula.closed_env_l ts_program0_m ts_program0_closed_l (ρ := _) (η := _) ?_).mp program
      funext i
      exact Fin.cases rfl (Fin.cases nextArity.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
    · simp only [ee_language_m,Formula.satisfies_bind]
      apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l (ρ := θ) (η := _) ?_).mp language
      funext i
      exact Fin.cases sameω (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (fun j => Fin.elim0 j)))))))))) i
    · exact exceeds
  let ψ : Env M 12 := ⟨fun i =>
    [ι.bound 25,ι.bound 28,ι.bound 0,ι.bound 24,ι.bound 27,B,U,E,g₀,g₁,g₂,g₃].get i,ι.free⟩
  have candidate : Formula.satisfies ψ tg_candidate0_m := by
    simp only [tg_candidate0_m,Formula.satisfies_conj_iff,Formula.satisfies_rename]
    refine ⟨?_,?_⟩
    · exact (Formula.closed_env_l ee_language0_m ee_language0_closed_l (by
        funext i
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
            (fun j => Fin.elim0 j)))))))))) i)).mp
          ((Formula.satisfies_bind ..).mp savedLanguage)
    · exact (tg_elastic_sat_l I hZF.1 ..).mpr ⟨v,drop,elasticCurrent⟩
  refine ⟨ρ,seed,?_,rfl,nextArity,?_,rfl,step,earlier,s,pn,pm,nodeQuery,maxQuery,nodeMember,maxMember,
    is,ik,zn,pc,heq,current.2.2.1.predecessor_mem,his,hik,nodeProgram,nodeCode,canonicalMember,
    zm,qm,maxProgram,maxCode,canonicalMax,ψ,candidate,?_,sameEE.2.1,sameEE.2.2.1,hs,played⟩
  · intro i
    exact Fin.cases sameω.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun j => Fin.elim0 j)))))))))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases nextArity.symm (fun j => Fin.elim0 j))))) i

end YesMetaZFC.SetTheory.LargeCardinal
