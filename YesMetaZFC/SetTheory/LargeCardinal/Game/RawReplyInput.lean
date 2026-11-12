import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReplyTransport
import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype

/-! # 同图完整回答进入实际目标请求层

原请求只沿实际前驱嵌入搬运。回答的所属模型可以是另一个原模型；
两者由已经生产的十六项同图对应识别。目标查询表由原控制核读取，
它的完整域再经同一个代表池与源回答域核对，不假设任何目标表真值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两种原后继共用同一个目标 issued、reply 和表域生产核。 -/
theorem Tg_raw_reply_transport_d.input_l
    {Ω c X R d Y S b Z T j g t L l U V Γ Dp wx ηx C wy ηy D : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (mt : Smdl_d I b Z T)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (sourceZF : (smdl_structure_l I (R := S) my.2.1).Models ZF)
    (targetZF : (smdl_structure_l I (R := T) mt.2.1).Models ZF)
    (cx : Tg_context_d I wx X R ηx C) (cy : Tg_context_d I wy Y S ηy D)
    (embed : Smap_d I Ω c b X Z j)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,cx.member⟩})
    (nd : Nonempty {y : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem y ⟨D,cy.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) ⟨C,cx.member⟩ nc) 46)
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) ⟨D,cy.member⟩ nd) 54)
    (issued : Formula.satisfies ι tg_issued0_m) (round : Formula.satisfies ρ tg_round0_m)
    (hw : (ι.bound 0).val.val = wx) (hwρ : (ρ.bound 16).val.val = wy)
    (omega : (smdl_structure_l I (R := S) my.2.1).IsOmega ⟨wy,cy.omega_mem⟩)
    (κ' A' D' u' Bp : (smdl_structure_l I (R := S) my.2.1).Domain)
    (common : Ic_common_d I Y S Z T L l U V Γ g)
    (transB : (smdl_structure_l I (R := S) my.2.1).TransitiveSet Bp)
    (carrier : ∀ y, M.mem y Dp ↔ M.mem y Y ∧ Rd_entry_d y Bp.val S)
    (pool : M.IsSetInjectionFromTo I t Dp Z) (restrict : M.IsRestrictionOf I g t Γ)
    (endpoint : Rd_entry_d L l t) (layer : Rd_entry_d U V t)
    (pred : ∀ y z, Rd_entry_d y z t → ∀ a, Rd_entry_d a z T ↔ ∃ x, Rd_entry_d x y S ∧ Rd_entry_d x a t)
    (hτL : Rd_entry_d (ρ.bound 15).val.val L S)
    (hQU : Rd_entry_d (ρ.bound 12).val.val U S) (huU : Rd_entry_d (ρ.bound 11).val.val U S)
    (ε : Env (smdl_structure_l I (R := T) mt.2.1) 22)
    (transport : Tg_raw_reply_transport_d I Ω Z T j g t l mt.2.1
      (fun i => (ρ.bound i).val.val) (fun i => (ι.bound i).val.val)
      (fun i => (tg_round_reply_values_d (fun j => (ρ.bound j).val) ⟨wy,cy.omega_mem⟩ κ' A' D' u' i).val) ε) :
    ∃ η' C', Rd_entry_d wx (ε.bound 0).val j ∧ Rd_entry_d ηx η' j ∧ Rd_entry_d C C' j ∧
    ∃ current : Tg_context_d I (ε.bound 0).val Z T η' C',
    ∃ ne : Nonempty {z : (smdl_structure_l I (R := T) mt.2.1).Domain //
      (smdl_structure_l I (R := T) mt.2.1).mem z ⟨C',current.member⟩},
    ∃ ι' : Env (rt_model_l (M := smdl_structure_l I (R := T) mt.2.1) ⟨C',current.member⟩ ne) 46,
    ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := T) mt.2.1) ⟨C',current.member⟩ ne) 22,
      (∀ i, Rd_entry_d (ι.bound i).val.val (ι'.bound i).val.val j) ∧
      Formula.satisfies ι' tg_issued0_m ∧ (ι'.bound 0).val.val = (ε.bound 0).val ∧
      Rr_truth_d I Z T (KP.ord0_m .newest) (fun _ : Fin 1 => (ι'.bound 24).val.val) ∧
      (∀ x, Rd_entry_d x l T → Rd_entry_d x (ι'.bound 24).val.val T) ∧
      Rd_entry_d l (ι'.bound 5).val.val T ∧ Rd_entry_d l C' T ∧
      Rr_truth_d I Z T (Formula.isRegularCardinal kpair_convention_l .newest)
        (fun _ : Fin 1 => (ι'.bound 5).val.val) ∧
      (∀ i, (θ.bound i).val = ε.bound i) ∧ Formula.satisfies θ tg_reply0_m ∧ Tg_reply_link_d Eq ι'.bound θ.bound ∧
      Rd_entry_d (ρ.bound 41).val.val (ι'.bound 23).val.val g ∧
      Rd_entry_d (ρ.bound 15).val.val (θ.bound 4).val.val g ∧
      Rd_entry_d (ρ.bound 11).val.val (θ.bound 9).val.val g ∧
      Rd_entry_d (θ.bound 1).val.val (ε.bound 0).val T ∧
      Rd_entry_d (ι'.bound 28).val.val (ε.bound 0).val T ∧
      (∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
        (ι'.bound ([0,1,27,28].get i)).val.val t) ∧
      Rd_entry_d (θ.bound 4).val.val (ι'.bound 5).val.val T ∧
      Formula.satisfies (⟨fun i => [ι'.bound 0,θ.bound 4,ι'.bound 26,ι'.bound 1,ι'.bound 1].get i,
        ι'.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := T) mt.2.1) ⟨C',current.member⟩ ne) 5)
        tg_query_request0_m ∧
    ∃ Aq Uq Dq rq mq bq hq qq,
      Dq = θ.bound 7 ∧ Tg_query_data_d (ι'.bound 11) (θ.bound 4) (ι'.bound 26)
        (ι'.bound 1) (ι'.bound 1) Aq Uq Dq rq mq bq hq qq ∧
      Formula.satisfies (⟨fun i => [ι'.bound 0,ι'.bound 1,ι'.bound 27,ι'.bound 28,θ.bound 4,Aq,Uq,Dq,rq,bq,hq].get i,
        ι'.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := T) mt.2.1) ⟨C',current.member⟩ ne) 11)
        tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ι'.bound 0,ι'.bound 1,ι'.bound 27,ι'.bound 28,ι'.bound 26,
        ι'.bound 1,ι'.bound 1,rq,mq,bq,hq,qq].get i,ι'.free⟩ :
        Env (rt_model_l (M := smdl_structure_l I (R := T) mt.2.1) ⟨C',current.member⟩ ne) 12)
        tg_query_row0_m := by
  let Yn := smdl_structure_l I (R := S) my.2.1
  let Zn := smdl_structure_l I (R := T) mt.2.1
  have hY := ZF.modelsKP sourceZF
  have hZ := ZF.modelsKP targetZF
  have fx := cx.finite_l mx.2.1 hX.1
  have fy := cy.finite_l my.2.1 hY.1
  have iw : Rd_entry_d wx (ε.bound 0).val j := hw ▸ transport.links 0
  obtain ⟨η',C',iη,iC,current⟩ := cx.map_l hZF hΩ mx mt embed iw
  let Cp : Zn.Domain := ⟨C',current.member⟩
  let ηp : Zn.Domain := ⟨η',current.height⟩
  have fz := current.finite_l mt.2.1 hZ.1
  let ne : Nonempty {z : Zn.Domain // Zn.mem z Cp} := ⟨⟨ε.bound 0,fz.omega_mem⟩⟩
  obtain ⟨r,record,tuple⟩ := rf_record_save_l I mx.2.1 hX.1 tg_issued0_m tg_issued0_closed_l
    ⟨C,cx.member⟩ fx.transitive fx.pair nc ι issued
  obtain ⟨_,ι',_,points,_,_,issued'⟩ := embed.record_image_l I hZF hΩ mx mt hZ.1 Cp iC fz.transitive ne
    tg_issued0_m tg_issued0_closed_l record tuple
  have rankC := (rr_rank_native_l I mt.2.1 hZ ηp Cp).mp ((rr_rank_truth_l I).mpr current.rank)
  have limitC : Zn.IsLimitOrdinal ηp := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mt.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηp)).mp current.limit)
  obtain ⟨boundδ,regularδ⟩ := tg_issued_control_l hZ rankC limitC fz ne ι' issued'
  have equal : Tg_reply_link_d Eq (fun i => (ι'.bound i).val) ε.bound :=
    fun i => Subtype.ext (embed.1.1.1.2 _ _ _ (points _) (transport.links i))
  have eqω : (ι'.bound 0).val.val = (ε.bound 0).val := congrArg Subtype.val (equal 0)
  let lp : Zn.Domain := ⟨l,common.right_rank.1⟩
  let Vp : Zn.Domain := ⟨V,common.right_rank.2.1⟩
  have rv := (rr_rank_native_l I mt.2.1 hZ lp Vp).mp common.right_rank
  have cap (x : Zn.Domain) (hx : Zn.mem x lp) : Zn.mem x (ι'.bound 24).val :=
    Eq.mpr (congrArg (fun a : Zn.Domain => Zn.mem x a) (equal 3)) (transport.bound x.val hx)
  have belowδ : Zn.mem lp (ι'.bound 5).val := ordinal_down_l hZ
    (v_ordinal_l (kp_pair_l hZ) rv) regularδ.isCardinal.1 cap boundδ
  have member : Zn.mem lp Cp := fz.transitive (ι'.bound 5).val (ι'.bound 5).property lp belowδ
  have ordinal : Rr_truth_d I Z T (KP.ord0_m .newest) (fun _ : Fin 1 => (ι'.bound 24).val.val) :=
    (rr_truth_native_l I mt.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (ι'.bound 24).val)).mpr
        ((KP.ord0_sat_l hZ _ .newest).mpr (regularδ.isCardinal.1.mem boundδ))
  have regular : Rr_truth_d I Z T (Formula.isRegularCardinal kpair_convention_l .newest)
      (fun _ : Fin 1 => (ι'.bound 5).val.val) :=
    (rr_truth_native_l I mt.2.1 _ (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (ι'.bound 5).val)).mpr
        ((Formula.satisfies_isRegularCardinal_iff (kp_pair_l hZ) hZ.1 ..).mpr regularδ)
  have hVC := ZF.v_mem_l (kp_pair_l hZ) targetZF rv rankC
    (ZF.v_ordinal_height_l targetZF rankC (v_ordinal_l (kp_pair_l hZ) rv) member)
  let Un : Yn.Domain := ⟨U,common.left_rank.2.1⟩
  have ru := (rr_rank_native_l I my.2.1 hY ⟨L,common.left_rank.1⟩ Un).mp common.left_rank
  have cut (x : Yn.Domain) y (hx : Yn.mem x Un) (xy : Rd_entry_d x.val y t) : Rd_entry_d x.val y g :=
    (restrict.2 _ _).mpr ⟨(common.carrier _).mpr ⟨x.property,hx⟩,xy⟩
  have iQ := cut (ρ.bound 12).val (ε.bound 7).val hQU (transport.values 7)
  have hQC : Zn.mem (ε.bound 7) Cp := fz.transitive Vp hVC (ε.bound 7)
    ((common.image _).mpr ⟨_,common.injection.1.input_mem_of_pairMember iQ,iQ⟩)
  have sourceRank := (rr_rank_native_l I my.2.1 hY ⟨ηy,cy.height⟩ ⟨D,cy.member⟩).mp
    ((rr_rank_truth_l I).mpr cy.rank)
  have body := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff] at body
  let fields : Fin 11 → Term 54 := fun i => [.bound 16,.bound 17,.bound 23,.bound 24,.bound 15,
    .bound 14,.bound 13,.bound 12,.bound 2,.bound 1,.bound 0].get i
  let sourceEnv := Definitional.Env.substitute ρ fields
  have sourceLanguage : Formula.satisfies sourceEnv tg_reply_language0_m :=
    (Formula.satisfies_bind ρ fields tg_reply_language0_m).mp body.2.2.2.2.2.2.2.2.2.1
  obtain ⟨finiteN,limitτ,rankA,constantsA,poolA⟩ :=
    tg_reply_domain_read_l sourceZF sourceRank fy nd sourceEnv (Subtype.ext hwρ) sourceLanguage
  have hτU := KP.v_ordinal_subset_l hY ru (ρ.bound 15).val hτL
  have iτ := cut (ρ.bound 15).val (ε.bound 4).val hτU (transport.values 4)
  let nu : Nonempty {x : Yn.Domain // Yn.mem x Un} := ⟨⟨(ρ.bound 15).val,hτU⟩⟩
  let a : Env (rt_model_l Un nu) 1 := ⟨fun _ => ⟨(ρ.bound 15).val,hτU⟩,fun _ => ⟨(ρ.bound 15).val,hτU⟩⟩
  let b : Env Zn 1 := ⟨fun _ => ε.bound 4,fun _ => ε.bound 4⟩
  have limitτ' := (KP.limit0_sat_l hZ b .newest).mp
    ((rr_native_delta_l I my.2.1 mt.2.1 Un (v_transitive_l (kp_pair_l hY) ru) nu
      common.carrier common.injection common.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) a b (fun _ => iτ)).mp
        ((KP.limit0_sat_l hY _ .newest).mpr limitτ))
  obtain ⟨z,numbers⟩ := transport.numbers
  have targetOmega : Zn.IsOmega (ε.bound 0) := numbers.omega_l I (ZF.modelsKP hZF) hΩ hZ.1
  obtain ⟨θ,values,reply,same,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,table,language,queries⟩ :=
    tg_answer_input_l targetZF targetOmega rankC limitC fz ne ι' ε issued' (Subtype.ext eqω)
      transport.truth equal hQC transport.arity limitτ'
  let targetEnv : Env (rt_model_l Cp ne) 11 :=
    ⟨fun i => [ι'.bound 0,ι'.bound 1,ι'.bound 27,ι'.bound 28,θ.bound 4,Aq,Uq,Dq,rq,bq,hq].get i,ι'.free⟩
  obtain ⟨finiteNp,_,rankAp,constantsAp,poolAp⟩ :=
    tg_reply_domain_read_l targetZF rankC fz ne targetEnv (Subtype.ext eqω) language
  have iω : Rd_entry_d wy (ε.bound 0).val t := transport.values 0
  have in₀ : Rd_entry_d (ρ.bound 24).val.val (ι'.bound 28).val.val t :=
    (congrArg Subtype.val (equal 2)).symm ▸ transport.values 2
  have iτ' : Rd_entry_d (ρ.bound 15).val.val (θ.bound 4).val.val t :=
    (congrArg Subtype.val (values 4)).symm ▸ transport.values 4
  have iD : Rd_entry_d (ρ.bound 12).val.val (θ.bound 7).val.val t :=
    (congrArg Subtype.val (values 7)).symm ▸ transport.values 7
  have hwU : Rd_entry_d wy U S := ((common.carrier wy).mp
    (common.injection.1.input_mem_of_pairMember (hwρ ▸ transport.omega))).2
  have eqD := tg_reply_domain_raw_l (ZF.modelsKP hZF) my.2.1 mt.2.1 sourceZF targetZF
    common Bp transB carrier pool pred restrict endpoint layer
    ⟨wy,cy.omega_mem⟩ (ρ.bound 24).val (ρ.bound 15).val (ρ.bound 14).val (ρ.bound 13).val (ρ.bound 12).val
    (ε.bound 0) (ι'.bound 28).val (θ.bound 4).val (θ.bound 7).val Aq.val Uq.val Dq.val
    omega targetOmega finiteN hwU hτL rankA constantsA poolA rankAp constantsAp poolAp iω in₀ iτ' iD
  have domain : Rd_entry_d (ρ.bound 15).val.val (θ.bound 4).val.val g :=
    (congrArg Subtype.val (values 4)).symm ▸ iτ
  have type : Rd_entry_d (ρ.bound 11).val.val (θ.bound 9).val.val g :=
    cut (ρ.bound 11).val _ huU ((congrArg Subtype.val (values 9)).symm ▸ transport.values 9)
  have finiteL : Rd_entry_d (θ.bound 1).val.val (ε.bound 0).val T :=
    (congrArg Subtype.val (values 1)).symm ▸ transport.arity
  exact ⟨η',C',iw,iη,iC,current,ne,ι',θ,points,issued',eqω,ordinal,
    (fun x hx => cap ⟨x,(mt.2.2.2 x l hx).1⟩ hx),belowδ,member,regular,values,reply,same,
    transport.label _ (points 23),domain,type,finiteL,finiteNp,
    (fun i => transport.scalars i _ (points ([0,1,27,28].get i))),belowτ,key,
    Aq,Uq,Dq,rq,mq,bq,hq,qq,Subtype.ext eqD.symm,table,language,queries⟩

end YesMetaZFC.SetTheory.LargeCardinal
