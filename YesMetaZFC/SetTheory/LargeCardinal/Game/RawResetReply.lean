import YesMetaZFC.SetTheory.LargeCardinal.Game.RawResetFactory
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReplyInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype

/-! # 同一次原重置的完整回答与查询表

只解包一次固定证书中的共同图及完整代表池。回答沿该池传输，原请求沿
同一超幂边传输，两者在唯一一次产生的目标反射层相会。实际查询表与
回答域由秩及有限池唯一性识别；根切片和三个查询成员随后使用此处的同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际回答与固定原超幂给出同图目标 issued、完整 reply 和原表项。 -/
theorem Tg_image_at_d.raw_reset_reply_l
    {ω c₀ X₀ R₀ d N R q w η C z Γ k Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂ : M.Domain}
    (hω : M.IsOmega ω) (root : Zc_model_d I ω c₀ X₀ R₀) (mn : Smdl_d I d N R)
    (native : (smdl_structure_l I (R := R) mn.2.1).Models ZF)
    (context : Tg_context_d I w N R η C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 54)
    (issued : Formula.satisfies ι tg_issued0_m) (round : Formula.satisfies ρ tg_round0_m)
    (hw : (ι.bound 0).val.val = w)
    (request : Tg_request_d Eq (fun i => (ι.bound i).val.val) (fun i => (ρ.bound i).val.val))
    (empty : ι.bound 23 = ι.bound 1)
    (growth : Rd_entry_d (ι.bound 24).val.val (ρ.bound 15).val.val R)
    (L W X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ V : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (data : Tg_image_at_d (ZF.modelsKP native) ⟨w,context.omega_mem⟩
      (ρ.bound 21).val (ρ.bound 18).val (ρ.bound 23).val (ρ.bound 24).val
      (ρ.bound 31).val (ρ.bound 32).val (ρ.bound 34).val (ρ.bound 15).val
      (ρ.bound 12).val (ρ.bound 11).val (ρ.bound 36).val
      (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) (ρ.bound 38).val
      ⟨(ρ.bound 2).val,(ρ.bound 1).val,(ρ.bound 0).val⟩ L W X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁)
    (rankV : V_d (kp_pair_l (ZF.modelsKP native)) (ρ.bound 15).val V)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X.val R)
    (graph : ∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y)
    (cert : Er_rank_cut_at_d hZF ω c₀ X₀ R₀ d N R q Γ k N R z d mn.2.1 (ZF.modelsKP native)
      X ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F V X K j₁
      Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂) :
    ∃ l Vc Dc t, Ic_common_d I N R P R₂ L.val l W.val Vc Dc t ∧
    ∃ Pκ : (smdl_structure_l I (R := R) mn.2.1).Domain,
      V_d (kp_pair_l (ZF.modelsKP native)) (ρ.bound 21).val Pκ ∧
      Rd_entry_d (ρ.bound 21).val.val L.val R ∧
      (∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain, ∀ E,
        Rd_entry_d x.val Pκ.val R → (Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j₂)) ∧
    ∃ B₀ : (smdl_structure_l I (R := R) mn.2.1).Domain, ∃ Bp t₀,
      (smdl_structure_l I (R := R) mn.2.1).TransitiveSet B₀ ∧
      (∀ x, M.mem x Bp ↔ M.mem x N ∧ Rd_entry_d x B₀.val R) ∧
      M.IsSetInjectionFromTo I t₀ Bp P ∧ M.IsRestrictionOf I t t₀ Dc ∧
      Rd_entry_d L.val l t₀ ∧ Rd_entry_d W.val Vc t₀ ∧
      (∀ x E, Rd_entry_d x E t₀ → ∀ y,
        Rd_entry_d y E R₂ ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t₀) ∧
    ∃ target : Smdl_d I d₂ P R₂,
      Zc_model_d I ω d₂ P R₂ ∧ Smap_d I ω d d₂ N P j₂ ∧ Smap_d I ω c₀ d₂ X₀ P q₂ ∧
      (∀ x E, Rd_entry_d x E q₂ ↔ M.mem x X₀ ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y E j₂) ∧
    ∃ w₂ η₂ C₂ z₂, Rd_entry_d w w₂ j₂ ∧ Rd_entry_d η η₂ j₂ ∧ Rd_entry_d C C₂ j₂ ∧
      Rr_layer_d I ω P R₂ w₂ z₂ ∧ Rd_entry_d w w₂ t ∧
    ∃ current : Tg_context_d I w₂ P R₂ η₂ C₂,
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := R₂) target.2.1).Domain //
      (smdl_structure_l I (R := R₂) target.2.1).mem x ⟨C₂,current.member⟩},
    ∃ ι₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 46,
    ∃ ε₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 22,
      (∀ i, Rd_entry_d (ι.bound i).val.val (ι₂.bound i).val.val j₂) ∧
      Formula.satisfies ι₂ tg_issued0_m ∧ (ι₂.bound 0).val.val = w₂ ∧
      Rr_truth_d I P R₂ (KP.ord0_m .newest) (fun _ : Fin 1 => (ι₂.bound 24).val.val) ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧
      Rd_entry_d l (ι₂.bound 5).val.val R₂ ∧ Rd_entry_d l C₂ R₂ ∧
      Rr_truth_d I P R₂ (Formula.isRegularCardinal kpair_convention_l .newest)
        (fun _ : Fin 1 => (ι₂.bound 5).val.val) ∧
      (∀ i, Rd_entry_d (tg_round_reply_values_d (fun j => (ρ.bound j).val)
        ⟨w,context.omega_mem⟩ κ₁ U₁ D₁ u₁ i).val (ε₂.bound i).val.val t₀) ∧
      Formula.satisfies ε₂ tg_reply0_m ∧ Tg_reply_link_d Eq ι₂.bound ε₂.bound ∧
      Rd_entry_d (ρ.bound 41).val.val (ι₂.bound 23).val.val t ∧
      Rd_entry_d (ρ.bound 15).val.val (ε₂.bound 4).val.val t ∧
      Rd_entry_d (ρ.bound 11).val.val (ε₂.bound 9).val.val t ∧
      Rd_entry_d (ε₂.bound 1).val.val w₂ R₂ ∧
      Rd_entry_d (ι₂.bound 28).val.val w₂ R₂ ∧
      (∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
        (ι₂.bound ([0,1,27,28].get i)).val.val t₀) ∧
      Rd_entry_d (ε₂.bound 4).val.val (ι₂.bound 5).val.val R₂ ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ε₂.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        ι₂.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 5)
        tg_query_request0_m ∧
    ∃ Aq Uq Dq rq mq bq hq qq,
      Dq = ε₂.bound 7 ∧
      Tg_query_data_d (ι₂.bound 11) (ε₂.bound 4) (ι₂.bound 26) (ι₂.bound 1) (ι₂.bound 1) Aq Uq Dq rq mq bq hq qq ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ε₂.bound 4,Aq,Uq,Dq,rq,bq,hq].get i,
        ι₂.free⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 11)
        tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ι₂.bound 26,
        ι₂.bound 1,ι₂.bound 1,rq,mq,bq,hq,qq].get i,ι₂.free⟩ :
        Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 12)
        tg_query_row0_m := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  have hN := ZF.modelsKP native
  have fs := context.finite_l mn.2.1 hN.1
  have rankC := (rr_rank_native_l I mn.2.1 hN ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have limitC : Nn.IsLimitOrdinal ⟨η,context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ⟨η,context.height⟩)).mp context.limit)
  have height := (tg_round_control_l hN rankC limitC fs nc ρ round).2.isLimitOrdinal
  have eκ : (ρ.bound 21).val = (ι.bound 24).val := Subtype.ext (request 14)
  have ew : (ρ.bound 16).val.val = w := (request 0).trans hw
  have body := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at body
  have language := body.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limitτ := (rt_limit_l fs.transitive nc hN (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have imageData := data
  obtain ⟨rankX,source,hLδ,hκL,hτL,rW,hQW,loc,card,strong,mx,my,ultra,crit,lb,_,iU,iD,iu,_,answer⟩ := imageData
  -- 命题字段直接投影；只对后续实际使用的见证块作存在消去。
  have finite := cert.1
  have hVX := cert.2.2.2.1
  have transV := cert.2.2.2.2.2.1
  have core := cert.2.2.2.2.2.2.2.2.2.2.2
  have mp := core.1
  have core := core.2.2.2.2
  have embed := core.1
  have rootMap := core.2.1
  have core := core.2.2.2.2.2.2
  have certificate := core.1
  have rootGraph := core.2.1
  obtain ⟨Uc,rankUc,readUc,_,_,l,Vc,Dc,t,common,_,_,Pκ,rankP,lowSquare,
    κ₀,bκ,κ',hκ₀,hbκ,hκ',_,boundκ,_,_,_,_,_,fixκ,_,_,rest⟩ := core.2.2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨w₀,w₂,z₀,z₂,hww₀,hww₂,omegaEdge,_,newNumbers,_,_,_,_,_,_,_,_,_,_,_,pool,_⟩ := rest
  obtain ⟨A₀,Q₀,B₀,e₀,Dp,Bp,_,_,t₀,pool,dc,bc,_,_,_,_,ft,restrict,endpoint,layer,_,_,
    _,HV,_,hbHV,fullPool,predPool,commute,_⟩ := pool
  -- 两个源 V_L 由同一高度的唯一性识别；下文共同图直接使用保存轮的 W。
  have eqW := ZF.v_unique_l (kp_pair_l hN) native rankUc rW
  subst Uc
  let Pn := smdl_structure_l I (R := R₂) mp.2.1
  have target := certificate root
  have targetZF := ZFC.models_zf_l (target.native_l I hZF hω)
  have hP := ZF.modelsKP targetZF
  have κδ := height.1.transitive L hLδ (ρ.bound 21).val hκL
  have subK := (KP.v_compare_l hN rankP rankX (height.1.transitive (ρ.bound 21).val κδ)).1
  have square (x : Nn.Domain) (E) (hx : Nn.mem x Pκ) : Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j₂ :=
    lowSquare x x.val E hx ((graph x.val x.val).mpr ⟨(carrier x.val).mpr ⟨x.property,subK x hx⟩,rfl⟩)
  have hκV := ZF.v_ordinal_mem_l (kp_pair_l hN) native rankV (eκ.symm ▸ growth)
  obtain ⟨hU,hD,hu,hl,hn',_,_,labelLow,digits⟩ := tg_round_members_l native
    source.omega rankC fs nc ρ (Subtype.ext ew) rankV limitτ hκV round
  have hWB : Nn.mem W B₀ := ((bc W.val).mp (ft.1.input_mem_of_pairMember layer)).2
  obtain ⟨transB,pairB,nb₀,ψ,values,replyB⟩ := data.reply_pool_l native height rankV limitτ
    (height.1.transitive L hLδ (ρ.bound 15).val hτL) hU hD hu pool hWB (digits 0) (digits 1)
    (fun i => digits i.succ.succ)
  let HVn : Pn.Domain := ⟨HV,embed.1.1.output_mem_of_pairMember hbHV⟩
  obtain ⟨ε,replyPoints,reply⟩ := tg_reply_raw_image_l I mn.2.1 mp.2.1 hP
    B₀ HVn pairB nb₀ ψ replyB bc ft fullPool predPool
  let vals := tg_round_reply_values_d (fun i => (ρ.bound i).val) ⟨w,context.omega_mem⟩ κ₁ U₁ D₁ u₁
  have points i : Rd_entry_d (vals i).val (ε.bound i).val t₀ :=
    Eq.mp (congrArg (fun x : Nn.Domain => Rd_entry_d x.val (ε.bound i).val t₀) (values i)) (replyPoints i)
  have carry (x : Nn.Domain) i a (hx : Nn.mem x V) (hi : Rd_entry_d x (vals i) j₁)
      (ha : x.val = a) : Rd_entry_d a (ε.bound i).val j₂ := by
    have hxΓ := (carrier x.val).mpr ⟨x.property,(v_transitive_l (kp_pair_l hN) rankX) V hVX x hx⟩
    have hi : Rd_entry_d x (ψ.bound i).val j₁ :=
      Eq.mp (congrArg (fun y => Rd_entry_d x y j₁) (values i).symm) hi
    exact ha ▸ (commute x (ψ.bound i).val x.val (ε.bound i).val hx hi
      ((graph x.val x.val).mpr ⟨hxΓ,rfl⟩)).mp (replyPoints i)
  have internalMap := ultra.elementary_l native mx.1 my.1
  have internalTrans := ultra.transitive_l native my.1
  have iw₀ := internalMap.omega_l (kp_pair_l hN) native source.omega source.transitive internalTrans mx my source.omega_mem
  have natural := internalMap.natural_l native source.omega source.transitive internalTrans mx my source.omega_mem
  have hwV := v_subset_mem_l (kp_pair_l hN) rankV hκV source.below
  have low (x : Nn.Domain) (hx : Nn.mem x ⟨w,context.omega_mem⟩) : Nn.mem x V := transV _ hwV x hx
  have program (i : Fin 9) : Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (ε.bound ([10,11,15,16,17,18,19,20,21].get i)).val j₂ := by
    have eq : vals ([10,11,15,16,17,18,19,20,21].get i) =
        (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val :=
      Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))) i
    have matched : (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val.val =
        (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val :=
      Fin.cases (request 5) (Fin.cases (request 6) (Fin.cases (request 7) (Fin.cases (request 8)
        (Fin.cases (request 9) (Fin.cases (request 10) (Fin.cases (request 11)
          (Fin.cases (request 12) (Fin.cases (request 13) (fun j => Fin.elim0 j))))))))) i
    exact carry _ _ _ (low _ (digits i))
      (Eq.mp (congrArg (fun y => Rd_entry_d (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val y j₁) eq.symm)
        (natural _ (digits i))) matched
  have linked : Tg_reply_link_d (fun x y => Rd_entry_d x y j₂)
      (fun i => (ι.bound i).val.val) (fun i => (ε.bound i).val) :=
    Fin.cases (carry _ 0 _ hwV iw₀ (ew.symm.trans (request 0)))
      (Fin.cases (carry _ 1 _ (low _ hl) (natural _ hl) (request 3))
        (Fin.cases (carry _ 2 _ (low _ hn') (natural _ hn') (request 4))
          (Fin.cases (carry _ 3 _ hκV crit.image (request 14))
            (Fin.cases (carry _ 5 _ hU iU (request 15))
              (Fin.cases (carry _ 6 _ hD iD (request 16))
                (Fin.cases (carry _ 8 _ hu iu (request 17))
                  (Fin.cases (program 0) (Fin.cases (program 1) (Fin.cases (program 2)
                    (Fin.cases (program 3) (Fin.cases (program 4) (Fin.cases (program 5)
                      (Fin.cases (program 6) (Fin.cases (program 7)
                        (Fin.cases (program 8) (fun i => Fin.elim0 i))))))))))))))))
  -- 同池输运只生产原生回答；唯一目标上下文与全部原表项交给共享读取核。
  have eqw := ft.1.1.2 w w₂ (ε.bound 0).val ((restrict.2 _ _).mp hww₂).2 (points 0)
  have numbers : Rr_layer_d I ω P R₂ (ε.bound 0).val z₂ := eqw ▸ newNumbers
  have omega : Rd_entry_d w (ε.bound 0).val t := eqw ▸ hww₂
  have arity : Pn.mem (ε.bound 1) (ε.bound 0) :=
    (predPool _ _ (replyPoints 0) _).mpr ⟨_,by rw [values 1,values 0]; exact hl,replyPoints 1⟩
  have eqb : bκ = (ι.bound 24).val.val :=
    ((graph (ρ.bound 21).val.val bκ).mp hbκ).2.symm.trans (congrArg Subtype.val eκ)
  have eqκ := embed.1.1.1.2 (ι.bound 24).val.val κ' (ε.bound 3).val (eqb ▸ hκ') (linked 3)
  have cap x (hx : Rd_entry_d x l R₂) : Rd_entry_d x (ε.bound 3).val R₂ := eqκ ▸ boundκ x hx
  have seedFacts := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m,tg_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at seedFacts
  have heω : Nn.mem (ρ.bound 17).val ⟨w,context.omega_mem⟩ :=
    Eq.mp (congrArg (fun x : Nn.Domain => Nn.mem (ρ.bound 17).val x)
      (show (ρ.bound 16).val = (⟨w,context.omega_mem⟩ : Nn.Domain) from Subtype.ext ew)) seedFacts.2.2.1
  have eLabel : (ρ.bound 41).val = (ρ.bound 17).val := Subtype.ext
    ((request 18).trans ((congrArg (fun x => x.val.val) empty).trans (request 1).symm))
  have hLabelω : Nn.mem (ρ.bound 41).val ⟨w,context.omega_mem⟩ := eLabel.symm ▸ heω
  have idLabel : Rd_entry_d (ρ.bound 41).val.val (ρ.bound 41).val.val k :=
    (graph _ _).mpr ⟨(carrier _).mpr ⟨(ρ.bound 41).val.property,
      (v_transitive_l (kp_pair_l hN) rankX) V hVX (ρ.bound 41).val labelLow⟩,rfl⟩
  have label y (iy : Rd_entry_d (ι.bound 23).val.val y j₂) : Rd_entry_d (ρ.bound 41).val.val y t :=
    (fixκ _ _ y (ρ.bound 41).val.property (source.below _ hLabelω) idLabel).mpr
      (Eq.mp (congrArg (fun x => Rd_entry_d x y j₂) (request 18).symm) iy)
  have scalar (x : Nn.Domain) a y (hx : Nn.mem x ⟨w,context.omega_mem⟩)
      (ha : x.val = a) (iy : Rd_entry_d a y j₂) : Rd_entry_d x.val y t₀ :=
    (commute x x a y (low x hx) (natural x hx)
      ((graph x.val a).mpr ⟨(carrier x.val).mpr ⟨x.property,finite.transitive _ finite.omega_mem x hx⟩,ha⟩)).mpr iy
  have scalarω y (iy : Rd_entry_d (ι.bound 0).val.val y j₂) : Rd_entry_d (ρ.bound 16).val.val y t₀ := by
    have eq := embed.1.1.1.2 (ι.bound 0).val.val (ε.bound 0).val y (linked 0) iy
    exact ew.symm ▸ eq ▸ points 0
  have scalars : ∀ i : Fin 4, ∀ y, Rd_entry_d (ι.bound ([0,1,27,28].get i)).val.val y j₂ →
      Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val y t₀ :=
    Fin.cases scalarω (Fin.cases (fun y iy => scalar _ _ y heω (request 1) iy)
      (Fin.cases (fun y iy => scalar _ _ y hl (request 3) iy)
        (Fin.cases (fun y iy => scalar _ _ y hn' (request 4) iy) (fun i => Fin.elim0 i))))
  have transport : Tg_raw_reply_transport_d I ω P R₂ j₂ t t₀ l mp.2.1
      (fun i => (ρ.bound i).val.val) (fun i => (ι.bound i).val.val) (fun i => (vals i).val) ε :=
    ⟨points,reply,linked,⟨z₂,numbers⟩,ew.symm ▸ omega,arity,cap,label,scalars⟩
  have huW : Nn.mem (ρ.bound 11).val W := v_subset_mem_l (kp_pair_l hN) rW hQW answer.1
  obtain ⟨η₂,C₂,iw,iη,iC,current,nd,ι₂,ε₂,issuedPoints,issued₂,eqω,ordinal,
    candidateBound,belowδ,member,regular,values₂,reflected,same,iLabel,domainView,iType,finiteL,finiteNp,
    pointBase,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,domainEq,table,language₂,queries⟩ :=
    transport.input_l hZF hω mn mn mp hN native targetZF context context embed nc nc ι ρ issued round hw ew
      source.omega κ₁ U₁ D₁ u₁ B₀ common transB bc ft restrict endpoint layer predPool hτL hQW huW ε
  have finalPoints i : Rd_entry_d (vals i).val (ε₂.bound i).val.val t₀ :=
    (congrArg Subtype.val (values₂ i)).symm ▸ points i
  exact ⟨l,Vc,Dc,t,common,Pκ,rankP,hκL,(fun x E hx => square x E hx),B₀,Bp,t₀,
    transB,bc,ft,restrict,endpoint,layer,predPool,mp,target,embed,rootMap,rootGraph,
    (ε.bound 0).val,η₂,C₂,z₂,iw,iη,iC,numbers,omega,current,nd,ι₂,ε₂,issuedPoints,issued₂,eqω,ordinal,
    candidateBound,belowδ,member,regular,finalPoints,reflected,same,iLabel,domainView,iType,
    finiteL,finiteNp,pointBase,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,domainEq,table,language₂,queries⟩

end YesMetaZFC.SetTheory.LargeCardinal
