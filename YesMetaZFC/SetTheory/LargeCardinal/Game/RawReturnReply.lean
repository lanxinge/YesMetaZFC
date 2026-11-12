import YesMetaZFC.SetTheory.LargeCardinal.Iteration.RawReturn
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReplyTransport
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord

/-! # 第二原后继中的同次完整回答

第一共同层的完整值域和池图单射性实际恢复第二施加图中的原像。
同一次常值方块随后搬运完整回答及十六个请求坐标。标签使用原有限函数
固定定理，四个基础参数保留原边与第二池的交换，不假设所属模型的全嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 第一同池及实际逆图供应所有回拉；第二 cert 只解包一次。 -/
theorem Tg_image_at_d.return_reply_l
    {Ω c₀ X₀ R₀ c N R d P S q zp L₀ l₀ U₀ V₀ Γ₀ g₀ B₀ t₀ B k
      wp η C Ls Js Os Zs Ds ps Vs Ws qs d₃ Z T j₃ q₃ p₃ : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (mp : Smdl_d I d P S)
    (native : (smdl_structure_l I (R := S) mp.2.1).Models ZF)
    (context : Tg_context_d I wp P S η C)
    (nc : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨C,context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C,context.member⟩ nc) 54)
    (round : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val.val = wp)
    (v : Fin 46 → M.Domain)
    (request : Tg_request_d (fun y x => Rd_entry_d x y t₀) v (fun i => (ρ.bound i).val.val))
    (first : Ic_common_d I N R P S L₀ l₀ U₀ V₀ Γ₀ g₀)
    (pool : M.IsSetInjectionFromTo I t₀ B₀ P) (restrict₀ : M.IsRestrictionOf I g₀ t₀ Γ₀)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x g₀)
    (α β L W X K R' F c' d' Y RY j κ' A' D' u' : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (hα : Rd_entry_d α.val l₀ S) (hβ : Rd_entry_d β.val V₀ S)
    (hκ : (smdl_structure_l I (R := S) mp.2.1).mem (ρ.bound 21).val β)
    (limitα : (smdl_structure_l I (R := S) mp.2.1).IsLimitOrdinal α)
    (rankβ : V_d (kp_pair_l (ZF.modelsKP native)) α β) (above : Rd_entry_d l₀ L.val S)
    (data : Tg_image_at_d (ZF.modelsKP native) ⟨wp,context.omega_mem⟩
      (ρ.bound 21).val (ρ.bound 18).val (ρ.bound 23).val (ρ.bound 24).val
      (ρ.bound 31).val (ρ.bound 32).val (ρ.bound 34).val (ρ.bound 15).val
      (ρ.bound 12).val (ρ.bound 11).val (ρ.bound 36).val
      (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) (ρ.bound 38).val
      ⟨(ρ.bound 2).val,(ρ.bound 1).val,(ρ.bound 0).val⟩ L W X K R' F c' d' Y RY j κ' A' D' u')
    (cert : Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ c N R q B k P S zp d mp.2.1 (ZF.modelsKP native)
      ⟨V₀,first.right_rank.2.1⟩ ⟨wp,context.omega_mem⟩ (ρ.bound 21).val L F β X K j
      Ls Js Os Zs Ds ps Vs Ws qs d₃ Z T j₃ q₃ p₃) :
    ∃ target : Smdl_d I d₃ Z T,
      Zc_model_d I Ω d₃ Z T ∧ Smap_d I Ω c d₃ N Z j₃ ∧ Smap_d I Ω c₀ d₃ X₀ Z q₃ ∧
      (∀ x y, Rd_entry_d x y q₃ ↔ M.mem x X₀ ∧ ∃ a, Rd_entry_d x a q ∧ Rd_entry_d a y j₃) ∧
      It_payload_d p₃ (ρ.bound 21).val.val L.val F.val ∧ It_active_d hZF Ω d c d₃ j₃ p₃ ∧
      (∀ a i TT QQ GG EE r o, It_tree_d hZF Ω c₀ a TT QQ GG EE → M.SuccessorOf a i →
        Rd_entry_d i d QQ → Rd_entry_d r c QQ → It_map_d GG o r q →
        ∃ a' TT' QQ' GG' EE', It_tree_d hZF Ω c₀ a' TT' QQ' GG' EE' ∧
          It_extension_d a i r TT QQ GG EE a' TT' QQ' GG' EE' ∧
          Rd_entry_d a d₃ QQ' ∧ It_map_d GG' r a j₃ ∧ Rd_entry_d i p₃ EE' ∧ It_map_d GG' o a q₃) ∧
    ∃ l V Γ g, Ic_common_d I P S Z T L.val l W.val V Γ g ∧
      Fs_read_d (M := smdl_structure_l I (R := S) mp.2.1) ⟨wp,context.omega_mem⟩ W ∧
      Rr_small_d I P S W.val ∧
    ∃ Pκ : (smdl_structure_l I (R := S) mp.2.1).Domain,
      V_d (kp_pair_l (ZF.modelsKP native)) (ρ.bound 21).val Pκ ∧
      (∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain, ∀ a y,
        Rd_entry_d x.val Pκ.val S → Rd_entry_d x.val a k → (Rd_entry_d x.val y g ↔ Rd_entry_d a y j₃)) ∧
    ∃ Bp : (smdl_structure_l I (R := S) mp.2.1).Domain, ∃ Dp t,
      (smdl_structure_l I (R := S) mp.2.1).TransitiveSet Bp ∧
      (∀ x, M.mem x Dp ↔ M.mem x P ∧ Rd_entry_d x Bp.val S) ∧
      M.IsSetInjectionFromTo I t Dp Z ∧ M.IsRestrictionOf I g t Γ ∧
      Rd_entry_d L.val l t ∧ Rd_entry_d W.val V t ∧
      (∀ x y, Rd_entry_d x y t → ∀ z, Rd_entry_d z y T ↔ ∃ a, Rd_entry_d a x S ∧ Rd_entry_d a z t) ∧
    ∃ ε : Env (smdl_structure_l I (R := T) target.2.1) 22,
      Tg_raw_reply_transport_d I Ω Z T j₃ g t l target.2.1 (fun i => (ρ.bound i).val.val) v
        (fun i => (tg_round_reply_values_d (fun j => (ρ.bound j).val) ⟨wp,context.omega_mem⟩ κ' A' D' u' i).val) ε := by
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have hP := ZF.modelsKP native
  have fs := context.finite_l mp.2.1 hP.1
  have rankC := (rr_rank_native_l I mp.2.1 hP ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have limitC : Pn.IsLimitOrdinal ⟨η,context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ⟨η,context.height⟩)).mp context.limit)
  have height := (tg_round_control_l hP rankC limitC fs nc ρ round).2.isLimitOrdinal
  have used := data
  obtain ⟨rankX,source,hLδ,_,hτL,rW,hQW,loc,_,_,mx,my,ultra,crit,_,_,iU,iD,iu,_,_⟩ := used
  have hαL : Pn.mem α L := (loc.ordinals_l hP source.transitive source.code).2.transitive
    ⟨l₀,first.right_rank.1⟩ above α hα
  have raw := cert
  obtain ⟨_,_,_,_,hβX,transβ,_,_,_,_,_,mt,_,_,_,embed,rootMap,_,agreement,payload,active,certificate,rootGraph,
    Uc,rankU,readU,_,small,l,V,Γ,g,common,_,_,Pκ,rankP,lowSquare,_,bκ,κt,_,ibκ,iκt,_,boundκ,_,_,_,_,_,_,_,_,rest⟩ := raw
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,wT,_,zT,_,iwT,_,_,numbers,_,_,_,_,_,_,_,_,_,_,_,pool',build⟩ := rest
  obtain ⟨Ap,Qp,Bp,ep,Dq,Dp,_,_,t,pool',_,carrier,_,_,_,_,ft,restrict,endpoint,layer,_,_,
    _,H,_,iH,full,pred,commute,_⟩ := pool'
  have eqU := ZF.v_unique_l (kp_pair_l hP) native rankU rW
  subst Uc
  have target := certificate root
  have targetZF := ZFC.models_zf_l (target.native_l I hZF hΩ)
  have hT := ZF.modelsKP targetZF
  let Tn := smdl_structure_l I (R := T) mt.2.1
  have rankFirst := (rr_rank_native_l I mp.2.1 hP
    ⟨l₀,first.right_rank.1⟩ ⟨V₀,first.right_rank.2.1⟩).mp first.right_rank
  -- 任意低对象先从第一共同层取像，再由第一池的单射性识别指定原像。
  have back (x : Pn.Domain) a (hx : Pn.mem x β) (ha : Rd_entry_d a x.val t₀) : Rd_entry_d x.val a k := by
    obtain ⟨b,_,ib⟩ := (first.image x.val).mp
      ((v_transitive_l (kp_pair_l hP) rankFirst) β hβ x hx)
    have eq := pool.2 a b x.val ha ((restrict₀.2 b x.val).mp ib).2
    exact (inverse x.val a).mpr (eq.symm ▸ ib)
  obtain ⟨hA,hD,hu,hl,hn,hk,labels,labelLow,digits⟩ := tg_round_members_l native
    source.omega rankC fs nc ρ (Subtype.ext hw) rankβ limitα hκ round
  have hWB : Pn.mem W Bp := ((carrier W.val).mp (ft.1.input_mem_of_pairMember layer)).2
  obtain ⟨transB,pairB,nb,ψ,values,replyB⟩ := data.reply_pool_l native height rankβ limitα
    (height.1.transitive L hLδ α hαL) hA hD hu pool' hWB (digits 0) (digits 1) (fun i => digits i.succ.succ)
  let Hn : Tn.Domain := ⟨H,embed.1.1.output_mem_of_pairMember iH⟩
  obtain ⟨ε,points,reply⟩ := tg_reply_raw_image_l I mp.2.1 mt.2.1 hT Bp Hn pairB nb ψ replyB carrier ft full pred
  let vals := tg_round_reply_values_d (fun i => (ρ.bound i).val) ⟨wp,context.omega_mem⟩ κ' A' D' u'
  have actual i : Rd_entry_d (vals i).val (ε.bound i).val t :=
    Eq.mp (congrArg (fun x : Pn.Domain => Rd_entry_d x.val (ε.bound i).val t) (values i)) (points i)
  have carry (x : Pn.Domain) i a (hx : Pn.mem x β) (hi : Rd_entry_d x (vals i) j)
      (ha : Rd_entry_d a x.val t₀) : Rd_entry_d a (ε.bound i).val j₃ := by
    have hi : Rd_entry_d x (ψ.bound i).val j := Eq.mp (congrArg (fun y => Rd_entry_d x y j) (values i).symm) hi
    exact (commute x (ψ.bound i).val a (ε.bound i).val hx hi (back x a hx ha)).mp (points i)
  have pj := ultra.elementary_l native mx.1 my.1
  have pt := ultra.transitive_l native my.1
  have iw := pj.omega_l (kp_pair_l hP) native source.omega source.transitive pt mx my source.omega_mem
  have natural := pj.natural_l native source.omega source.transitive pt mx my source.omega_mem
  have hwβ := v_subset_mem_l (kp_pair_l hP) rankβ hκ source.below
  have low (x : Pn.Domain) (hx : Pn.mem x ⟨wp,context.omega_mem⟩) : Pn.mem x β := transβ _ hwβ x hx
  have program (i : Fin 9) : Rd_entry_d (v ([36,37,38,39,40,41,42,43,44].get i))
      (ε.bound ([10,11,15,16,17,18,19,20,21].get i)).val j₃ := by
    have eq : vals ([10,11,15,16,17,18,19,20,21].get i) =
        (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val :=
      Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))) i
    have old : Rd_entry_d (v ([36,37,38,39,40,41,42,43,44].get i))
        (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val.val t₀ :=
      Fin.cases (request 5) (Fin.cases (request 6) (Fin.cases (request 7) (Fin.cases (request 8)
        (Fin.cases (request 9) (Fin.cases (request 10) (Fin.cases (request 11)
          (Fin.cases (request 12) (Fin.cases (request 13) (fun i => Fin.elim0 i))))))))) i
    exact carry _ _ _ (low _ (digits i))
      (Eq.mp (congrArg (fun y => Rd_entry_d (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val y j) eq.symm)
        (natural _ (digits i))) old
  have linked : Tg_reply_link_d (fun x y => Rd_entry_d x y j₃) v (fun i => (ε.bound i).val) :=
    Fin.cases (carry _ 0 _ hwβ iw
      (Eq.mp (congrArg (fun a => Rd_entry_d (v 0) a t₀) hw) (request 0)))
      (Fin.cases (carry _ 1 _ (low _ hl) (natural _ hl) (request 3))
        (Fin.cases (carry _ 2 _ (low _ hn) (natural _ hn) (request 4))
          (Fin.cases (carry _ 3 _ hκ crit.image (request 14))
            (Fin.cases (carry _ 5 _ hA iU (request 15))
              (Fin.cases (carry _ 6 _ hD iD (request 16))
                (Fin.cases (carry _ 8 _ hu iu (request 17))
                  (Fin.cases (program 0) (Fin.cases (program 1) (Fin.cases (program 2)
                    (Fin.cases (program 3) (Fin.cases (program 4) (Fin.cases (program 5)
                      (Fin.cases (program 6) (Fin.cases (program 7)
                        (Fin.cases (program 8) (fun i => Fin.elim0 i))))))))))))))))
  have eqw := ft.1.1.2 wp wT (ε.bound 0).val ((restrict.2 _ _).mp iwT).2 (actual 0)
  have nums : Rr_layer_d I Ω Z T (ε.bound 0).val zT := eqw ▸ numbers
  have omega : Rd_entry_d (ρ.bound 16).val.val (ε.bound 0).val g := hw.symm ▸ eqw ▸ iwT
  have arity : Tn.mem (ε.bound 1) (ε.bound 0) :=
    (pred _ _ (points 0) _).mpr ⟨_,by rw [values 1,values 0]; exact hl,points 1⟩
  have eqb := agreement.injection.1.1.2 (ρ.bound 21).val.val bκ (v 24) ibκ (back _ _ hκ (request 14))
  have eqκ := embed.1.1.1.2 (v 24) κt (ε.bound 3).val (eqb ▸ iκt) (linked 3)
  have cap x (hx : Rd_entry_d x l T) : Rd_entry_d x (ε.bound 3).val T := eqκ ▸ boundκ x hx
  have labelsFixed := pj.finite_fixed_l native source.omega source.transitive pt mx my
    source.omega_mem hk (source.transitive β hβX _ labelLow) labels
  have labelW : Pn.mem (ρ.bound 41).val W := (v_transitive_l (kp_pair_l hP) rW) β
    (ZF.v_mem_l (kp_pair_l hP) native rankβ rW hαL) _ labelLow
  have label y (iy : Rd_entry_d (v 23) y j₃) : Rd_entry_d (ρ.bound 41).val.val y g := by
    have it := (commute (ρ.bound 41).val (ρ.bound 41).val (v 23) y labelLow labelsFixed
      (back _ _ labelLow (request 18))).mpr iy
    exact (restrict.2 _ _).mpr ⟨(common.carrier _).mpr ⟨(ρ.bound 41).val.property,labelW⟩,it⟩
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m,tg_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at seed
  have he : Pn.mem (ρ.bound 17).val ⟨wp,context.omega_mem⟩ :=
    Eq.mp (congrArg (fun a : Pn.Domain => Pn.mem (ρ.bound 17).val a) (Subtype.ext hw)) seed.2.2.1
  have scalar (x : Pn.Domain) a y (hx : Pn.mem x ⟨wp,context.omega_mem⟩)
      (old : Rd_entry_d a x.val t₀) (iy : Rd_entry_d a y j₃) : Rd_entry_d x.val y t :=
    (commute x x a y (low x hx) (natural x hx) (back x a (low x hx) old)).mpr iy
  have scalarω y (iy : Rd_entry_d (v 0) y j₃) : Rd_entry_d (ρ.bound 16).val.val y t := by
    have old : Rd_entry_d (v 0) wp t₀ := hw ▸ request 0
    have actualω := (commute ⟨wp,context.omega_mem⟩ ⟨wp,context.omega_mem⟩ (v 0) y hwβ iw
      (back _ _ hwβ old)).mpr iy
    exact hw.symm ▸ actualω
  have scalars : ∀ i : Fin 4, ∀ y, Rd_entry_d (v ([0,1,27,28].get i)) y j₃ →
      Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val y t :=
    Fin.cases scalarω (Fin.cases (fun y iy => scalar _ _ y he (request 1) iy)
      (Fin.cases (fun y iy => scalar _ _ y hl (request 3) iy)
        (Fin.cases (fun y iy => scalar _ _ y hn (request 4) iy) (fun i => Fin.elim0 i))))
  obtain ⟨_,_,_,extend⟩ := build.2 root
  refine ⟨mt,target,embed,rootMap,rootGraph,payload,active,?_,l,V,Γ,g,common,readU,small,
    Pκ,rankP,(fun x a y hx ia => lowSquare x a y hx ia),Bp,Dp,t,transB,carrier,ft,restrict,endpoint,layer,pred,
    ε,actual,reply,linked,⟨zT,nums⟩,omega,arity,cap,label,scalars⟩
  intro a i TT QQ GG EE r o tree succ owner parent origin
  obtain ⟨a',TT',QQ',GG',EE',next,extension,node,edge,move,rootEdge,_⟩ :=
    extend a i TT QQ GG EE r o tree succ owner parent origin
  exact ⟨a',TT',QQ',GG',EE',next,extension,node,edge,move,rootEdge⟩

end YesMetaZFC.SetTheory.LargeCardinal
