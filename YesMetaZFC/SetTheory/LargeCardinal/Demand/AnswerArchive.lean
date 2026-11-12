import YesMetaZFC.SetTheory.LargeCardinal.Demand.AnswerTransport
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveHistory
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep

/-! # 同一次原回答实际登记新档案

从原后继的 23 槽回答读取固定 Q 行，运输三条查询的完整语义，构造合法
回答后立即调用历史追加。新行保存产生该回答的原 62 槽回合和原树节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_archive_d.finish_round_l
    {Ω c₀ X₀ R₀ c X R d Y S j k L l U V Γ g D t wr zr zx zy γ₀ D₀ C₀ C γ K z Da m i δ H : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (left : Smap_d I Ω c₀ c X₀ X j) (right : Smap_d I Ω c₀ d X₀ Y k)
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 62)
    (round : Formula.satisfies ρ td_round0_m)
    (rootLow : ∀ a x, M.mem a D₀ → Rd_entry_d a x j → Rd_entry_d x (ρ.bound 1).val R)
    (lettersRoot : Rd_entry_d Ar (ρ.bound 50).val j)
    (treeRoot : Rd_entry_d Sr (ρ.bound 22).val j)
    (depth : Td_depth_d I Ω X R (ρ.bound 47).val δ H)
    (chosen : Td_pick_d I Ω δ H (ρ.bound 49).val)
    (alphabetCode : Td_code_d I X R (ρ.bound 22).val (ρ.bound 21).val)
    (powerCount : Pc_count_d I Ω X R (ρ.bound 21).val)
    (supportBelow : Rd_entry_d L (ρ.bound 21).val R)
    (ι : Env (smdl_structure_l I (R := S) my.2.1) 47) (issued : Formula.satisfies ι td_issued0_m)
    (η : Env (smdl_structure_l I (R := S) my.2.1) 23) (reply : Formula.satisfies η td_reply0_m)
    (links : Td_reply_link_d Eq ι.bound η.bound)
    (sourceNumbers : Rr_layer_d I Ω X R (ρ.bound 19).val zx)
    (targetNumbers : Rr_layer_d I Ω Y S (ι.bound 0).val zy)
    (common : Ic_common_d I X R Y S L l U V Γ g)
    (below : Rd_entry_d (ρ.bound 0).val L R)
    (small : Rr_small_d I X R U) (cofinal : Tg_raw_cofinal_d I (ρ.bound 19).val X R L)
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
    (omegaLow : Rd_entry_d (ι.bound 0).val K S) (lettersLow : Rd_entry_d (ι.bound 6).val K S)
    (hm : M.mem m Ω) (sequence : M.IsSequenceOfLength I Da m)
    (index : Rd_entry_d m (ι.bound 19).val zy)
    (old : Td_archive_d I Ω c₀ X₀ Ar Sr Da Y S l
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val zy (ι.bound 20).val D₀ k)
    (real : ∃ s, Rd_entry_d (ρ.bound 44).val s g ∧
      Td_play_at_d I Y S (ι.bound 4).val (ι.bound 2).val (ι.bound 20).val s)
    (x : (smdl_structure_l I (R := S) my.2.1).Domain)
    (hx : (smdl_structure_l I (R := S) my.2.1).mem x (ι.bound 6)) :
    let Yn := smdl_structure_l I (R := S) my.2.1
    let native := ZFC.models_zf_l ((root.map_l hZF hΩ my right).native_l I hZF hΩ)
    let J := kp_pair_l (ZF.modelsKP native)
    ∃ b h n : Yn.Domain, ∃ m' Da' r E,
      KPair_d Yn b (η.bound 5) (η.bound 10) ∧ Fseq_end_d J (ι.bound 0) h (ι.bound 20) b ∧
      Yn.mem n (ι.bound 0) ∧ Yn.SuccessorOf n (ι.bound 46) ∧
      Fn0_d n (ι.bound 12) h ∧ Yn.mem h (ι.bound 18) ∧
      Yn.IsOrdinalDivision J n (ι.bound 4) (ι.bound 19) (ι.bound 3) ∧
      M.mem m' Ω ∧ M.SuccessorOf m' m ∧ M.IsSequenceOfLength I Da' m' ∧
      Rt_tuple_d (Td_archive_row_d.values_d
        ⟨fun k => (ρ.bound k).val,i,c,X,R,j,L,U,zx,δ,H,E⟩) r ∧
      (∀ n s, Rd_entry_d n s Da' ↔ Rd_entry_d n s Da ∨ n = m ∧ s = r) ∧
    ∃ y t : Yn.Domain, ∃ ψ : Env Yn 47,
      Yn.mem y (ι.bound 6) ∧
      (Gm_even_d J (ι.bound 0) (ι.bound 19) → y = x) ∧
      (¬ Gm_even_d J (ι.bound 0) (ι.bound 19) → Rd_entry_d h y (ι.bound 17)) ∧
      Fseq_end_d J (ι.bound 0) t h y ∧
      Fseq_end_d J (ι.bound 0) (ψ.bound 20) t (ψ.bound 21) ∧
      Rd_entry_d t (ψ.bound 21) (ι.bound 17) ∧
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι.bound (i.castAdd 28)) ∧
      Yn.SuccessorOf (ψ.bound 19) (ι.bound 19) ∧ Formula.satisfies ψ td_issued0_m ∧
      Rd_entry_d m' (ψ.bound 19).val zy ∧
      Yn.mem (ι.bound 24) (ψ.bound 24) ∧ Rd_entry_d l (ψ.bound 24).val S ∧
      Yn.MemberSubset h (ψ.bound 20) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' Y S l
        (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zy (ψ.bound 20).val D₀ k := by
  intro Yn native J
  have hX := ZF.modelsKP (ZFC.models_zf_l ((root.map_l hZF hΩ mx left).native_l I hZF hΩ))
  obtain ⟨b,pair,answer,keys⟩ := common.demand_answer_l hZF hΩ root mx my left right rootNumbers
    ρ round ι issued η reply links sourceNumbers targetNumbers below ft restrict pred points names cap
    target square omegaLow lettersLow
  obtain ⟨h,n,m',Da',r,E,ending,hn,sn,fn,position,clock,hm',sm,seq,tuple,append,archive⟩ :=
    old.answer_l hZF (i := i) hΩ hm sequence my native mx hX left ρ round rootLow lettersRoot treeRoot
      depth chosen alphabetCode powerCount supportBelow sourceNumbers below
      small cofinal common square (Or.inr rfl) ι issued index b (η.bound 5) (η.bound 10) pair answer keys real
  obtain ⟨y,t,ψ,hy,even,odd,digit,aux,value,head,successor,valid,increase,history⟩ :=
    td_issued_next_l native ι issued ending hn fn position clock hx
  obtain ⟨n',hn',idx⟩ := targetNumbers.injection.1.2.2 m' hm'
  have step : Yn.SuccessorOf ⟨n',hn'⟩ (ι.bound 19) :=
    targetNumbers.successor_l I hZF.1 native.1 (ι.bound 19) ⟨n',hn'⟩ index idx sm
  have eq := congrArg Subtype.val (step.eq native.1 successor)
  have index' : Rd_entry_d m' (ψ.bound 19).val zy := eq ▸ idx
  have state := (td_issued_sat_l J native.1 ψ).mp valid
  have rankL := (rr_rank_native_l I my.2.1 (ZF.modelsKP native)
    ⟨l,common.right_rank.1⟩ ⟨V,common.right_rank.2.1⟩).mp common.right_rank
  have bound : Rd_entry_d l (ψ.bound 24).val S := ordinal_down_l (ZF.modelsKP native)
    (v_ordinal_l J rankL) state.payload.2.2.2.2.2.2.2.2.1.1
      (fun a ha => (links 4).symm ▸ cap a.val ha) increase
  have kept := archive.mono_l I my (ZF.modelsKP native) (ψ.bound 20).property
    (fun a ha h => history ⟨a,ha⟩ h)
  have archive' : Td_archive_d I Ω c₀ X₀ Ar Sr Da' Y S l
      (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zy (ψ.bound 20).val D₀ k :=
    (congrArg Subtype.val (head 4)).symm ▸ (congrArg Subtype.val (head 1)).symm ▸
      (congrArg Subtype.val (head 2)).symm ▸ kept
  exact ⟨b,h,n,m',Da',r,E,pair,ending,hn,sn,fn,position,clock,hm',sm,seq,tuple,append,
    y,t,ψ,hy,even,odd,digit,aux,value,head,successor,valid,index',increase,bound,history,archive'⟩

end YesMetaZFC.SetTheory.LargeCardinal
