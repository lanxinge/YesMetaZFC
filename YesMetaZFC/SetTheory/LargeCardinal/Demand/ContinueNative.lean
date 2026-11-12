import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundReal
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawPool
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.RawReturn
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AnswerTransport
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.PowerRead
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveHistory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyPastRound

/-! # 非重置回合的两个实际原树后继

第一次施加的所属模型是当前节点 N，父模型是旧节点 A；该证书确定
新奇模型 P。恢复输入在这个 P 中更新，第二个扩展器再经共同层逆图
施加回 N。两个父边分别为 k→m 与 n→m+1，均保存同一个原根。

这里消费实际第一施加证书和已经恢复、更新的同一六十二槽回合。回合中的 κ、u
必须是同一共同图上的当前候选像；没有后继存在性或下一轮生产回调。
全部旧档案沿这两次共同层自动推进，当前事件使用原偶数父边的实际像。
两个固定名字与当前标签经低秩方块识别；在目标模型读取同一查询表，
实际证明返回的回答合法，并追加回答历史。两条边和回答先于实数输入固定；
每个输入随后由原策略产生下一请求。旧档案随完整历史延长保持，
第一施加给出的新奇模型幂集计数控制第二次施加的支撑，原偶模型的计数
控制其代表；下一请求实际返回计数与内部编码不变量。新奇行在下一实数
输入前生成完整字母枚举并登记，随后保存同一档案与实际树节点的对应。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_rank_cut_at_d.demand_double_l
    {Ω c₀ X₀ R₀ cA A RA qA Γ k₀ cN N R z o k n m T Q G E qN
      Ls Js Os Zs Ds ps Vs Ws qs cP P S j₁ q₁ p₁ Da χ D₀
      γ₀ C₀ CP γP VP tP wr zr mA dep tab : M.Domain}
    (root : Zc_model_d I Ω c₀ X₀ R₀)
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (tree : It_tree_d hZF Ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (mn : Smdl_d I cN N R) (qr : Rd_entry_d o c₀ Q)
    (parent : Rd_entry_d k cA Q) (current : Rd_entry_d n cN Q)
    (oldOrigin : It_map_d G o k qA) (origin : It_map_d G o n qN)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (U₀ w ξ L F β X K j δ κ u : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (first : Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ cA A RA qA Γ k₀ N R z cN mn.2.1 hN
      U₀ w ξ L F β X K j Ls Js Os Zs Ds ps Vs Ws qs cP P S j₁ q₁ p₁)
    (omega : (smdl_structure_l I (R := R) mn.2.1).IsOmega w)
    (rankX : V_d (kp_pair_l hN) δ X)
    (height : (smdl_structure_l I (R := R) mn.2.1).IsLimitOrdinal δ)
    (card : Sc_inaccessible_d w X L)
    (below : (smdl_structure_l I (R := R) mn.2.1).mem κ L)
    (mp : Smdl_d I cP P S)
    {l U V Δ g : M.Domain} (common : Ic_common_d I N R P S L.val l U V Δ g)
    (ε : Env (smdl_structure_l I (R := S) mp.2.1) 62)
    (round : Formula.satisfies ε td_round0_m)
    (pointκ : Rd_entry_d κ.val (ε.bound 24).val g)
    (pointu : Rd_entry_d u.val (ε.bound 38).val g)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m)
    (sourcePoints : ∀ i : Fin 17, Rd_entry_d
      (ι.bound ([0,23,24,27,28,25,31,32,37,38,39,40,41,42,43,44,45].get i)).val
      (ε.bound ([19,25,24,27,28,38,35,36,40,42,55,56,57,58,59,60,61].get i)).val g)
    (basePoints : ∀ i : Fin 2, Rd_entry_d (ι.bound ([1,6].get i)).val
      (ε.bound ([20,50].get i)).val g)
    {s₀ : M.Domain} (realTrace : Td_play_at_d I N R (ι.bound 4).val (ι.bound 2).val (ι.bound 20).val s₀)
    (realPoint : Rd_entry_d s₀ (ε.bound 44).val g)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S CP q₁ γP VP tP)
    (omegaLow : Rd_entry_d (ε.bound 19).val VP S)
    (lettersLow : Rd_entry_d (ε.bound 50).val VP S)
    (rootSquare : Tg_root_square_d D₀ qN q₁ g)
    (lower : ∀ x, Rd_entry_d x γP S → Rd_entry_d x (ε.bound 24).val S)
    (historyBound : ∀ x, Rd_entry_d x l S → Rd_entry_d x (ε.bound 43).val S)
    (numbersN : Rr_layer_d I Ω N R w.val z)
    (archive : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ qN)
    (archiveBound : Rd_entry_d χ κ.val R)
    (powerCount : Pc_count_d I Ω N R (ι.bound 5).val)
    (oddCount : Pc_count_d I Ω P S (ε.bound 21).val)
    (supportBelow : Rd_entry_d L.val (ι.bound 5).val R)
    (alphabetCode : Td_code_d I N R (ι.bound 7).val (ι.bound 5).val)
    (oddCode : Td_code_d I P S (ε.bound 22).val (ε.bound 21).val)
    (depth : Td_depth_d I Ω P S (ε.bound 47).val dep tab)
    (chosen : Td_pick_d I Ω dep tab (ε.bound 49).val)
    (rootLow : ∀ a x, M.mem a D₀ → Rd_entry_d a x q₁ → Rd_entry_d x (ε.bound 1).val S)
    (lettersRoot : Rd_entry_d Ar (ε.bound 50).val q₁)
    (treeRoot : Rd_entry_d Sr (ε.bound 22).val q₁)
    (hmA : M.mem mA Ω) (sequence : M.IsSequenceOfLength I Da mA)
    (index : Rd_entry_d mA (ι.bound 19).val z)
    (treeLinks : Td_archive_links_d o Q G E Da) :
    let Pn := smdl_structure_l I (R := S) mp.2.1
    let target := first.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 root
    let ground := target.native_l I hZF tree.omega
    let hP := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ L₂ W₂ X₂ K₂ R₂ F₂ c₂ d₂ Y₂ S₂ j₂ κ₂ U₂ E₂ u₂ : Pn.Domain,
      Td_image_at_d hP (ε.bound 19) (ε.bound 24) (ε.bound 21) (ε.bound 27) (ε.bound 28)
        (ε.bound 9) (ε.bound 35) (ε.bound 36) (ε.bound 38) (ε.bound 0) (ε.bound 3)
        (ε.bound 4) (ε.bound 40) (ε.bound 42) (ε.bound 16) (ε.bound 17) (ε.bound 18)
        (fun i => ε.bound ⟨55+i.val,by omega⟩) L₂ W₂ X₂ K₂ R₂ F₂ c₂ d₂ Y₂ S₂ j₂ κ₂ U₂ E₂ u₂ ∧
      Rd_entry_d l L₂.val S ∧ Tg_raw_cofinal_d I (ε.bound 19).val P S L₂.val ∧
    ∃ α β₂ : Pn.Domain, ∃ B v zp,
      Pn.mem α ⟨l,common.right_rank.1⟩ ∧ Pn.IsLimitOrdinal α ∧ V_d (kp_pair_l hP) α β₂ ∧
      Pn.mem (ε.bound 24) β₂ ∧
      (∀ x, M.mem x B ↔ M.mem x P ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I v B N ∧
      (∀ x y, Rd_entry_d x y v ↔ Rd_entry_d y x g) ∧
      Rr_layer_d I Ω P S (ε.bound 19).val zp ∧
    ∃ Ls₂ Js₂ Os₂ Zs₂ Ds₂ ps₂ Vs₂ Ws₂ qs₂ cH H RH J qH pH,
      Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ cN N R qN B v P S zp cP mp.2.1 hP
        ⟨V,common.right_rank.2.1⟩ (ε.bound 19) (ε.bound 24) L₂ F₂ β₂ X₂ K₂ j₂
        Ls₂ Js₂ Os₂ Zs₂ Ds₂ ps₂ Vs₂ Ws₂ qs₂ cH H RH J qH pH ∧
      Zc_model_d I Ω cH H RH ∧ Smap_d I Ω cN cH N H J ∧
      Smap_d I Ω c₀ cH X₀ H qH ∧
      (∀ x y, Rd_entry_d x y qH ↔ M.mem x X₀ ∧ ∃ a, Rd_entry_d x a qN ∧ Rd_entry_d a y J) ∧
      It_payload_d pH (ε.bound 24).val L₂.val F₂.val ∧ It_active_d hZF Ω cP cN cH J pH ∧
    ∃ mh : Smdl_d I cH H RH, ∃ lH VH ΔH gH D t,
      Ic_common_d I P S H RH L₂.val lH W₂.val VH ΔH gH ∧ Rr_small_d I P S W₂.val ∧
      M.IsSetInjectionFromTo I t D H ∧ M.IsRestrictionOf I gH t ΔH ∧
      Rd_entry_d L₂.val lH t ∧ Rd_entry_d W₂.val VH t ∧
      (∀ x y, Rd_entry_d x y t → ∀ a, Rd_entry_d a y RH ↔
        ∃ b, Rd_entry_d b x S ∧ Rd_entry_d b a t) ∧
    ∃ ζ : Env (smdl_structure_l I (R := RH) mh.2.1) 23,
      Formula.satisfies ζ td_reply0_m ∧
      (∀ i, Rd_entry_d
        (td_reply_values_d (ε.bound 19) (ε.bound 27) (ε.bound 28) (ε.bound 9) κ₂ (ε.bound 0)
          U₂ E₂ (ε.bound 3) u₂ (ε.bound 4) (ε.bound 40) (ε.bound 42)
          (ε.bound 16) (ε.bound 17) (ε.bound 18) (fun j => ε.bound ⟨55+j.val,by omega⟩) i).val
        (ζ.bound i).val t) ∧
      Rd_entry_d κ.val (ζ.bound 4).val J ∧ Rd_entry_d u.val (ζ.bound 9).val J ∧
      (∃ zh, Rr_layer_d I Ω H RH (ζ.bound 0).val zh) ∧
      Rd_entry_d (ε.bound 19).val (ζ.bound 0).val gH ∧
      Rd_entry_d (ζ.bound 1).val (ζ.bound 0).val RH ∧
      Rd_entry_d (ζ.bound 2).val (ζ.bound 0).val RH ∧
      Rd_entry_d (ζ.bound 3).val (ζ.bound 0).val RH ∧
      (∀ x, Rd_entry_d x lH RH → Rd_entry_d x (ζ.bound 4).val RH) ∧
    ∃ ι' : Env (smdl_structure_l I (R := RH) mh.2.1) 47,
      (∀ i, Rd_entry_d (ι.bound i).val (ι'.bound i).val J) ∧
      Formula.satisfies ι' td_issued0_m ∧ Td_reply_link_d Eq ι'.bound ζ.bound ∧
    ∃ CH γH VH₀ tH,
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ H RH CH qH γH VH₀ tH ∧
      Rd_entry_d γP γH gH ∧ Rd_entry_d VP VH₀ gH ∧ It_comp_d tP gH tH ∧
      Rd_entry_d γH lH RH ∧ Tg_root_square_d D₀ q₁ qH gH ∧
      (∀ x y, Rd_entry_d x VP S → Rd_entry_d x y gH → Rd_entry_d y VH₀ RH) ∧
      (∀ x, Rd_entry_d x γH RH → Rd_entry_d x (ζ.bound 4).val RH) ∧
      Rd_entry_d (ι'.bound 0).val VH₀ RH ∧ Rd_entry_d (ι'.bound 6).val VH₀ RH ∧
    ∃ b : (smdl_structure_l I (R := RH) mh.2.1).Domain,
      KPair_d (smdl_structure_l I (R := RH) mh.2.1) b (ζ.bound 5) (ζ.bound 10) ∧
      Formula.satisfies (⟨fun i => [ι'.bound 0,ι'.bound 1,ι'.bound 2,ι'.bound 3,ι'.bound 4,
        ι'.bound 5,ι'.bound 6,ι'.bound 7,ι'.bound 8,ι'.bound 9,ι'.bound 10,ι'.bound 11,
        ι'.bound 19,ι'.bound 20,b].get i,ι'.free⟩ :
          Env (smdl_structure_l I (R := RH) mh.2.1) 15) td_answer0_m ∧
      (∀ i : Fin 3, Rd_entry_d (ε.bound ([25,0,4].get i)).val
        ([ι'.bound 23,ζ.bound 5,ζ.bound 10].get i).val gH) ∧
    ∃ zh, ∃ h jh : (smdl_structure_l I (R := RH) mh.2.1).Domain,
      Rr_layer_d I Ω H RH (ι'.bound 0).val zh ∧
    let Hn := smdl_structure_l I (R := RH) mh.2.1
    ∃ nativeH : Hn.Models ZF,
      Fseq_end_d (kp_pair_l (ZF.modelsKP nativeH)) (ι'.bound 0) h (ι'.bound 20) b ∧
      Hn.mem jh (ι'.bound 0) ∧ Hn.SuccessorOf jh (ι'.bound 46) ∧
      Fn0_d jh (ι'.bound 12) h ∧ Hn.mem h (ι'.bound 18) ∧
      Hn.IsOrdinalDivision (kp_pair_l (ZF.modelsKP nativeH)) jh
        (ι'.bound 4) (ι'.bound 19) (ι'.bound 3) ∧
    ∃ mA' Da' r En,
      M.mem mA' Ω ∧ M.SuccessorOf mA' mA ∧ M.IsSequenceOfLength I Da' mA' ∧
      Rt_tuple_d (Td_archive_row_d.values_d
        ⟨fun i => (ε.bound i).val,m,cP,P,S,q₁,L₂.val,W₂.val,zp,dep,tab,En⟩) r ∧
      (∀ i s, Rd_entry_d i s Da' ↔ Rd_entry_d i s Da ∨ i = mA ∧ s = r) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' H RH lH
        (ι'.bound 4).val (ι'.bound 1).val (ι'.bound 2).val zh h.val D₀ qH ∧
    ∃ θ T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂,
      It_tree_d hZF Ω c₀ θ T₁ Q₁ G₁ E₁ ∧ It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m cP Q₁ ∧ It_map_d G₁ k m j₁ ∧ Rd_entry_d n p₁ E₁ ∧ It_map_d G₁ o m q₁ ∧
      It_tree_d hZF Ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ cH Q₂ ∧ It_map_d G₂ n θ J ∧ Rd_entry_d m pH E₂ ∧ It_map_d G₂ o θ qH ∧
      (∀ γ, It_lower_d I γ N R ξ.val → It_lower_d I γ P S (ε.bound 24).val →
        It_critical_bound_d I γ Q E → It_critical_bound_d I γ Q₂ E₂) ∧
      Td_archive_links_d o Q₂ G₂ E₂ Da' ∧
      Ic_round_d hZF Ω (fun i => [m,θ,T₁,Q₁,G₁,E₁,P,S,l].get i)
        (fun i => [θ,θ₂,T₂,Q₂,G₂,E₂,H,RH,lH].get i) ∧
    ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x (ι.bound 6) →
    ∃ a y t : Hn.Domain, ∃ ψ : Env Hn 47,
      Rd_entry_d x.val a.val J ∧ Hn.mem y (ι'.bound 6) ∧
      (Gm_even_d (kp_pair_l (ZF.modelsKP nativeH)) (ι'.bound 0) (ι'.bound 19) → y = a) ∧
      (¬ Gm_even_d (kp_pair_l (ZF.modelsKP nativeH)) (ι'.bound 0) (ι'.bound 19) →
        Rd_entry_d h y (ι'.bound 17)) ∧
      Fseq_end_d (kp_pair_l (ZF.modelsKP nativeH)) (ι'.bound 0) t h y ∧
      Fseq_end_d (kp_pair_l (ZF.modelsKP nativeH)) (ι'.bound 0) (ψ.bound 20) t (ψ.bound 21) ∧
      Rd_entry_d t (ψ.bound 21) (ι'.bound 17) ∧
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι'.bound (i.castAdd 28)) ∧
      Hn.SuccessorOf (ψ.bound 19) (ι'.bound 19) ∧ Formula.satisfies ψ td_issued0_m ∧
      Hn.mem (ι'.bound 24) (ψ.bound 24) ∧ Rd_entry_d lH (ψ.bound 24).val RH ∧
      Hn.MemberSubset h (ψ.bound 20) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' H RH lH
        (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zh (ψ.bound 20).val D₀ qH ∧
      Td_rank_step_d (N := smdl_structure_l I (R := R) mn.2.1) (P := Hn)
        (fun x y => Rd_entry_d x.val y.val J) ι.bound ψ.bound ∧
      Pc_count_d I Ω H RH (ψ.bound 5).val ∧
      Td_code_d I H RH (ψ.bound 7).val (ψ.bound 5).val ∧
      Rd_entry_d mA' (ψ.bound 19).val zh := by
  intro Pn target ground hP
  have fromRoot := tree.diagram.elementary o n qN c₀ X₀ R₀ cN N R origin qr current root.model mn
  have native := ZFC.models_zf_l ((root.map_l hZF tree.omega mn fromRoot).native_l I hZF tree.omega)
  have nativeP := ZFC.models_zf_l ground
  -- 第一证书的共同层及数字解释确实来自该次施加。
  have used := first
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    Uc,rankUc,_,_,small,_,_,_,_,_,_,_,rest⟩ := used
  have rankU := (rr_rank_native_l I mn.2.1 (ZF.modelsKP native)
    ⟨L.val,common.left_rank.1⟩ ⟨U,common.left_rank.2.1⟩).mp common.left_rank
  have equalU := congrArg Subtype.val (ZF.v_unique_l (kp_pair_l hN) native rankUc rankU)
  have smallU : Rr_small_d I N R U := by
    change Uc.val = U at equalU
    rw [← equalU]
    exact small
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,wp,_,zp,_,_,_,_,numbers,_,_,_,_,_,_,_,_,_,_,_,_,build⟩ := rest
  obtain ⟨_,_,_,extend₁⟩ := build.2 root
  obtain ⟨omegaP,heightP,_,_,growth,L₂,W₂,X₂,K₂,R₂,F₂,c₂,d₂,Y₂,S₂,j₂,κ₂,U₂,E₂,u₂,image⟩ :=
    td_round_native_l hP ε round
  have data := image
  obtain ⟨rank₂,source,hLδ,_,hτL,rankW,hDW,loc,card₂,strong,mx,my,ultra,critical,bound,
    limitκ,iU,iE,iu,_,reply⟩ := data
  have cofinal₂ := it_support_cofinal_l I hZF.1 mp.2.1 hP card₂ rank₂ heightP
  have above : Rd_entry_d l L₂.val S := by
    have rankV := (rr_rank_native_l I mp.2.1 hP ⟨l,common.right_rank.1⟩
      ⟨V,common.right_rank.2.1⟩).mp common.right_rank
    have high := (loc.ordinals_l hP source.transitive source.code).2
    have hχ : Pn.mem (ε.bound 43) L₂ := high.transitive (ε.bound 0) hτL (ε.bound 43) growth
    exact ordinal_down_l hP (v_ordinal_l (kp_pair_l hP) rankV) high
      (fun x hx => historyBound x.val hx) hχ
  have omega' := numbers.omega_l I (ZF.modelsKP hZF) tree.omega hP.1
  have ew : ε.bound 19 = (⟨wp,numbers.member⟩ : Pn.Domain) :=
    hP.1.eq_of_same_members _ _ (fun x => ⟨omegaP.2 _ omega'.1 x,omega'.2 _ omegaP.1 x⟩)
  have nums : Rr_layer_d I Ω P S (ε.bound 19).val zp := (congrArg Subtype.val ew).symm ▸ numbers
  obtain ⟨high,regular,_⟩ := sc_v_inaccessible_up_l hN height rankX card
  have cofinal : ∃ ν : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).IsCofinality (kp_pair_l (ZF.modelsKP native)) ν
        ⟨L.val,common.left_rank.1⟩ ∧ (smdl_structure_l I (R := R) mn.2.1).mem w ν :=
    ⟨L,regular,high⟩
  obtain ⟨α,β₂,hα,_,hκ,limitα,rankβ,B,v,carrier,fv,range,pred,inverse,cut⟩ :=
    common.return_cut_l hZFC tree.omega root mn mp fromRoot ground w κ omega cofinal smallU below
      source rank₂ heightP loc card₂ strong mx my ultra critical.image bound nums pointκ above
  obtain ⟨Ls₂,Js₂,Os₂,Zs₂,Ds₂,ps₂,Vs₂,Ws₂,qs₂,cH,H,RH,J,qH,pH,second⟩ := cut
  obtain ⟨ωN,_,hωN,aboveN,regularN,strongN,_⟩ := td_issued_woodin_l (ZF.modelsKP native) ι issued
  have ownerLocal := it_local_short_l I mp.2.1 (kp_pair_l hP) nativeP.1
    (loc.rank_absolute_l hP source.omega rank₂ heightP source.code)
  have nextCount := second.power_l hZFC tree.omega root mn fromRoot mp.2.1 nativeP
    ⟨V,common.right_rank.2.1⟩ (ε.bound 19) (ε.bound 24) L₂ F₂ β₂ X₂ K₂ j₂ (ε.bound 21)
      nums ownerLocal heightP.1 hLδ oddCount
      ωN (ι.bound 5) ⟨L.val,common.left_rank.1⟩ ⟨U,common.left_rank.2.1⟩
        hωN aboveN regularN strongN rankU
          (regularN.isCardinal.1.transitive _ supportBelow) range powerCount
  -- 第二次施加的范围由本轮的原语言证明，完整回答进入同一个实际 H。
  have hαδ := heightP.1.transitive L₂ hLδ α
    ((loc.ordinals_l hP source.transitive source.code).2.transitive
      ⟨l,common.right_rank.1⟩ above α hα)
  obtain ⟨hU,hE,hu,hq,hm',hb,hz,hσ⟩ := td_round_native_scope_l nativeP ε round rankβ limitα hκ
  obtain ⟨mh,targetH,embed,rootH,rootGraph,payload,active,lH,VH,ΔH,gH,commonH,_,smallH,
    Kκ,rankKκ,lowSquare,pool⟩ :=
    second.demand_reply_l hZF tree.omega root mp.2.1 nativeP rank₂ source heightP loc mx my ultra critical
      limitκ iU iE iu reply rankβ limitα hαδ hU hE hu rankW hDW hq hm' hb hz hσ
  obtain ⟨_,_,_,_,D,t,_,_,_,_,ft,restrict,endpoint,layer,_,_,predH,commute,
    ζ,points,truth,numsH,omegaH,hqH,hnH,hmH,capH⟩ := pool
  have iκ := (commute (ε.bound 24) κ₂ κ.val (ζ.bound 4).val hκ critical.image
    ((inverse _ _).mpr pointκ)).mp (points 4)
  have iuH := (commute (ε.bound 38) u₂ u.val (ζ.bound 9).val hu iu
    ((inverse _ _).mpr pointu)).mp (points 9)
  -- 当前请求沿原偶数父边整体搬运；源语言和程序用同一个常值方块识别。
  obtain ⟨vι,iι⟩ := Classical.axiomOfChoice
    (fun i : Fin 47 => embed.1.1.2.2 (ι.bound i).val (ι.bound i).property)
  let ι' : Env (smdl_structure_l I (R := RH) mh.2.1) 47 :=
    ⟨fun i => ⟨vι i,(iι i).1⟩,fun _ => ⟨vι 0,(iι 0).1⟩⟩
  have issued' : Formula.satisfies ι' td_issued0_m :=
    (smap_source_l I hZF tree.omega mn mh embed td_issued0_m td_issued0_closed_l
      ι ι' (fun i => (iι i).2)).mp issued
  have sourceSeed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at sourceSeed
  have language := sourceSeed.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff,
    ee_domain_pack_m,ee_domain_pack0_m,Formula.satisfies_mem_iff] at language
  have ωU : Pn.mem (ε.bound 19) (ε.bound 35) := language.1.1
  have ωβ := (v_transitive_l (kp_pair_l hP) rankβ) _ hU _ ωU
  have elementary := ultra.elementary_l nativeP mx.1 my.1
  have transTarget := ultra.transitive_l nativeP my.1
  have natural := elementary.natural_l nativeP source.omega source.transitive transTarget mx my source.omega_mem
  have omegaFixed := elementary.omega_l (kp_pair_l hP) nativeP source.omega source.transitive
    transTarget mx my source.omega_mem
  have sourceRound := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at sourceRound
  have record := (td_record_sat_l (kp_pair_l hP) hP.1 ..).mp sourceRound.2.2.2.2.2.2.2.2.2.2.1
  have hnP := omegaP.transitive hP (ε.bound 9) hm' (ε.bound 28) record.height_end.predecessor_mem
  have carry (x y : Pn.Domain) (b E : M.Domain) (hx : Pn.mem x β₂)
      (xy : Rd_entry_d x y j₂) (back : Rd_entry_d b x.val g) (value : Rd_entry_d y.val E t) :
      Rd_entry_d b E J := (commute x y b E hx xy ((inverse _ _).mpr back)).mp value
  have carryNat (x : Pn.Domain) (b E : M.Domain) (hx : Pn.mem x (ε.bound 19))
      (back : Rd_entry_d b x.val g) (value : Rd_entry_d x.val E t) : Rd_entry_d b E J :=
    carry x x b E ((v_transitive_l (kp_pair_l hP) rankβ) _ ωβ x hx) (natural x hx) back value
  have pw := carry (ε.bound 19) (ε.bound 19) (ι.bound 0).val (ζ.bound 0).val
    ωβ omegaFixed (sourcePoints 0) (points 0)
  have pq := carryNat (ε.bound 27) (ι.bound 27).val (ζ.bound 1).val hq (sourcePoints 3) (points 1)
  have pn := carryNat (ε.bound 28) (ι.bound 28).val (ζ.bound 2).val hnP (sourcePoints 4) (points 2)
  have pk := carry (ε.bound 24) κ₂ (ι.bound 24).val (ζ.bound 4).val hκ critical.image
    (sourcePoints 2) (points 4)
  have pU := carry (ε.bound 35) U₂ (ι.bound 31).val (ζ.bound 6).val hU iU (sourcePoints 6) (points 6)
  have pE := carry (ε.bound 36) E₂ (ι.bound 32).val (ζ.bound 7).val hE iE (sourcePoints 7) (points 7)
  have pu := carry (ε.bound 38) u₂ (ι.bound 25).val (ζ.bound 9).val hu iu (sourcePoints 5) (points 9)
  have pb := carryNat (ε.bound 40) (ι.bound 37).val (ζ.bound 11).val hb (sourcePoints 8) (points 11)
  have pz := carryNat (ε.bound 42) (ι.bound 38).val (ζ.bound 12).val hz (sourcePoints 9) (points 12)
  have ps (i : Fin 7) : Rd_entry_d (ι.bound ⟨39+i.val,by omega⟩).val
      (ζ.bound ⟨16+i.val,by omega⟩).val J := by
    apply carryNat (ε.bound ⟨55+i.val,by omega⟩) _ _ (hσ i)
    · exact Fin.cases (sourcePoints 10) (Fin.cases (sourcePoints 11) (Fin.cases (sourcePoints 12)
        (Fin.cases (sourcePoints 13) (Fin.cases (sourcePoints 14) (Fin.cases (sourcePoints 15)
          (Fin.cases (sourcePoints 16) (fun j => Fin.elim0 j))))))) i
    · exact Fin.cases (points 16) (Fin.cases (points 17) (Fin.cases (points 18)
        (Fin.cases (points 19) (Fin.cases (points 20) (Fin.cases (points 21)
          (Fin.cases (points 22) (fun j => Fin.elim0 j))))))) i
  have eqn : ι'.bound 28 = ζ.bound 2 := Subtype.ext (embed.1.1.1.2 _ _ _ (iι 28).2 pn)
  -- 回答元数由同一池图中的 n+1 决定，不增加第一共同图上的 m 坐标。
  let Hn := smdl_structure_l I (R := RH) mh.2.1
  have sm : Hn.SuccessorOf (ζ.bound 3) (ζ.bound 2) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a,ha,ia⟩ := (predH _ _ (points 3) x.val).mp hx
      let aP : Pn.Domain := ⟨a,(mp.2.2.2 a (ε.bound 9).val ha).1⟩
      rcases (record.height_end aP).mp ha with h | eq
      · exact Or.inl ((predH _ _ (points 2) x.val).mpr ⟨a,h,ia⟩)
      · have eq : aP = ε.bound 28 := nativeP.1.eq_of_same_members _ _ eq
        have ex : x = ζ.bound 2 :=
          Subtype.ext (ft.1.1.2 _ _ _ (congrArg Subtype.val eq ▸ ia) (points 2))
        exact Or.inr (fun y => ex ▸ Iff.rfl)
    · rintro (hx | eq)
      · obtain ⟨a,ha,ia⟩ := (predH _ _ (points 2) x.val).mp hx
        exact (predH _ _ (points 3) x.val).mpr
          ⟨a,(record.height_end ⟨a,(mp.2.2.2 a (ε.bound 28).val ha).1⟩).mpr (Or.inl ha),ia⟩
      · have ex : x = ζ.bound 2 := (targetH.ext.native_l I mh.2.1).eq_of_same_members _ _ eq
        subst x
        exact (predH _ _ (points 3) (ζ.bound 2).val).mpr
          ⟨(ε.bound 28).val,record.height_end.predecessor_mem,points 2⟩
  have targetState := (td_issued_sat_l (kp_pair_l (ZF.modelsKP
    (ZFC.models_zf_l (targetH.native_l I hZF tree.omega)))) (targetH.ext.native_l I mh.2.1) ι').mp issued'
  have sm' : Hn.SuccessorOf (ι'.bound 29) (ζ.bound 2) := eqn ▸ targetState.payload.2.2.2.1.2.2.2
  have eqm : ι'.bound 29 = ζ.bound 3 := sm'.eq (targetH.ext.native_l I mh.2.1) sm
  have links : Td_reply_link_d Eq ι'.bound ζ.bound :=
    Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 0).2 pw))
      (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 27).2 pq))
        (Fin.cases eqn (Fin.cases eqm
          (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 24).2 pk))
            (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 31).2 pU))
              (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 32).2 pE))
                (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 25).2 pu))
                  (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 37).2 pb))
                    (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 38).2 pz))
                      (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 39).2 (ps 0)))
                        (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 40).2 (ps 1)))
                          (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 41).2 (ps 2)))
                            (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 42).2 (ps 3)))
                              (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 43).2 (ps 4)))
                                (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 44).2 (ps 5)))
                                  (Fin.cases (Subtype.ext (embed.1.1.1.2 _ _ _ (iι 45).2 (ps 6)))
                                    (fun i => Fin.elim0 i)))))))))))))))))
  -- 全部旧行同时经过这两次共同层；历史沿本次原偶数父边搬运。
  obtain ⟨zh,numsTarget⟩ := numsH
  have historyPoints : ∀ i : Fin 4,
      Rd_entry_d ([(ι.bound 4).val,(ι.bound 1).val,(ι.bound 2).val,(ι.bound 20).val].get i)
        ([(ι'.bound 4).val,(ι'.bound 1).val,(ι'.bound 2).val,(ι'.bound 20).val].get i) J :=
    Fin.cases (iι 4).2 (Fin.cases (iι 1).2 (Fin.cases (iι 2).2
      (Fin.cases (iι 20).2 (fun i => Fin.elim0 i))))
  have roots : It_comp_d qN J qH := ⟨rootH.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨a,xa,ay⟩ => ⟨fromRoot.1.1.input_mem_of_pairMember xa,a,xa,ay⟩⟩⟩
  -- 第二条实际父边来自 N；以第一共同图的逆图推进 P 中的根切片。
  have fromP : Smap_d I Ω c₀ cP X₀ P q₁ := first.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have domain : M.MemberSubset D₀ X₀ := by
    intro x hx
    obtain ⟨y,_,xy⟩ := slice.injection.1.2.2 x hx
    exact fromP.1.1.input_mem_of_pairMember (slice.root x y xy)
  obtain ⟨CH,_,contextH⟩ := rootH.1.1.2.2 C₀
    (fromP.1.1.input_mem_of_pairMember slice.context)
  have hH := ZF.modelsKP (ZFC.models_zf_l (targetH.native_l I hZF tree.omega))
  obtain ⟨γH,VH₀,tH,iγ,iV,comp,sliceH,boundH,squareH⟩ :=
    slice.continue_step_l hZF commonH mp mh hP hH
      (ε.bound 24) Kκ rankKκ image.2.2.2.1 lower rootSquare inverse
      (fun x hx y E back => lowSquare x y E hx back)
      fromP.1.1.1 fromRoot.1.1 domain roots contextH
  have insideH x y (hx : Rd_entry_d x VP S) (xy : Rd_entry_d x y gH) :
      Rd_entry_d y VH₀ RH := (commonH.pred VP VH₀ iV y).mpr ⟨x,hx,xy⟩
  have rankH := (rr_rank_native_l I mh.2.1 hH
    ⟨lH,commonH.right_rank.1⟩ ⟨VH,commonH.right_rank.2.1⟩).mp commonH.right_rank
  have lowerH x (hx : Rd_entry_d x γH RH) : Rd_entry_d x (ζ.bound 4).val RH :=
    capH x ((v_ordinal_l (kp_pair_l hH) rankH).transitive
      ⟨γH,sliceH.rank.1⟩ boundH ⟨x,(mh.2.2.2 x γH hx).1⟩ hx)
  -- 两个固定名字与当前标签使用同一低秩方块，随后在 H 内验证实际回答。
  have subK : Pn.MemberSubset ⟨VP,slice.rank.2.1⟩ Kκ :=
    (KP.v_compare_l hP
      ((rr_rank_native_l I mp.2.1 hP ⟨γP,slice.rank.1⟩ ⟨VP,slice.rank.2.1⟩).mp slice.rank)
      rankKκ (fun x hx => lower x.val hx)).1
  have omegaK : Pn.mem (ε.bound 19) Kκ := subK _ omegaLow
  have transK := v_transitive_l (kp_pair_l hP) rankKκ
  have empty := (Formula.satisfies_isEmpty_iff ..).mp sourceSeed.2.1
  have stateN := (td_issued_sat_l (kp_pair_l hN) hN.1 ι).mp issued
  have kω : Pn.mem (ε.bound 25) (ε.bound 19) :=
    (common.pred _ _ (sourcePoints 0) _).mpr ⟨_,stateN.payload.2.1,sourcePoints 1⟩
  have lowPoint (x : Pn.Domain) (i : Fin 47) (hx : Pn.mem x Kκ)
      (back : Rd_entry_d (ι.bound i).val x.val g) :
      Rd_entry_d x.val (ι'.bound i).val gH :=
    (lowSquare x _ _ hx ((inverse _ _).mpr back)).mpr (iι i).2
  have ePoint := lowPoint (ε.bound 20) 1
    (transK _ omegaK _ (num_mem_l nativeP.1 omegaP (show Num_d 0 (ε.bound 20) from empty)))
    (basePoints 0)
  have kPoint := lowPoint (ε.bound 25) 23 (transK _ omegaK _ kω) (sourcePoints 1)
  have aPoint := lowPoint (ε.bound 50) 6 (subK _ lettersLow) (basePoints 1)
  have names : ∀ i : Fin 3, Rd_entry_d (ε.bound ([20,25,50].get i)).val
      (ι'.bound ([1,23,6].get i)).val t :=
    Fin.cases ((restrict.2 _ _).mp ePoint).2
      (Fin.cases ((restrict.2 _ _).mp kPoint).2
        (Fin.cases ((restrict.2 _ _).mp aPoint).2 (fun i => Fin.elim0 i)))
  have wLowH : Rd_entry_d (ι'.bound 0).val VH₀ RH :=
    (congrArg Subtype.val (links 0)).symm ▸ insideH _ _ omegaLow omegaH
  have aLowH : Rd_entry_d (ι'.bound 6).val VH₀ RH := insideH _ _ lettersLow aPoint
  have numsIssued : Rr_layer_d I Ω H RH (ι'.bound 0).val zh :=
    (congrArg Subtype.val (links 0)).symm ▸ numsTarget
  obtain ⟨b,pair,answer,keys⟩ := commonH.demand_answer_l hZF tree.omega root mp mh fromP rootH
    rootNumbers ε round ι' issued' ζ truth links nums numsIssued hτL ft restrict predH
    (Fin.cases (points 0) (Fin.cases (points 5) (Fin.cases (points 3)
      (Fin.cases (points 8) (Fin.cases (points 10) (fun i => Fin.elim0 i))))))
    names capH sliceH squareH wLowH aLowH
  have nextArchive := archive.advance_l hZF common commonH tree.omega mn mp mh embed hN hP
    targetH.ext numbersN numsTarget (ε.bound 24) Kκ rankKκ pointκ below
      (above := image.2.2.2.1) archiveBound inverse lowSquare roots historyPoints
  have nativeH := ZFC.models_zf_l (targetH.native_l I hZF tree.omega)
  have realLanguage := sourceSeed.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at realLanguage
  have realLow := td_round_real_mem_l nativeP ε round rankKκ
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp realLanguage.2.1) omegaK (subK _ lettersLow)
  obtain ⟨sH,realImage,realPlay⟩ := realTrace.image_l I hZF tree.omega mn mh embed
    (Fin.cases (iι 4).2 (Fin.cases (iι 2).2 (Fin.cases (iι 20).2 (fun i => Fin.elim0 i))))
  have realH : Rd_entry_d (ε.bound 44).val sH gH :=
    (lowSquare (ε.bound 44) s₀ sH realLow ((inverse _ _).mpr realPoint)).mpr realImage
  -- 档案轮号沿同一原偶数父边搬运；随后实际生成新奇行的枚举和行码。
  obtain ⟨a,ha,ia⟩ := numsIssued.injection.1.2.2 mA hmA
  have naturalMap := (numbersN.omega_map_l I hZF tree.omega mn mh embed
    (root.map_l hZF tree.omega mn fromRoot).ext targetH.ext numsIssued).2
  have ea := embed.1.1.1.2 _ _ _ (naturalMap mA _ _ index ia) (iι 19).2
  have index' : Rd_entry_d mA (ι'.bound 19).val zh := by
    change Rd_entry_d mA (vι 19) zh
    exact ea ▸ ia
  obtain ⟨h,jh,mA',Da',r,En,ending,hjh,sjh,fh,hh,clock,hmA',smA,seq,tuple,append,registered⟩ :=
    nextArchive.answer_l hZF (i := m) tree.omega hmA sequence mh nativeH mp hP fromP
      ε round rootLow lettersRoot treeRoot depth chosen oddCode oddCount hLδ nums hτL
      smallH cofinal₂ commonH squareH (Or.inr rfl) ι' issued' index' b (ζ.bound 5) (ζ.bound 10)
      pair answer keys ⟨sH,realH,realPlay⟩
  -- 两次插入分别使用旧父节点 k 和当前偶节点 n。
  obtain ⟨θ,T₁,Q₁,G₁,E₁,tree₁,extension₁,node₁,edge₁,move₁,root₁,critical₁⟩ :=
    extend₁ m n T Q G E k o tree hm current parent oldOrigin
  have cert₂ := second
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    _,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := cert₂
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,build₂⟩ := rest
  obtain ⟨_,_,_,extend₂⟩ := build₂.2 root
  have current₁ := extension₁.2.2.1 n cN current
  have origin₁ := (extension₁.2.2.2.1 o n qN hm.predecessor_mem).mpr origin
  obtain ⟨θ₂,T₂,Q₂,G₂,Eout,tree₂,extension₂,node₂,edge₂,move₂,root₂,critical₂⟩ :=
    extend₂ θ m T₁ Q₁ G₁ E₁ n o tree₁ extension₁.1 node₁ current₁ origin₁
  have linksTree := ((treeLinks.extend_l hZF tree extension₁).extend_l hZF tree₁ extension₂).push_l
    tuple (extension₂.2.2.1 m cP node₁)
      ((extension₂.2.2.2.1 o m q₁ extension₁.1.predecessor_mem).mpr root₁) move₂ payload append
  have firstData := first
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,firstPayload,_⟩ := firstData
  have quality := it_owner_l I mp hP (ε.bound 19) (ε.bound 24) L₂ F₂
    (ε.bound 21) X₂ K₂ R₂ nums rank₂ heightP source loc card₂ strong
  have copy := ic_copy_past_l hZFC tree₁ extension₁.1 mn mp current₁ node₁ hP
    ⟨V,common.right_rank.2.1⟩ (ε.bound 19) (ε.bound 24) L₂ F₂ β₂ X₂ K₂ j₂
      (ε.bound 21) R₂ second nums source rank₂ heightP loc quality
      common move₁ firstPayload inverse smallU commonH above tree₂ extension₂ node₂ edge₂ move₂ payload
  refine ⟨L₂,W₂,X₂,K₂,R₂,F₂,c₂,d₂,Y₂,S₂,j₂,κ₂,U₂,E₂,u₂,image,above,cofinal₂,
    α,β₂,B,v,zp,hα,limitα,rankβ,hκ,carrier,fv,inverse,nums,
    Ls₂,Js₂,Os₂,Zs₂,Ds₂,ps₂,Vs₂,Ws₂,qs₂,cH,H,RH,J,qH,pH,second,targetH,embed,rootH,
    rootGraph,payload,active,mh,lH,VH,ΔH,gH,D,t,commonH,smallH,ft,restrict,endpoint,layer,
    predH,ζ,truth,points,iκ,iuH,⟨zh,numsTarget⟩,omegaH,hqH,hnH,hmH,capH,
    ι',fun i => (iι i).2,issued',links,
    CH,γH,VH₀,tH,sliceH,iγ,iV,comp,boundH,squareH,insideH,lowerH,wLowH,aLowH,b,pair,answer,keys,
    zh,h,jh,numsIssued,nativeH,ending,hjh,sjh,fh,hh,clock,mA',Da',r,En,hmA',smA,seq,tuple,append,registered,
    θ,T₁,Q₁,G₁,E₁,θ₂,T₂,Q₂,G₂,Eout,tree₁,extension₁,node₁,edge₁,move₁,root₁,
    tree₂,extension₂,node₂,edge₂,move₂,root₂,
    (fun γ lower₁ lower₂ old => critical₂ γ lower₂ (critical₁ γ lower₁ old)),linksTree,copy,?_⟩
  -- 已选回答与两条原边不依赖对手的实数输入；之后只读取原策略。
  intro x hx
  obtain ⟨a,ha,xa⟩ := embed.1.1.2.2 x.val x.property
  let a' : Hn.Domain := ⟨a,ha⟩
  have ha' : Hn.mem a' (ι'.bound 6) :=
    (embed.relation_l I hZF tree.omega mn mh xa (iι 6).2).mp hx
  obtain ⟨y,t',ψ,hy,even,odd,digit,aux,value,head,succ,valid,increase,history⟩ :=
    td_issued_next_l nativeH ι' issued' ending hjh fh hh clock ha'
  have state := (td_issued_sat_l (kp_pair_l hH) nativeH.1 ψ).mp valid
  have boundNext : Rd_entry_d lH (ψ.bound 24).val RH := ordinal_down_l hH
    (v_ordinal_l (kp_pair_l hH) rankH) state.payload.2.2.2.2.2.2.2.2.1.1
      (fun a ha => (links 4).symm ▸ capH a.val ha) increase
  have kept := registered.mono_l I mh hH (ψ.bound 20).property
    (fun a ha h₀ => history ⟨a,ha⟩ h₀)
  have archive' : Td_archive_d I Ω c₀ X₀ Ar Sr Da' H RH lH
      (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zh (ψ.bound 20).val D₀ qH :=
    (congrArg Subtype.val (head 4)).symm ▸ (congrArg Subtype.val (head 1)).symm ▸
      (congrArg Subtype.val (head 2)).symm ▸ kept
  obtain ⟨a,ha,ia⟩ := numsIssued.injection.1.2.2 mA' hmA'
  have step : Hn.SuccessorOf ⟨a,ha⟩ (ι'.bound 19) :=
    numsIssued.successor_l I hZF.1 nativeH.1 (ι'.bound 19) ⟨a,ha⟩ index' ia smA
  have ea := congrArg Subtype.val (step.eq nativeH.1 succ)
  exact ⟨a',y,t',ψ,xa,hy,even,odd,digit,aux,value,head,succ,valid,increase,boundNext,history,archive',
    Smap_d.demand_rank_step_l hZF tree.omega mn mh embed hN hH
      ι issued ι' ψ (fun i => (iι i).2) head valid ending history,
    (congrArg Subtype.val (head 5)).symm ▸ nextCount (ι'.bound 5).val (iι 5).2,
    (congrArg Subtype.val (head 7)).symm ▸ (congrArg Subtype.val (head 5)).symm ▸
      alphabetCode.map_l hZF tree.omega mn mh embed (iι 7).2 (iι 5).2,ea ▸ ia⟩

end YesMetaZFC.SetTheory.LargeCardinal
