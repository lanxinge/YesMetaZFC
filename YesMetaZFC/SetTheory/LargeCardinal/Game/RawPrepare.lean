import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepareRoot
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.ContinueNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.PreparedResult
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalStep

/-! # 非空原请求自动选择真实档案

实际 issued 的继续规则给出较早原轮号；同一完整数字图将它读成
外部有限档案中的索引。返回原十一项行及其整份证书，不另选共同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem Tg_raw_request_d.select_l
    {Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q : M.Domain}
    {frame : Tg_raw_archive_frame_d M.Domain} {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q frame v)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨w,request.context.omega_mem⟩))
    (ne : v 23 ≠ v 1) :
    ∃ m r₀, ∃ row : Tg_raw_archive_row_d M.Domain,
      M.mem m k ∧ Rd_entry_d m (v 22) z ∧ Rd_entry_d m r₀ D ∧
      Rt_tuple_d row.values_d r₀ ∧ row.link_d frame ∧
      Tg_raw_archive_entry_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ q N R χ w C
        (v 4) (v 1) (v 2) (v 3) z (v 20) m r₀ := by
  let N₀ := smdl_structure_l I (R := R) ⟨w,request.context.omega_mem⟩
  obtain ⟨nc,ι,values,issued,index⟩ := request.read_l I hKP ext
  have fs := request.context.finite_l ⟨w,request.context.omega_mem⟩ ext
  let J := rt_pair_l fs.transitive nc ext fs.pair
  have en := rt_model_ext_l ext fs.transitive nc
  have different : ι.bound 23 ≠ ι.bound 1 := fun eq => ne
    ((values 23).symm.trans ((congrArg (fun a => a.val.val) eq).trans (values 1)))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,fork,_⟩ := tg_issued_query_l J en ι issued
  have earlier : N₀.mem (ι.bound 22).val (ι.bound 19).val :=
    ((Formula.satisfies_conj_iff ..).mp (fork different)).1
  obtain ⟨m,r₀,hm,point,entry⟩ := index.select D request.sequence (ι.bound 22).val.val earlier
  obtain ⟨row,tuple,rest⟩ := request.views m r₀ entry
  exact ⟨m,r₀,row,hm,(values 22) ▸ point,entry,tuple,
    request.links m r₀ row entry tuple,row,tuple,rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 非空原请求的实际继续准备

非空标签按真实轮号选择档案。所选共同图同时搬运语言、事件、标签、
短图及根查询；根高度只用保存的交换方块和完整端点识别。源共尾度
给出严格极限切片，再由当前继续核与同一逆图直接生成原生后继工厂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际非空请求自动选档案并完成原继续工厂；所有图和环境只选取一次。 -/
theorem Tg_raw_request_d.prepare_l
    {ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N S w η C χ z k H r q c₀ n m T Q G E Λ d o : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N S w η C χ z k H r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N S) (qr : Rd_entry_d o c₀ Q)
    (ne : v 23 ≠ v 1) :
    let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N S request.origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let Nn := smdl_structure_l I (R := S) mn.2.1
    let Cn : Nn.Domain := ⟨C,request.context.member⟩
    ∃ m₀ r₀, ∃ row : Tg_raw_archive_row_d M.Domain,
      M.mem m₀ k ∧ Rd_entry_d m₀ (v 22) z ∧ Rd_entry_d m₀ r₀ H ∧
      Rt_tuple_d row.values_d r₀ ∧ row.link_d ⟨o,n,Q,G,Λ⟩ ∧
    ∃ _ : Smdl_d I row.c row.X row.R,
      Tg_saved_d I row.w row.X row.R row.η row.C row.L row.U row.q ∧
      Tg_saved_name_d I S₀ row.X row.R row.w row.U row.q row.p ∧
      Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ row.X row.R row.w row.C row.U row.q row.p ∧
      Tg_raw_cofinal_d I row.w row.X row.R row.L ∧
      Smap_d I ω c₀ row.c X₀ row.X row.p ∧
    ∃ zx, Rr_layer_d I ω row.X row.R row.w zx ∧
    ∃ vs : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q vs ∧ vs 16 = row.w ∧
    ∃ l V Γ g, ∃ common : Ic_common_d I row.X row.R N S row.L l row.U V Γ g,
      Tg_root_square_d D₀ row.p q g ∧ Rd_entry_d V C S ∧
    ∃ Δ b, (∀ x, M.mem x Δ ↔ M.mem x N ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I b Δ row.X ∧
      (∀ y, Rd_entry_d y row.U row.R ↔ ∃ x, M.mem x Δ ∧ Rd_entry_d x y b) ∧
      (∀ x y, Rd_entry_d x y b → ∀ a,
        Rd_entry_d a y row.R ↔ ∃ t, Rd_entry_d t x S ∧ Rd_entry_d t a b) ∧
      (∀ x y, Rd_entry_d x y b ↔ Rd_entry_d y x g) ∧
    ∃ nc : Nonempty {x : Nn.Domain // Nn.mem x Cn}, ∃ ι : Env (rt_model_l Cn nc) 46,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
    ∃ ν : Env (rt_model_l Cn nc) 29,
      Formula.satisfies ν tc_seed0_m ∧ Formula.satisfies ν tc_result0_m ∧
      ν.bound 3 = ι.bound 27 ∧ (ν.bound 28).val.val = χ ∧
      (∀ j : Fin 14, ν.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get j) =
        ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get j)) ∧
      (∀ j : Fin 5, Rd_entry_d
        ([⟨w,request.context.omega_mem⟩,(ν.bound 3).val,(ν.bound 1).val,(ν.bound 5).val,(ν.bound 7).val].get j).val
          (vs ([16,24,15,13,11].get j)) b) ∧
    ∃ ε : Env (rt_model_l Cn nc) 7,
      Formula.satisfies ε tg_reply_base0_m ∧ ε.bound 0 = ν.bound 0 ∧ ε.bound 3 = ν.bound 3 ∧
      Nn.mem (ε.bound 2).val (ν.bound 3).val ∧ Nn.mem (ε.bound 6).val (ν.bound 7).val ∧
      (∀ x : Nn.Domain, ¬ Nn.mem x (ε.bound 1).val) ∧
    ∃ s t a : (rt_model_l Cn nc).Domain,
      Tg_play_d I N S C (v 4) (v 3) (v 20) s.val.val ∧ Tg_graph_d (kp_pair_l hN) a.val s.val ∧
      Nn.MemberSubset a.val (ι.bound 26).val ∧ Nn.MemberSubset t.val (ι.bound 23).val ∧
      Rd_entry_d s.val.val (vs 40) b ∧ Rd_entry_d t.val.val (vs 41) b ∧
    ∃ γ Vγ tγ, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N S C q γ Vγ tγ ∧
      Rd_entry_d w Vγ S ∧ (∀ x, Rd_entry_d x γ S → Rd_entry_d x (ν.bound 1).val.val S) ∧
    ∃ α β : Nn.Domain, Rd_entry_d α.val l S ∧ Rd_entry_d β.val V S ∧ Nn.mem (ν.bound 1).val β ∧
      Nn.IsLimitOrdinal α ∧ V_d (kp_pair_l hN) α β ∧ Nn.MemberSubset α (ν.bound 8).val ∧
      Tg_continue_raw_d hZF ω c₀ X₀ R₀ row.c row.X row.R row.p Δ b N S z d mn.2.1 hN
        ⟨V,common.right_rank.2.1⟩
        ⟨w,request.context.omega_mem⟩ β (fun i => (ν.bound i).val) row.w row.η row.C row.L row.U row.q vs := by
  intro right ground hN Nn Cn
  have hn := ZFC.models_zf_l ground
  have fsN := request.context.finite_l mn.2.1 hN.1
  obtain ⟨m₀,r₀,row,hm₀,index,stored,tuple,link,entry⟩ := request.select_l (ZF.modelsKP hZF) hN.1 ne
  obtain ⟨mx,saved,⟨zx,nx⟩,name,baseOld,cofinal,l,V,Γ,g,common,upper,roots,view⟩ :=
    entry.read_l I tuple
  have left := tree.diagram.elementary o row.i row.p c₀ X₀ R₀ row.c row.X row.R
    link.2.2.1 qr link.2.1 root.model mx
  have sourceGround := (root.map_l hZF tree.omega mx left).native_l I hZF tree.omega
  have hx := ZFC.models_zf_l sourceGround
  have hX := ZF.modelsKP hx
  let Xn := smdl_structure_l I (R := row.R) mx.2.1
  let Ln : Xn.Domain := ⟨row.L,common.left_rank.1⟩
  let Un : Xn.Domain := ⟨row.U,common.left_rank.2.1⟩
  let wx : Xn.Domain := ⟨row.w,saved.context.omega_mem⟩
  let ln : Nn.Domain := ⟨l,common.right_rank.1⟩
  let Vn : Nn.Domain := ⟨V,common.right_rank.2.1⟩
  let wn : Nn.Domain := ⟨w,request.context.omega_mem⟩
  let ηn : Nn.Domain := ⟨η,request.context.height⟩
  let χn : Nn.Domain := ⟨χ,request.ordinal.1 0⟩
  obtain ⟨Xr,Rr,wr,Kr,zr,mr,_,numbers⟩ := (tree.sources o c₀ qr).objects
  obtain ⟨eqX,eqR⟩ := smdl_unique_l I mr root.model
  subst Xr Rr
  obtain ⟨ncN,ι,eq,issued,_⟩ := request.read_l I (ZF.modelsKP hZF) hN.1
  have hwι : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  have notEmpty : ι.bound 23 ≠ ι.bound 1 := fun h => ne
    ((eq 23).symm.trans ((congrArg (fun x => x.val.val) h).trans (eq 1)))
  have belowχ : Nn.mem χn (ι.bound 24).val :=
    Eq.mpr (congrArg (fun a => Rd_entry_d χ a S) (eq 24)) request.below
  have memberχ : Nn.mem χn Cn := fsN.transitive (ι.bound 24).val (ι.bound 24).property χn belowχ
  have lc : Nn.mem ln Cn := upper.elim
    (fun h => fsN.transitive χn memberχ ln h) (fun e => (show ln = χn from Subtype.ext e).symm ▸ memberχ)
  have ru : V_d (kp_pair_l hX) Ln Un := (rr_rank_native_l I mx.2.1 hX Ln Un).mp common.left_rank
  have rv : V_d (kp_pair_l hN) ln Vn := (rr_rank_native_l I mn.2.1 hN ln Vn).mp common.right_rank
  have rc : V_d (kp_pair_l hN) ηn Cn := (rr_rank_native_l I mn.2.1 hN ηn Cn).mp
    ((rr_rank_truth_l I).mpr request.context.rank)
  have lη := KP.v_ordinal_height_l hN rc (v_ordinal_l (kp_pair_l hN) rv) lc
  have inside : Nn.mem Vn Cn := (KP.v_compare_l hN rv rc
    ((v_ordinal_l (kp_pair_l hN) rc).transitive ln lη)).2 lη
  have limit := common.right_limit_native_l I hZF.1 mx mn hX hN
  have scope (x : Nn.Domain) (hxV : Nn.mem x Vn) : Nn.mem x Cn := fsN.transitive Vn inside x hxV
  have sourceBase := baseOld
  obtain ⟨γx,Vγx,sx,sourceSlice,omegaX,sourceLower⟩ := baseOld
  obtain ⟨γn,Vγn,sn,targetSlice,omegaN,_⟩ := request.slice
  obtain ⟨nc,ρ,code,round,hw,hτ,_,_,hu⟩ := saved.read_l I hZF.1
  let vs : Fin 54 → M.Domain := fun i => (ρ.bound i).val.val
  have fsX := saved.context.finite_l mx.2.1 hX.1
  have parts := tg_round_parts_l hX fsX nc ρ round
  let fields : Fin 10 → Term 54 := fun i => [.bound 16,.bound 15,.bound 24,.bound 14,.bound 13,
    .bound 12,.bound 6,.bound 5,.bound 4,.bound 3].get i
  let ε := Definitional.Env.substitute ρ fields
  have language : Formula.satisfies ε ee_language0_m := parts.language
  obtain ⟨_,_,nd,θ,points,hwθ,valid⟩ := common.language_native_l hZF tree.omega root.model mx mn hX hN
    left right root.ext numbers nx request.numbers saved.context request.context sourceSlice.context targetSlice.context
    (fun x hx => scope ⟨x,(mn.2.2.2 x V hx).1⟩ hx) nc ε hw hτ language
  obtain ⟨Δ,b,carrier,fk,image,pred,graph⟩ := common.reverse_native_l hZF mx hX
  have coords (i : Fin 10) : (ε.bound i).val.val = vs ([16,15,24,14,13,12,6,5,4,3].get i) := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))) i
  have huΓ := (common.carrier (vs 11)).mpr ⟨(ρ.bound 11).val.property,hu⟩
  obtain ⟨u',hu',iu⟩ := common.injection.1.2.2 (vs 11) huΓ
  let u : (rt_model_l Cn nd).Domain := ⟨⟨u',hu'⟩,scope ⟨u',hu'⟩ ((common.image u').mpr ⟨vs 11,huΓ,iu⟩)⟩
  have move (i : Fin 10) (h : Rd_entry_d (vs ([16,15,24,14,13,12,6,5,4,3].get i)) (vs 11) row.R) :
      Rd_entry_d (θ.bound i).val.val u' S := (common.pred (vs 11) u' iu _).mpr ⟨_,h,coords i ▸ points i⟩
  have elastic : Formula.satisfies (θ.push u)
      (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest) := by
    simp only [ee_elastic_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff]
    exact ⟨⟨move 6 parts.elastic.1.1,move 7 parts.elastic.1.2⟩,move 8 parts.elastic.2.1,move 9 parts.elastic.2.2⟩
  have omega : Xn.IsOmega (ρ.bound 16).val := (show (ρ.bound 16).val = wx from Subtype.ext hw).symm ▸
    nx.omega_l I (ZF.modelsKP hZF) tree.omega hX.1
  obtain ⟨a₀,a₁,t₀,ia₀,ia₁,it,ha₀,ha₁,ht,labels,first,last⟩ := common.labels_l hZF mx.2.1 mn.2.1 hX hN.1
    (ρ.bound 16).val (ρ.bound 22).val (ρ.bound 23).val (ρ.bound 24).val (ρ.bound 41).val
    (θ.bound 0).val (θ.bound 2).val omega parts.finite parts.first parts.last parts.labels (points 0) (points 2)
  let tn : (rt_model_l Cn nd).Domain := ⟨t₀,scope t₀ ht⟩
  let an : (rt_model_l Cn nd).Domain := ⟨a₀,scope a₀ ha₀⟩
  obtain ⟨trace,s_cur,is_cur,play_cur⟩ := view.read_l I hZF.1 code common.injection.1.1
    request.numbers.injection.1.1 ((eq 22).symm ▸ index) it (points 1) iu
  have trace' : Tg_trace_d I N S w C (ι.bound 4).val.val (ι.bound 1).val.val (ι.bound 2).val.val
      (ι.bound 22).val.val (ι.bound 20).val.val tn.val.val (θ.bound 1).val.val u.val.val := by
    simpa only [eq] using trace
  let sc : (rt_model_l Cn nd).Domain :=
    ⟨⟨s_cur,play_cur.elim fun mem _ => mem 4⟩,play_cur.member_l I⟩
  have shortGraph : Tg_graph_d (kp_pair_l hN) a₀ sc.val := rr_native_graph_l I hZF.1 mx.2.1 mn.2.1
    hX.1 (KP.exists_pair hX) hN.1 (KP.exists_pair hN) Un Vn
    (v_transitive_l (kp_pair_l hX) ru) (v_transitive_l (kp_pair_l hN) rv)
    common.carrier common.injection common.image common.pred (ρ.bound 22).val (ρ.bound 40).val
    a₀ sc.val ia₀ is_cur parts.graph
  -- 原 γ≤τ<L 在同一原生秩历史中给出 γ、Vγ 的所属，再识别当前根对象。
  have lang := language
  simp only [ee_language0_m,Formula.satisfies_conj_iff] at lang
  have limitτ := (rt_limit_l fsX.transitive nc hX (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp lang.2.1)
  have τL := KP.v_ordinal_height_l hX ru limitτ.1 hτ
  let γs : Xn.Domain := ⟨γx,sourceSlice.rank.1⟩
  let Vγs : Xn.Domain := ⟨Vγx,sourceSlice.rank.2.1⟩
  have rankγ := (rr_rank_native_l I mx.2.1 hX γs Vγs).mp sourceSlice.rank
  have limitγ : Xn.IsLimitOrdinal γs := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => γs)).mp sourceSlice.limit)
  have lower := sourceLower vs code
  have γL : Xn.mem γs Ln := ordinal_down_l hX limitγ.1 (v_ordinal_l (kp_pair_l hX) ru)
    (fun x hx => lower x.val hx) τL
  have γU := KP.v_ordinal_subset_l hX ru γs γL
  have VγU := (KP.v_compare_l hX rankγ ru ((v_ordinal_l (kp_pair_l hX) ru).transitive γs γL)).2 γL
  have objects := sourceSlice.common_objects_l I hZF.1 targetSlice common roots mn hN.1 right.1.1.1 γU VγU
  let ε₀ := ρ.reindex (fun i : Fin 7 => [16,17,23,24,2,1,0].get i)
  have hwX : (ρ.bound 16).val = wx := Subtype.ext hw
  have hwγ : Xn.mem (ρ.bound 16).val Vγs := hwX.symm ▸ (show Xn.mem wx Vγs from omegaX)
  have transγ := v_transitive_l (kp_pair_l hX) rankγ
  have hnγ := transγ (ρ.bound 16).val hwγ (ρ.bound 24).val parts.finite
  have low : ∀ i : Fin 4, Xn.mem (ε₀.bound (i.castAdd 3)).val Vγs :=
    Fin.cases hwγ (Fin.cases (transγ _ hwγ _ parts.empty_omega)
      (Fin.cases (transγ _ hnγ _ parts.last.predecessor_mem) (Fin.cases hnγ (fun i => Fin.elim0 i))))
  have lowAll := tg_reply_base_scope_l hX (nx.omega_l I (ZF.modelsKP hZF) tree.omega hX.1)
    fsX nc ε₀ rankγ limitγ hwX
      (Eq.mp (congrArg (fun a => Xn.mem (ρ.bound 24).val a) hwX) parts.finite) low parts.reply
  have reverseRoots := sourceSlice.inverse_square_l I hZF.1 roots common.injection graph
  obtain ⟨ε₁,backPoints,reply⟩ := targetSlice.back_l hZF sourceSlice reverseRoots tree.omega root.model mn mx
    right left fsN.transitive fsX.transitive nd nc tg_reply_base0_m tg_reply_base0_closed_l ε₀ lowAll parts.reply
  have replyPoints i : Rd_entry_d (ε₀.bound i).val.val (ε₁.bound i).val.val g :=
    (graph _ _).mp (backPoints i)
  have replyω : ε₁.bound 0 = θ.bound 0 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _ (replyPoints 0) (points 0)))
  have replyN : ε₁.bound 3 = θ.bound 2 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _ (replyPoints 3) (points 2)))
  have replyLt : Nn.mem (ε₁.bound 2).val (θ.bound 2).val :=
    (common.pred _ _ (points 2) _).mpr ⟨_,parts.last.predecessor_mem,replyPoints 2⟩
  have replyMem : Nn.mem (ε₁.bound 6).val u.val :=
    (common.pred _ _ iu _).mpr ⟨_,parts.height,replyPoints 6⟩
  have replyEmpty (x : Nn.Domain) (hx₀ : Nn.mem x (ε₁.bound 1).val) : False := by
    obtain ⟨y,hy,yx⟩ := (common.pred _ _ (replyPoints 1) x.val).mp hx₀
    exact parts.empty ⟨y,((common.carrier y).mp (common.injection.1.input_mem_of_pairMember yx)).1⟩ hy
  -- 同一原事件进入继续核，历史界就是当前请求保存的 χ。
  have limitC : Nn.IsLimitOrdinal ηn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ηn)).mp request.context.limit)
  obtain ⟨κδ,regular⟩ := tg_issued_control_l hN rc limitC fsN nd ι issued
  have χδ : Nn.mem χn (ι.bound 5).val := regular.isCardinal.1.transitive (ι.bound 24).val κδ χn belowχ
  obtain ⟨ν,seed,result,oldEq,typeEq,arity,newEq,labelsSub,boundEq⟩ := request.context.continue_native_l hZF
    mn.2.1 hn nd ι issued hwι notEmpty θ valid hwθ u tn ⟨χn,memberχ⟩ a₀ a₁ elastic labels first last trace' χδ
  have currentLabels := (rt_fn_l fsN.transitive nd hN.1 (ι.bound 26) (ι.bound 0) (ι.bound 23)).mp
    ((tg_issued_sat_l (rt_pair_l fsN.transitive nd hN.1 fsN.pair)
      (rt_model_ext_l hN.1 fsN.transitive nd) ι).mp issued).labels
  have shortDomain : Nn.MemberSubset a₀ (ι.bound 26).val := by
    intro x hx
    obtain ⟨y,_,p,pair,hp⟩ := labels.2.1 x hx
    exact (currentLabels.bound_l ⟨p,pair,labelsSub p hp⟩).1
  have candidateLower x (hx : Rd_entry_d x γn S) : Rd_entry_d x (ν.bound 1).val.val S := by
    obtain ⟨y,hy,yx⟩ := (common.pred γx γn objects.1 x).mp hx
    have h := (common.pred _ _ (points 1) x).mpr ⟨y,lower y hy,yx⟩
    exact Eq.mpr (congrArg (fun a => Rd_entry_d x a.val.val S) (oldEq 1)) h
  -- 只消费源支撑的不可数共尾度，严格切片为同一候选的 τ+ω。
  obtain ⟨cf,cof,uncountable⟩ := cofinal.native_l I hZF.1 mx.2.1 (kp_pair_l hX) hX.1 wx Ln
  obtain ⟨α,β,cutHeight,cutLayer,cutPoint,cutLimit,cutRank,least⟩ := common.limit_cut_l (ZF.modelsKP hZF)
    mx.2.1 mn.2.1 hx hN wx cf (ρ.bound 15).val (θ.bound 1).val
    (nx.omega_l I (ZF.modelsKP hZF) tree.omega hX.1) cof uncountable τL (points 1)
  have facts := seed
  simp only [tc_seed0_m,Formula.satisfies_conj_iff] at facts
  obtain ⟨_,_,_,limitν,_,_,_,_,exceedsν,_⟩ := facts
  have limitν := (rt_limit_l fsN.transitive nd hN (ν.bound 8)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limitν)
  have belowν : Nn.mem (θ.bound 1).val (ν.bound 8).val :=
    Eq.mp (congrArg (fun x => Nn.mem x (ν.bound 8).val) (congrArg Subtype.val (oldEq 1)))
      ((Formula.satisfies_conj_iff ..).mp exceedsν).1
  have candidateβ : Nn.mem (ν.bound 1).val β :=
    Eq.mpr (congrArg (fun x => Nn.mem x β) (congrArg Subtype.val (oldEq 1))) cutPoint
  have small : Rr_small_d I row.X row.R row.U := by
    intro B hB _
    let Bn : Xn.Domain := ⟨B,hB⟩
    obtain ⟨μ,f,ord,fn,onto⟩ := ZFC.ordinal_enum_l sourceGround (kp_pair_l hX) Bn
    obtain ⟨h,inj,_⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hx (kp_pair_l hX) ord fn onto
    apply (rf_small_native_l I mx.2.1 Bn).mpr
    simp only [sc_small_m,Formula.satisfies_exists_iff]
    exact ⟨μ,h,(sc_index_sat_l hX _ (.bound 1) (.bound 2) .newest).mpr (Sc_index_d.of_injection_l hX ord inj)⟩
  have hwν : (ν.bound 0).val = wn := Subtype.ext ((congrArg (fun x => x.val.val) (oldEq 0)).trans hwθ)
  have oldLinks : ∀ i : Fin 5,
      Rd_entry_d ([wn,(ν.bound 3).val,(ν.bound 1).val,(ν.bound 5).val,(ν.bound 7).val].get i).val
        (vs ([16,24,15,13,11].get i)) b := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))
    · exact Eq.mp (congrArg (fun x => Rd_entry_d x (vs 16) b) hwθ) ((graph _ _).mpr (points 0))
    · exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (vs 24) b) (oldEq 2)) ((graph _ _).mpr (points 2))
    · exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (vs 15) b) (oldEq 1)) ((graph _ _).mpr (points 1))
    · exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (vs 13) b) (oldEq 4)) ((graph _ _).mpr (points 4))
    · exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (vs 11) b) typeEq) ((graph _ _).mpr iu)
  have regularν : Nn.IsRegularCardinal (kp_pair_l hN) (ν.bound 2).val :=
    Eq.mpr (congrArg (fun x => Nn.IsRegularCardinal (kp_pair_l hN) x)
      (congrArg Subtype.val (newEq 1))) regular
  have raw := Tg_context_d.raw_continue_l hZFC tree.omega mn.2.1 ground
    Vn wn ηn Cn α β ln nd ν vs request.context mn root mx left right numbers sourceSlice.context targetSlice.context
    saved code oldLinks request.numbers rv limit carrier fk image pred common.left_closed small
    cutLayer candidateβ cutLimit cutRank (least _ limitν belowν) hwν regularν seed result
  exact ⟨m₀,r₀,row,hm₀,index,stored,tuple,link,mx,saved,name,sourceBase,cofinal,left,zx,nx,vs,code,hw,l,V,Γ,g,common,roots,inside,
    Δ,b,carrier,fk,image,pred,graph,nd,ι,eq,issued,ν,seed,result,arity,congrArg (fun x => x.val.val) boundEq,
    newEq,oldLinks,ε₁,reply,replyω.trans (oldEq 0).symm,replyN.trans (oldEq 2).symm,
    Eq.mpr (congrArg (fun x => Nn.mem (ε₁.bound 2).val x.val) (oldEq 2)) replyLt,
    Eq.mpr (congrArg (fun x => Nn.mem (ε₁.bound 6).val x.val) typeEq) replyMem,replyEmpty,
    sc,tn,an,play_cur,shortGraph,shortDomain,labelsSub,(graph _ _).mpr is_cur,(graph _ _).mpr it,
    γn,Vγn,sn,targetSlice,omegaN,candidateLower,α,β,cutHeight,cutLayer,candidateβ,cutLimit,cutRank,
    least _ limitν belowν,raw⟩

end YesMetaZFC.SetTheory.LargeCardinal
