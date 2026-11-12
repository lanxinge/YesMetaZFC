import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Game.IssuedReset
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.CumulativeRelativeRead
import YesMetaZFC.SetTheory.CumulativeOrdinalHeight
import YesMetaZFC.SetTheory.LargeCardinal.Game.ResetResult
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalPad
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyExtend
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype

/-! # 目标表中的原查询回到完整回答层核验

低层只运输参数，整句查询性质沿共同根在两份反射层之间运输。
原回答层的已证比较规则给出三条成员判断，再沿同一完整池图返回目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.reply_members_l
    {ω γ B r Z Q x X R y Y S π σ C₀ L l U V Γ k H f K g D₀ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ k)
    (hω : M.IsOmega ω) (mz : Smdl_d I r Z Q) (mx : Smdl_d I x X R) (my : Smdl_d I y Y S)
    (j : Smap_d I ω r x Z X π) (j' : Smap_d I ω r y Z Y σ)
    (ex : Rf_ext_d I X R) (ey : Rf_ext_d I Y S)
    (anchor : Tg_anchor_d I γ B X R π) (target : Tg_anchor_d I γ B Y S σ)
    (source : Rr_layer_d I B X R H f) (next : Rr_layer_d I B Y S K g)
    (trans : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet ⟨U,common.left_rank.2.1⟩)
    (inside : Rd_entry_d H U R)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (nc : Nonempty {a : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val π) (iD : Rd_entry_d C₀ D.val σ)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models ZF)
    (v a w : (smdl_structure_l I (R := S) my.2.1).Domain)
    (omega : (smdl_structure_l I (R := S) my.2.1).IsOmega v)
    (fs : Fs_read_d v D)
    (rank : V_d (kp_pair_l (ZF.modelsKP hY)) a ⟨K,next.member⟩)
    (limit : (smdl_structure_l I (R := S) my.2.1).IsLimitOrdinal a)
    (kernel : Tg_kernel_d (rt_model_l C nc))
    (ρ : Env (rt_model_l C nc) 54) (round : Formula.satisfies ρ tg_round0_m)
    (θ : Env (rt_model_l D nd) 7) (hw : (θ.bound 0).val = v)
    (hn : (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 3).val v)
    (low : ∀ i : Fin 4, Rd_entry_d (θ.bound (i.castAdd 3)).val.val K S)
    (base : Formula.satisfies θ tg_reply_base0_m)
    (ft : M.IsSetInjectionFromTo I t D₀ Y) (restrict : M.IsRestrictionOf I k t Γ)
    (pred : ∀ x E, Rd_entry_d x E t → ∀ y, Rd_entry_d y E S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t)
    (points : ∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
      (θ.bound (i.castAdd 3)).val.val t)
    (type : Rd_entry_d (ρ.bound 11).val.val w.val t) :
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 4).val w ∧
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 5).val w ∧
    (smdl_structure_l I (R := S) my.2.1).mem (θ.bound 6).val w := by
  have all := tg_reply_base_scope_l (ZF.modelsKP hY) omega fs nd θ rank limit hw hn low base
  obtain ⟨ψ,images,valid⟩ := common.anchor_back_l hZF hω mz mx my j j' ex ey anchor target
    source next trans inside C D ct fs.transitive nc nd iC iD
    tg_reply_base0_m tg_reply_base0_closed_l θ all base
  have same (i : Fin 4) : ψ.bound (i.castAdd 3) = ρ.bound ([16,17,23,24].get i) :=
    Subtype.ext (Subtype.ext (ft.2 _ _ _ ((restrict.2 _ _).mp (images (i.castAdd 3))).2 (points i)))
  have compare := kernel.reply_queries_l ρ round
  simp only [tg_reply_compare0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at compare
  have members := compare (ψ.bound 4) (ψ.bound 5) (ψ.bound 6) (by
    unfold tg_reply_base_m
    apply (Formula.satisfies_bind ..).mpr
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (ρ := ψ) (η := _) ?_).mp valid
    funext i
    exact Fin.cases (same 0) (Fin.cases (same 1) (Fin.cases (same 2) (Fin.cases (same 3)
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))) i)
  have carry i (hi : (smdl_structure_l I (R := R) mx.2.1).mem (ψ.bound i).val (ρ.bound 11).val) :
      (smdl_structure_l I (R := S) my.2.1).mem (θ.bound i).val w :=
    (pred _ _ type _).mpr ⟨_,hi,((restrict.2 _ _).mp (images i)).2⟩
  exact ⟨carry 4 members.1,carry 5 members.2.1,carry 6 members.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 首次原生重置的实际字母与目标前缀

首请求自身给出字母表属于原生 Vκ。原工厂的临界点坐标与它相同，
故同一次字母满像可以直接供目标前缀解码使用；没有工作复制历史或背景低层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 首轮的真实语言、同一次自施加工厂和目标请求共同构造完整前缀。 -/
theorem Er_rank_cut_at_d.first_reset_prefix_l
    {ω c₀ X₀ R₀ d N R q Γ k z : M.Domain}
    (mn : Smdl_d I d N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    {U₀ w ξ ℓ e β X' K' jN δ : (smdl_structure_l I (R := R) mn.2.1).Domain}
    {Ls Js Os Zs As ps Ts Vs rs o P W j q' p₀ : M.Domain}
    (data : Er_rank_cut_at_d hZF ω c₀ X₀ R₀ d N R q Γ k N R z d mn.2.1 hN U₀ w ξ ℓ e β X' K' jN
      Ls Js Os Zs As ps Ts Vs rs o P W j q' p₀)
    (rankU : V_d (kp_pair_l hN) δ U₀)
    (diagonal : ∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y)
    {η C : M.Domain} (context : Tg_context_d I w.val N R η C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (empty : ι.bound 23 = ι.bound 1)
    (zero : ι.bound 19 = ι.bound 1) (critical : ξ = (ι.bound 24).val)
    (target : Smdl_d I o P W) (ext : Rf_ext_d I P W)
    {w' η' C' z' n : M.Domain} (current : Tg_context_d I w' P W η' C')
    (nd : Nonempty {x : (smdl_structure_l I (R := W) target.2.1).Domain //
      (smdl_structure_l I (R := W) target.2.1).mem x ⟨C',current.member⟩})
    (ι' : Env (rt_model_l (M := smdl_structure_l I (R := W) target.2.1) ⟨C',current.member⟩ nd) 46)
    (issued' : Formula.satisfies ι' tg_issued0_m)
    (images : ∀ i, Rd_entry_d (ι.bound i).val.val (ι'.bound i).val.val j)
    (numbers : Rr_layer_d I ω P W w' z') (point : Rd_entry_d n (ι'.bound 19).val.val z') :
    ∃ A B t f,
      (∀ x, M.mem x A ↔ M.mem x N ∧ Rd_entry_d x (ι.bound 6).val.val R) ∧
      (∀ x, M.mem x B ↔ M.mem x P ∧ Rd_entry_d x (ι'.bound 6).val.val W) ∧
      M.IsSetBijectionFromTo I t A B ∧ M.IsRestrictionOf I t j A ∧
      Tg_prefix_d I n A P W C' (ι'.bound 4).val.val (ι'.bound 3).val.val (ι'.bound 20).val.val z' j f := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  let J := kp_pair_l hN
  have fs := context.finite_l mn.2.1 hN.1
  let K := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ex := rt_model_ext_l hN.1 fs.transitive nc
  have state := (tg_issued_sat_l K ex ι).mp issued
  obtain ⟨ε,seed,_,_,_,_,_,_,move,_,_,letters,_⟩ := tg_issued_reset_l K ex ι issued empty
  have eqκ : (ε.bound 5).val = ξ :=
    (congrArg Subtype.val (move.unique_l state.move).2.2.1).trans critical.symm
  have facts := seed
  simp only [tg_seed0_m,tg_seed_m,Formula.satisfies_conj_iff] at facts
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,language,_⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0,.bound 5,.bound 7,.bound 14,.bound 15,
    .bound 16,.bound 27,.bound 28,.bound 29,.bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m :=
    (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m,Formula.satisfies_conj_iff] at language
  have inner : Vr_d (⟨C,context.member⟩ : N₀.Domain) (ε.bound 5).val (ε.bound 14).val :=
    (vr_sat_l hN fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have rankC := (rr_rank_native_l I mn.2.1 hN ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have rank₀ : V_d J (ε.bound 5).val (ε.bound 14).val :=
    inner.absolute_l hN fs.transitive (ε.bound 14).property
      (fun A B hA sub => v_subset_mem_l J rankC (A := A) (B := B) hA sub)
  have rank : V_d J ξ (ε.bound 14).val :=
    Eq.mp (congrArg (fun α : N₀.Domain => V_d J α (ε.bound 14).val) eqκ) rank₀
  have letter : N₀.mem (ι.bound 6).val (ε.bound 14).val := letters zero
  have used := data
  obtain ⟨_,_,carrier,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,agreement,_⟩ := used
  have memberκ : N₀.mem ξ U₀ := ((carrier ξ.val).mp agreement.critical).2
  have heightκ := KP.v_ordinal_height_l hN rankU (v_ordinal_l J rank) memberκ
  have below := (v_ordinal_l J rankU).transitive ξ heightκ
  have hA := (KP.v_compare_l hN rank rankU below).1 (ι.bound 6).val letter
  have iA := (diagonal (ι.bound 6).val.val (ι.bound 6).val.val).mpr
    ⟨(carrier _).mpr ⟨(ι.bound 6).val.property,hA⟩,rfl⟩
  obtain ⟨A,B,t,source,range,bijection,rest,_⟩ :=
    data.alphabet_l hZF ξ (ε.bound 14).val (ι.bound 6).val rank letter (fun _ h => h) iA (images 6)
  obtain ⟨f,play⟩ := current.prefix_l hZF target.2.1 (ext.native_l I target.2.1) nd ι' issued'
    numbers point range bijection rest
  exact ⟨A,B,t,f,source,range,bijection,rest,play⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 空标签请求在原模型中生成重置轮

实际请求调用当前反射核；回答、存档及扩展器保留同一批见证。原树与复制
历史先同步插入恒等边，再将同一扩展器施加到原偶数前驱并完成工作复制。
回答域的实际极限秩切片提供施加范围，两次延伸保留同一原根。
同一完整代表池随后搬运规则 (7)，原请求在目标反射层解码；原回答域与
当前查询表的域由完整秩历史和有限池唯一性识别。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.reset_native_l
    {ω c₀ X₀ R₀ n m T Q G E Λ H ST QT GT N R B σ u U β d o q C₀ S₀ γ Bγ w η C z χ : M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT) (hn : M.mem n ω) (hm : M.SuccessorOf m n)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (an : Ic_at_d H n N B σ u U β) (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N R)
    (qr : Rd_entry_d o c₀ Q) (origin : It_map_d G o n q)
    (context : Tg_context_d I w N R η C) (basis : Tg_basis_d I γ Bγ C₀ w N R C q)
    (numbers : Rr_layer_d I ω N R w z) (bound : Ic_bound_d I H Q N R σ n χ)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val.val = w)
    (treeName : Rd_entry_d S₀ (ι.bound 7).val.val q)
    (lowerγ : It_lower_d I γ N R (ι.bound 24).val.val)
    (empty : ι.bound 23 = ι.bound 1) (below : Rd_entry_d χ (ι.bound 24).val.val R) :
    let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N R origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    Tg_reset_native_d hZF ω c₀ X₀ R₀ n m T Q G E Λ H QT GT N R B σ u U β d o q C₀ S₀ γ Bγ w η C z χ
      mn hN context nc ι := by
  intro right ground hN
  let Nn := smdl_structure_l I (R := R) mn.2.1
  have anchor := basis.anchor_l I
  obtain ⟨image,aγ,Vγ,sγ,tγ,heightg,layerg,rankg,limitg₀,omegaG,fixedg⟩ := basis
  have fs := context.finite_l mn.2.1 hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  obtain ⟨ε,seed,head,length_zero,hb,zero,tag,graph,_,_,_,_,matched⟩ := tg_issued_reset_l J ext ι issued empty
  obtain ⟨v,round⟩ := tg_successor_read_l ε seed ((context.kernel_l mn.2.1 nc).renew_l ε seed)
  let ρ := tg_round_env_d ε v
  have request : Tg_request_d Eq (fun i => (ι.bound i).val.val) (fun i => (ρ.bound i).val.val) :=
    fun i => congrArg (fun x => x.val.val) (matched v i)
  have eκ : (ρ.bound 21).val = (ι.bound 24).val := congrArg Subtype.val (matched v 14)
  have eχ : (ρ.bound 39).val = (ι.bound 24).val := (congrArg Subtype.val hb).trans eκ
  have ew : (ρ.bound 16).val.val = w := (congrArg (fun x => x.val.val) (matched v 0)).trans hw
  -- 同一回答的支撑和内部超幂一并保存；历史界严格低于这个实际支撑。
  obtain ⟨L,W,r,saved,code,high,X,K,R₁,F,c₁,d₁,Y,S,j₁,κ₁,U₁,D₁,u₁,data⟩ :=
    context.save_round_native_l hZF mn.2.1 ground
      (numbers.omega_l I (ZF.modelsKP hZF) tree.omega hN.1) nc ρ round ew
  have limitL : Nn.IsLimitOrdinal L := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => L)).mp saved.limit)
  have above : Rd_entry_d χ L.val R := limitL.1.transitive (ι.bound 24).val (eχ ▸ high)
    ⟨χ,bound.ordinal.1 0⟩ below
  have body := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at body
  have growth : Nn.mem (ι.bound 24).val (ρ.bound 15).val := eχ ▸ body.1
  have lower a (lo : It_lower_d I a N R (ι.bound 24).val.val) :
      It_lower_d I a N R (ρ.bound 15).val.val := by
    obtain ⟨b,s,layer,down⟩ := lo
    exact ⟨b,s,layer,fun x hx => (limitL.1.mem data.2.2.2.2.1).transitive
      (ι.bound 24).val growth ⟨x,(mn.2.2.2 x b hx).1⟩ (down x hx)⟩
  -- 原恒等边及复制恒等边使用同一个后继长度；根图逐点保留旧像。
  obtain ⟨θ,T₁,Q₁,G₁,E₁,d',j,H₁,ST₁,QT₁,GT₁,succ,next,extension,old,node,edge,identity,
    noMove,lv,history,hh,hq,hg,rows⟩ := hist.original_pad_l hZF tree hm levels
  have eq := tree.diagram.model_function.2 n d' d old qn
  subst d'
  obtain ⟨row,bd⟩ := rows N R B σ u U β χ an bound
  have oldRoot := (extension.2.2.2.1 o n q hm.predecessor_mem).mpr origin
  have pad := next.diagram.elementary n m j d N R d N R edge (extension.2.2.1 n d qn) node mn mn
  obtain ⟨q₁,root₁⟩ := next.diagram.map_l hZF
    ((extension.2.1 o m).mpr (Or.inr ⟨rfl,Or.inr (tree.diagram.map_bound_l hZF origin)⟩))
  have keep x y (point : Rd_entry_d x y q) : Rd_entry_d x y q₁ := by
    obtain ⟨v,_,hv⟩ := pad.1.1.2.2 y (right.1.1.output_mem_of_pairMember point)
    have fixed : Rd_entry_d y y j := (identity y v hv).symm ▸ hv
    exact next.diagram.comp o n m q j q₁ oldRoot edge root₁ x y y point fixed
  have anchor₁ : Tg_anchor_d I γ Bγ N R q₁ := by
    obtain ⟨a,V,s,t,ha,hV,rank,fixed⟩ := anchor
    exact ⟨a,V,s,t,ha,hV,rank,fun x y hxy => keep x y (fixed x y hxy)⟩
  refine ⟨θ,T₁,Q₁,G₁,E₁,j,H₁,ST₁,QT₁,GT₁,q₁,succ,next,extension,node,edge,identity,noMove,
    lv,history,hh,hq,hg,row,bd,root₁,keep,keep C₀ C image,anchor₁,ρ,round,request,
    congrArg Subtype.val eχ,congrArg (fun x => x.val.val) length_zero,
    congrArg (fun x => x.val.val) zero,congrArg (fun x => x.val.val) tag,
    congrArg (fun x => x.val.val) graph,congrArg (fun x => x.val.val) (head 3),
    congrArg (fun x => x.val.val) (head 4),lower,L,W,r,saved,code,above,
    X,K,R₁,F,c₁,d₁,Y,S,j₁,κ₁,U₁,D₁,u₁,data,?_⟩
  -- 新回答域本身是 κ 以上、L 以下的极限高度，直接用其实际秩层作切片。
  have native := ZFC.models_zf_l ground
  have language := body.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limitτ := (rt_limit_l fs.transitive nc hN (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have rankC := (rr_rank_native_l I mn.2.1 hN ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have limitC : Nn.IsLimitOrdinal ⟨η,context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ⟨η,context.height⟩)).mp context.limit)
  have height := (tg_round_control_l hN rankC limitC fs nc ρ round).2.isLimitOrdinal
  have imageData := data
  obtain ⟨rankX,source,hLδ,hκL,hτL,rW,hQW,loc,card,strong,mx,my,ultra,crit,lb,_,iU,iD,iu,_,answer⟩ := imageData
  obtain ⟨V,Γ,k,rankV,carrier,graph,small,cut⟩ := loc.raw_self_l hZFC tree.omega mn.2.1 ground
    ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F (ρ.bound 15).val X K R₁ (ρ.bound 18).val
    c₁ d₁ Y S j₁ κ₁ mn root right numbers rankX height limitτ (eκ.symm ▸ growth) hτL hLδ
    source mx my ultra card strong crit.image lb
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,P,R₂,j₂,q₂,p₂,cert⟩ := cut
  refine ⟨V,Γ,k,Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,P,R₂,j₂,q₂,p₂,rankV,carrier,graph,cert,?_⟩
  have used := cert
  obtain ⟨finite,closed,_,hVX,hVX',transV,products,length,raw,diagram,limit,mp,_,_,_,embed,
    rootMap,constants,agreement,payload,_,certificate,rootGraph,Uc,rankUc,readUc,_,_,l,Vc,Dc,t,
    common,_,_,tail⟩ := used
  obtain ⟨Pκ,rankP,lowSquare,κ₀,bκ,κ',hκ₀,hbκ,hκ',belowL,boundκ,neκ,memκ,ordκ,ord₀,ord₁,
    fixκ,lowerImages,anchors,rest⟩ := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨w₀,w₂,z₀,z₁,hww₀,hww₂,omegaEdge,_,newNumbers,_,_,_,_,_,_,_,_,_,_,_,pool,build⟩ := rest
  obtain ⟨A₀,Q₀,B₀,e₀,Dp,Bp,s₁,v₁,t₀,pool,dc,bc,_,_,_,_,ft,restrict,endpoint,layer,present,prepare,
    bV,HV,_,hbHV,fullPool,predPool,commute,_⟩ := pool
  obtain ⟨_,_,_,extend⟩ := build.2 root
  have parentNode := extension.2.2.1 n d qn
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,critical₂⟩ :=
    extend θ m T₁ Q₁ G₁ E₁ n o next succ node parentNode oldRoot
  obtain ⟨Λ₂,lf₂,levels₂,entries₂,hist₂⟩ :=
    history.original_extend_l hZF next succ lf lv tree₂ extension₂ move₂ payload
  have bound₂ := history.bound_extend_l hZF next tree₂ extension₂ succ.predecessor_mem bd
  have parent : Ic_at_d H₁ n N B σ u U β := by
    obtain ⟨r,⟨p,pair,hp⟩,cell⟩ := an
    exact ⟨r,⟨p,pair,hh p hp⟩,cell⟩
  -- 两端是恒等延伸的同一复制行；Vδ 的像自动成为两侧同一个工作秩段。
  obtain ⟨d',hd',_,own⟩ := hist.row_l hZF an
  have eq := tree.diagram.model_function.2 n d' d hd' qn
  subst d'
  obtain ⟨R',RB,RU,bB,KB,KU,mn',mb,mu,sourceB,outer,hBU,rBU,limB,map⟩ := own
  have eq := (smdl_unique_l I mn' mn).2
  subst R'
  obtain ⟨δw,hδB,iδ⟩ := map.1.1.2.2 (ρ.bound 18).val.val (ρ.bound 18).val.property
  obtain ⟨Dw,hDB,iX⟩ := map.1.1.2.2 X.val X.property
  have nativeRank := (rr_rank_native_l I mn.2.1 hN (ρ.bound 18).val X).mpr rankX
  have movedRank := ((rr_rank_truth_l I).mp nativeRank).map_l I hZF tree.omega mn mb.1 map
    (w := Fin.cases Dw (fun _ : Fin 1 => δw)) (by simp -implicitDefEqProofs)
    (Fin.cases iX (fun _ => iδ))
  have workRank := (rr_rank_mem_l I (ZF.modelsKP hZF) mb sourceB.transitive hδB hDB).mp
    ((rr_rank_truth_l I).mpr movedRank)
  have nativeLimit := (rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
    (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (ρ.bound 18).val)).mpr
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr height)
  have movedLimit := nativeLimit.map_l I hZF tree.omega mn mb.1 map
    (w := fun _ : Fin 1 => δw) (by simp -implicitDefEqProofs) (fun _ => iδ)
  let nb : Nonempty {x // M.mem x B} := ⟨⟨δw,hδB⟩⟩
  let ζ : Env (rt_model_l B nb) 1 := ⟨fun _ => ⟨δw,hδB⟩,fun _ => ⟨δw,hδB⟩⟩
  have limitw := (rt_limit_l sourceB.transitive nb (ZF.modelsKP hZF) ⟨δw,hδB⟩).mp
    ((Formula.satisfies_isLimitOrdinal_iff ζ .newest).mp
      ((smem_formula_l I mb nb _ ζ).mpr movedLimit.2))
  have square x x' y (hx : Rd_entry_d x x' σ) (hy : Rd_entry_d x y k) : Rd_entry_d y x' σ :=
    ((graph x y).mp hy).2 ▸ hx
  have parentImage y : Rd_entry_d y X.val R ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k := by
    constructor
    · intro hy
      have hyΓ := (carrier y).mpr ⟨(mn.2.2.2 y X.val hy).1,hy⟩
      exact ⟨y,hyΓ,(graph y y).mpr ⟨hyΓ,rfl⟩⟩
    · rintro ⟨x,hx,hxy⟩
      exact ((graph x y).mp hxy).2 ▸ ((carrier x).mp hx).2
  obtain ⟨κw,_,iκ⟩ := map.1.1.2.2 (ρ.bound 21).val.val (ρ.bound 21).val.property
  obtain ⟨Lw,_,iL⟩ := map.1.1.2.2 L.val L.property
  obtain ⟨Fw,_,iF⟩ := map.1.1.2.2 F.val F.property
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hnθ := (next.diagram.model_domain n).mpr ⟨d,parentNode⟩
  have oldOrder i : Rd_entry_d i n T₂ ↔ Rd_entry_d i n T₁ :=
    (extension₂.2.1 i n).trans ⟨fun h => h.elim id (fun e => (ir θ (e.1 ▸ hnθ)).elim),Or.inl⟩
  have predecessor : It_pred_d T₂ n θ := by
    refine ⟨hnθ,fun i => (extension₂.2.1 i θ).trans ?_⟩
    exact ⟨fun h => h.elim (fun h => (ir θ (next.diagram.order.bound i θ h).2).elim)
      (fun h => h.2.imp_right (oldOrder i).mpr),
      fun h => Or.inr ⟨rfl,h.imp_right (oldOrder i).mp⟩⟩
  obtain ⟨m',sm,hm'⟩ := tree.omega.1.2 n hn
  have hmω : M.mem m ω := (hm.eq hZF.1 sm).symm ▸ hm'
  obtain ⟨Y₂,v₂,B₂,β₂,σ₂,r₂,H₂,ST₂,QT₂,GT₂,succ₂,result,rows₂,codes₂,maps₂,last,bound₃,adjacent⟩ :=
    hist₂.copy_step_l hZFC mn mn hN ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F X (ρ.bound 18).val
      K R₁ X V A₀ Q₀ B₀ e₀ numbers source rankX height loc
      (it_owner_l I mn hN ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F
        (ρ.bound 18).val X K R₁ numbers rankX height source loc card strong)
      iκ iL iF finite closed carrier
      iX hDB workRank workRank limitw agreement square parentImage small hVX hVX' transV products
      pool dc bc (fn0_of_function_l (ZF.modelsKP hZF) ft.1) present prepare length raw diagram limit mp
      (fn0_of_function_l (ZF.modelsKP hZF) embed.1.1) constants common restrict endpoint layer
      tree₂ hmω succ predecessor (extension₂.2.2.1 n d parentNode) (extension₂.2.2.1 m d node)
      node₂ edge₂ move₂ payload ((entries₂ m L.val).mpr (Or.inr ⟨rfl,rfl⟩)) lf₂ parent row bound₂ above
  have eq := succ₂.eq hZF.1 extension₂.1
  subst r₂
  have sourceLower : It_lower_d I γ N R (ρ.bound 21).val.val :=
    Eq.mp (congrArg (fun a => It_lower_d I γ N R a) (congrArg Subtype.val eκ).symm) lowerγ
  have critical (old : It_critical_bound_d I γ Q E) : It_critical_bound_d I γ Q₂ E₂ := by
    apply critical₂ γ sourceLower
    apply extension.critical_bound_l I old
    rintro p κ L F hp ⟨s,⟨a,b,_,_,pair⟩,_⟩
    exact (noMove p hp a ((pair a).mpr (Or.inl rfl))).elim
  refine ⟨θ₂,T₂,Q₂,G₂,E₂,Λ₂,H₂,ST₂,QT₂,GT₂,v₂,Y₂,β₂,B₂,σ₂,l,Lw,Uc.val,Vc,Dc,t,
    tree₂,extension₂,critical,node₂,edge₂,move₂,root₂,lf₂,levels₂,entries₂,result,rows₂,codes₂,maps₂,last,bound₃,adjacent,?_⟩
  refine ⟨A₀,Q₀,B₀,e₀,Dp,Bp,t₀,pool,dc,bc,ft,present,restrict,endpoint,layer,mp,?_⟩
  let Pn := smdl_structure_l I (R := R₂) mp.2.1
  have targetZF := ZFC.models_zf_l ((certificate root).native_l I hZF tree.omega)
  have hP := ZF.modelsKP targetZF
  -- 同一完整代表池搬运规则 (7)，包括其投影和子类型存在见证。
  have hκV := ZF.v_ordinal_mem_l (kp_pair_l hN) native rankV (eκ.symm ▸ growth)
  obtain ⟨hU,hD,hu,hl,hn',hk,labels,labelLow,digits⟩ := tg_round_members_l native
    source.omega rankC fs nc ρ (Subtype.ext ew) rankV limitτ hκV round
  have hWB : Nn.mem W B₀ := (ZF.v_unique_l (kp_pair_l hN) native rankUc rW) ▸
    ((bc Uc.val).mp (ft.1.input_mem_of_pairMember layer)).2
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
  -- 原请求在同一目标反射层中实际解码；新界由它的真实候选和 δ 控制。
  have iw : Rd_entry_d w w₂ j₂ := ((graph w w₀).mp hww₀).2.symm ▸ omegaEdge
  obtain ⟨η₂,C₂,iη,iC,current⟩ := context.map_l hZF tree.omega mn mp embed iw
  let Cp : Pn.Domain := ⟨C₂,current.member⟩
  let ηp : Pn.Domain := ⟨η₂,current.height⟩
  have fp := current.finite_l mp.2.1 hP.1
  let nd : Nonempty {x : Pn.Domain // Pn.mem x Cp} := ⟨⟨⟨w₂,current.omega_mem⟩,fp.omega_mem⟩⟩
  obtain ⟨rN,recordN,tupleN⟩ := rf_record_save_l I mn.2.1 hN.1 tg_issued0_m tg_issued0_closed_l
    ⟨C,context.member⟩ fs.transitive fs.pair nc ι issued
  obtain ⟨r₂,ι₂,ir₂,issuedPoints,record₂,tuple₂,issued₂⟩ := embed.record_image_l I hZF tree.omega mn mp
    hP.1 Cp iC fp.transitive nd tg_issued0_m tg_issued0_closed_l recordN tupleN
  have rankCp := (rr_rank_native_l I mp.2.1 hP ηp Cp).mp ((rr_rank_truth_l I).mpr current.rank)
  have limitCp : Pn.IsLimitOrdinal ηp := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηp)).mp current.limit)
  obtain ⟨boundδ,regularδ⟩ := tg_issued_control_l hP rankCp limitCp fp nd ι₂ issued₂
  have eqb : bκ = (ι.bound 24).val.val :=
    ((graph (ρ.bound 21).val.val bκ).mp hbκ).2.symm.trans (congrArg Subtype.val eκ)
  have eqκ := embed.1.1.1.2 _ κ' (ι₂.bound 24).val.val (eqb ▸ hκ') (issuedPoints 24)
  let lp : Pn.Domain := ⟨l,common.right_rank.1⟩
  let Vp : Pn.Domain := ⟨Vc,common.right_rank.2.1⟩
  have rankVp := (rr_rank_native_l I mp.2.1 hP lp Vp).mp common.right_rank
  have candidateBound : Pn.MemberSubset lp (ι₂.bound 24).val :=
    fun x hx => Eq.mp (congrArg (fun y => Rd_entry_d x.val y R₂) eqκ) (boundκ x.val hx)
  have belowδ : Pn.mem lp (ι₂.bound 5).val := ordinal_down_l hP
    (v_ordinal_l (kp_pair_l hP) rankVp) regularδ.isCardinal.1 candidateBound boundδ
  have member : Pn.mem lp Cp := fp.transitive (ι₂.bound 5).val (ι₂.bound 5).property lp belowδ
  have eqω := embed.1.1.1.2 w (ι₂.bound 0).val.val w₂ (hw ▸ issuedPoints 0) iw
  have equal : Tg_reply_link_d Eq (fun i => (ι₂.bound i).val) ε.bound :=
    fun i => Subtype.ext (embed.1.1.1.2 _ _ _ (issuedPoints _) (linked i))
  -- 回答域属于实际共同层，故查询域和完整极限性可回收到当前控制层。
  have hVpC := ZF.v_mem_l (kp_pair_l hP) targetZF rankVp rankCp
    (ZF.v_ordinal_height_l targetZF rankCp (v_ordinal_l (kp_pair_l hP) rankVp) member)
  have lowPoint (x : Nn.Domain) y (hx : Nn.mem x W) (ip : Rd_entry_d x.val y t₀) : Rd_entry_d x.val y t :=
    (restrict.2 _ _).mpr ⟨(common.carrier _).mpr ⟨x.property,
      (ZF.v_unique_l (kp_pair_l hN) native rW rankUc) ▸ hx⟩,ip⟩
  have iQ := lowPoint (ρ.bound 12).val (ε.bound 7).val hQW (points 7)
  have hQC : Pn.mem (ε.bound 7) Cp := fp.transitive Vp hVpC (ε.bound 7)
    ((common.image _).mpr ⟨_,common.injection.1.input_mem_of_pairMember iQ,iQ⟩)
  have hwReply : ε.bound 0 = (⟨w₂,current.omega_mem⟩ : Pn.Domain) :=
    (equal 0).symm.trans (Subtype.ext eqω)
  have hnReply : Pn.mem (ε.bound 1) (ε.bound 0) :=
    (predPool _ _ (replyPoints 0) _).mpr ⟨_,by rw [values 1,values 0]; exact hl,replyPoints 1⟩
  have hnReply : Pn.mem (ε.bound 1) ⟨w₂,current.omega_mem⟩ := hwReply ▸ hnReply
  have hτUc := KP.v_ordinal_subset_l hN rankUc (ρ.bound 15).val hτL
  have iτ := lowPoint (ρ.bound 15).val (ε.bound 4).val
    (KP.v_ordinal_subset_l hN rW (ρ.bound 15).val hτL) (points 4)
  let nu : Nonempty {x : Nn.Domain // Nn.mem x Uc} := ⟨⟨(ρ.bound 15).val,hτUc⟩⟩
  let τsrc : Env (rt_model_l Uc nu) 1 := ⟨fun _ => ⟨(ρ.bound 15).val,hτUc⟩,fun _ => ⟨(ρ.bound 15).val,hτUc⟩⟩
  let τdst : Env Pn 1 := ⟨fun _ => ε.bound 4,fun _ => ε.bound 4⟩
  have limitτp := (KP.limit0_sat_l hP τdst .newest).mp
    ((rr_native_delta_l I mn.2.1 mp.2.1 Uc (v_transitive_l (kp_pair_l hN) rankUc) nu
      common.carrier common.injection common.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) τsrc τdst (fun _ => iτ)).mp
        ((KP.limit0_sat_l hN _ .newest).mpr limitτ))
  obtain ⟨ε₂,values₂,reflected,same,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,table,language₂,queries⟩ :=
    tg_answer_input_l targetZF (newNumbers.omega_l I (ZF.modelsKP hZF) tree.omega hP.1)
      rankCp limitCp fp nd ι₂ ε issued₂ (Subtype.ext eqω) reply equal hQC hnReply limitτp
  -- 当前表和原回答沿同一完整池解释同一个 Vτ 及全部有限查询，故域必须相等。
  let sourceFields : Fin 11 → Term 54 := fun i => [.bound 16,.bound 17,.bound 23,.bound 24,.bound 15,
    .bound 14,.bound 13,.bound 12,.bound 2,.bound 1,.bound 0].get i
  let sourceEnv := Definitional.Env.substitute ρ sourceFields
  have sourceLanguage : Formula.satisfies sourceEnv tg_reply_language0_m :=
    (Formula.satisfies_bind ρ sourceFields tg_reply_language0_m).mp body.2.2.2.2.2.2.2.2.2.1
  obtain ⟨finiteN,_,rankA,constantsA,poolA⟩ :=
    tg_reply_domain_read_l native rankC fs nc sourceEnv (Subtype.ext ew) sourceLanguage
  let targetEnv : Env (rt_model_l Cp nd) 11 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ε₂.bound 4,Aq,Uq,Dq,rq,bq,hq].get i,ι₂.free⟩
  obtain ⟨finiteNp,_,rankAp,constantsAp,poolAp⟩ :=
    tg_reply_domain_read_l targetZF rankCp fp nd targetEnv (Subtype.ext eqω) language₂
  have pointω : Rd_entry_d w w₂ t₀ :=
    Eq.mp (congrArg (fun x : Pn.Domain => Rd_entry_d w x.val t₀) hwReply) (points 0)
  have pointn : Rd_entry_d (ρ.bound 24).val.val (ι₂.bound 28).val.val t₀ :=
    (congrArg Subtype.val (equal 2)).symm ▸ points 2
  have pointτ : Rd_entry_d (ρ.bound 15).val.val (ε₂.bound 4).val.val t₀ :=
    (congrArg Subtype.val (values₂ 4)).symm ▸ points 4
  have pointD : Rd_entry_d (ρ.bound 12).val.val (ε₂.bound 7).val.val t₀ :=
    (congrArg Subtype.val (values₂ 7)).symm ▸ points 7
  have domainEq := tg_reply_domain_raw_l (ZF.modelsKP hZF) mn.2.1 mp.2.1 native targetZF
    common B₀ transB bc ft predPool restrict endpoint layer
    ⟨w,context.omega_mem⟩ (ρ.bound 24).val (ρ.bound 15).val (ρ.bound 14).val
    (ρ.bound 13).val (ρ.bound 12).val ⟨w₂,current.omega_mem⟩ (ι₂.bound 28).val (ε₂.bound 4).val
    (ε₂.bound 7).val Aq.val Uq.val Dq.val source.omega
    (newNumbers.omega_l I (ZF.modelsKP hZF) tree.omega hP.1)
    finiteN readUc.omega_mem hτL rankA constantsA poolA rankAp constantsAp poolAp pointω pointn pointτ pointD
  -- 重置标签是原空集，故在临界点以下；它、回答域和类型均落在实际新共同图上。
  have seedFacts := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m,tg_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at seedFacts
  have heω : Nn.mem (ρ.bound 17).val ⟨w,context.omega_mem⟩ :=
    Eq.mp (congrArg (fun x : Nn.Domain => Nn.mem (ρ.bound 17).val x)
      (show (ρ.bound 16).val = (⟨w,context.omega_mem⟩ : Nn.Domain) from Subtype.ext ew)) seedFacts.2.2.1
  have eLabel : ρ.bound 41 = ρ.bound 17 := (matched v 18).trans (empty.trans (matched v 1).symm)
  have hLabelω : Nn.mem (ρ.bound 41).val ⟨w,context.omega_mem⟩ := (congrArg Subtype.val eLabel).symm ▸ heω
  have idLabel : Rd_entry_d (ρ.bound 41).val.val (ρ.bound 41).val.val k :=
    (graph _ _).mpr ⟨(carrier _).mpr ⟨(ρ.bound 41).val.property,
      (v_transitive_l (kp_pair_l hN) rankX) V hVX (ρ.bound 41).val labelLow⟩,rfl⟩
  have iLabel : Rd_entry_d (ρ.bound 41).val.val (ι₂.bound 23).val.val t :=
    (fixκ _ _ _ (ρ.bound 41).val.property (source.below _ hLabelω) idLabel).mpr
      (Eq.mp (congrArg (fun x => Rd_entry_d x (ι₂.bound 23).val.val j₂)
        (show (ι.bound 23).val.val = (ρ.bound 41).val.val from (request 18).symm)) (issuedPoints 23))
  have pointType : Rd_entry_d (ρ.bound 11).val.val (ε₂.bound 9).val.val t₀ :=
    (congrArg Subtype.val (values₂ 9)).symm ▸ points 9
  have iType := lowPoint (ρ.bound 11).val (ε₂.bound 9).val.val
    (v_subset_mem_l (kp_pair_l hN) rW hQW answer.1) pointType
  have regular : Rr_truth_d I P R₂ (Formula.isRegularCardinal kpair_convention_l .newest)
      (fun _ : Fin 1 => (ι₂.bound 5).val.val) :=
    (rr_truth_native_l I mp.2.1 _ (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (ι₂.bound 5).val)).mpr
        ((Formula.satisfies_isRegularCardinal_iff (kp_pair_l hP) hP.1 ..).mpr regularδ)
  -- 重置只有一条活动边；实际低秩方块直接更新所有旧共同图与事件视图。
  have κδ := height.1.transitive L hLδ (ρ.bound 21).val hκL
  have subK := (KP.v_compare_l hN rankP rankX (height.1.transitive (ρ.bound 21).val κδ)).1
  have archives := adjacent.archive_step_l hZF tree.omega mn mp mb map hN targetZF.1
    (ρ.bound 21).val Pκ rankP hκL (fun x hx E => lowSquare x x.val E hx
      ((graph x.val x.val).mpr ⟨(carrier x.val).mpr ⟨x.property,subK x hx⟩,rfl⟩))
  have sourceExt := (root.map_l hZF tree.omega mn right).ext
  have traces := current.trace_image_l hZF tree.omega mn mp embed hP sourceExt numbers newNumbers nd
    (ι₂.bound 4) (ι₂.bound 1) (ι₂.bound 2) (ι₂.bound 3) (ι₂.bound 20)
    iw iC (issuedPoints 4) (issuedPoints 1) (issuedPoints 2) (issuedPoints 3) (issuedPoints 20)
  have archiveMove := traces.archive_l (ZF.modelsKP hZF) archives
  let oldFrame : Tg_archive_frame_d M.Domain := ⟨o,n,Q,G,Λ,H⟩
  let newFrame : Tg_archive_frame_d M.Domain := ⟨o,θ,Q₂,G₂,Λ₂,H₂⟩
  have oldLinks D (old : Tg_archive_links_d I oldFrame D) : Tg_archive_links_d I newFrame D := by
    apply old.extend_l I
    · intro i hi
      exact (succ i).mpr (Or.inl ((hm i).mpr (Or.inl hi)))
    · intro i c hi
      exact extension₂.2.2.1 i c (extension.2.2.1 i c hi)
    · intro i p hi hp
      have him := (hm i).mpr (Or.inl hi)
      exact (extension₂.2.2.2.1 o i p ((succ i).mpr (Or.inl him))).mpr
        ((extension.2.2.2.1 o i p him).mpr hp)
    · exact fun i L hi => (entries₂ i L).mpr (Or.inl hi)
    · exact fun x hx => rows₂ x (hh x hx)
  have newLink : (⟨m,d,N,R,w,η,C,L.val,W.val,r,q₁,B,σ⟩ : Tg_archive_row_d M.Domain).link_d newFrame := by
    refine ⟨succ.predecessor_mem,extension₂.2.2.1 m d node,
      (extension₂.2.2.2.1 o m q₁ succ.predecessor_mem).mpr root₁,
      (entries₂ m L.val).mpr (Or.inr ⟨rfl,rfl⟩),?_⟩
    obtain ⟨s,⟨p,pair,hp⟩,cell⟩ := row
    exact ⟨u,U,β,s,⟨p,pair,rows₂ p hp⟩,cell⟩
  have columns := archiveMove.columns_l I hZF.1 ω γ Bγ C₀ oldFrame mn hN an qn
    (ρ.bound 21).val (loc.ordinals_l hN source.transitive source.code).1.transitive
  have belowκ : Rd_entry_d χ (ρ.bound 21).val.val R :=
    Eq.mp (congrArg (fun a => Rd_entry_d χ a R) (congrArg Subtype.val eκ).symm) below
  -- 固定根基底的实际高度低于 L，完整 γ 层由同一共同图进入目标。
  let ag : Nn.Domain := ⟨aγ,heightg.member⟩
  let Vg : Nn.Domain := ⟨Vγ,layerg.member⟩
  have rankG := (rr_rank_native_l I mn.2.1 hN ag Vg).mp rankg
  have limitG : Nn.IsLimitOrdinal ag := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ag)).mp limitg₀)
  obtain ⟨bγ,sb,baseHeight,down⟩ := lowerγ
  have eqg := (heightg.unique_l (ZF.modelsKP hZF) baseHeight sourceExt).1
  have downG x (hx : Rd_entry_d x aγ R) : Rd_entry_d x (ρ.bound 21).val.val R :=
    Eq.mp (congrArg (fun a => Rd_entry_d x a R) (congrArg Subtype.val eκ).symm) (down x (eqg ▸ hx))
  have agL : Nn.mem ag L := ordinal_down_l hN limitG.1 (v_ordinal_l (kp_pair_l hN) rankUc)
    (fun x hx => downG x.val hx) hκL
  have agU := KP.v_ordinal_subset_l hN rankUc ag agL
  have VgU := ZF.v_mem_l (kp_pair_l hN) native rankG rankUc agL
  have anchor₂ := anchors γ Bγ aγ Vγ sγ tγ heightg layerg rankg downG anchor
  have atlas := anchor₂
  obtain ⟨ap,Vpγ,sp,tp,heightp,layerp,rankp,fixedp⟩ := atlas
  let agp : Pn.Domain := ⟨ap,heightp.member⟩
  let Vgp : Pn.Domain := ⟨Vpγ,layerp.member⟩
  have rankGp := (rr_rank_native_l I mp.2.1 hP agp Vgp).mp rankp
  have iγ := (common.layer_image_l (ZF.modelsKP hZF) mn.2.1 (certificate root).ext
    heightg heightp (v_transitive_l (kp_pair_l hN) rankUc) agU).1
  have iVg := (common.layer_image_l (ZF.modelsKP hZF) mn.2.1 (certificate root).ext
    layerg layerp (v_transitive_l (kp_pair_l hN) rankUc) VgU).1
  let ng : Nonempty {x : Nn.Domain // Nn.mem x Uc} := ⟨⟨ag,agU⟩⟩
  let γsrc : Env (rt_model_l Uc ng) 1 := ⟨fun _ => ⟨ag,agU⟩,fun _ => ⟨ag,agU⟩⟩
  let γdst : Env Pn 1 := ⟨fun _ => agp,fun _ => agp⟩
  have limitGp := (KP.limit0_sat_l hP γdst .newest).mp
    ((rr_native_delta_l I mn.2.1 mp.2.1 Uc (v_transitive_l (kp_pair_l hN) rankUc) ng
      common.carrier common.injection common.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) γsrc γdst (fun _ => iγ)).mp
        ((KP.limit0_sat_l hN _ .newest).mpr limitG))
  have omegaGp : Pn.mem ⟨w₂,current.omega_mem⟩ Vgp :=
    (common.pred _ _ iVg _).mpr ⟨w,omegaG,hww₂⟩
  have rootC₂ : Rd_entry_d C₀ C₂ q₂ := (rootGraph C₀ C₂).mpr
    ⟨right.1.1.input_mem_of_pairMember image,C,image,iC⟩
  have targetBasis : Tg_basis_d I γ Bγ C₀ w₂ P R₂ C₂ q₂ := by
    refine ⟨rootC₂,ap,Vpγ,sp,tp,heightp,layerp,rankp,?_,omegaGp,fixedp⟩
    exact (rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => agp)).mpr
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limitGp)
  have targetLower : It_lower_d I γ P R₂ (ι₂.bound 24).val.val := by
    obtain ⟨a,s,layer,down⟩ := (lowerImages γ sourceLower).2.1
    have high : Pn.mem ⟨κ₀,common.injection.1.output_mem_of_pairMember hκ₀⟩ (ι₂.bound 24).val :=
      Eq.mp (congrArg (fun b => Rd_entry_d κ₀ b R₂) eqκ) memκ
    exact ⟨a,s,layer,fun x hx => (regularδ.isCardinal.1.mem boundδ).transitive
      ⟨κ₀,common.injection.1.output_mem_of_pairMember hκ₀⟩ high ⟨x,(mp.2.2.2 x a hx).1⟩ (down x hx)⟩
  -- 表内三个查询回到原回答层核验，量词仍遍及两侧各自的完整反射层。
  let queriesEnv : Env (rt_model_l Cp nd) 12 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1,
      rq,mq,bq,hq,qq].get i,ι₂.free⟩
  let baseFields : Fin 7 → Term 12 := fun i => [.bound 0,.bound 1,.bound 2,.bound 3,.bound 7,.bound 9,.bound 10].get i
  let baseEnv := Definitional.Env.substitute queriesEnv baseFields
  have baseTruth : Formula.satisfies baseEnv tg_reply_base0_m :=
    (Formula.satisfies_bind queriesEnv baseFields tg_reply_base0_m).mp
      ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp queries).1).2
  have langFacts := language₂
  simp only [tg_reply_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at langFacts
  have omegaP := newNumbers.omega_l I (ZF.modelsKP hZF) tree.omega hP.1
  have insideG x (hx : Pn.mem x ⟨w₂,current.omega_mem⟩) :=
    (v_transitive_l (kp_pair_l hP) rankGp) _ omegaGp x hx
  have lowBase : ∀ i : Fin 4, Pn.mem (baseEnv.bound (i.castAdd 3)).val Vgp :=
    Fin.cases (Eq.mp (congrArg (fun x : Pn.Domain => Pn.mem x Vgp)
      (show (ι₂.bound 0).val = (⟨w₂,current.omega_mem⟩ : Pn.Domain) from Subtype.ext eqω).symm) omegaGp)
      (Fin.cases (insideG _ (omegaP.transitive hP _ finiteNp _ langFacts.2.1))
        (Fin.cases (insideG _ (omegaP.transitive hP _ finiteNp _ langFacts.2.2.1))
          (Fin.cases (insideG _ finiteNp) (fun i => Fin.elim0 i))))
  have scalar (x : Nn.Domain) a b (hx : Nn.mem x ⟨w,context.omega_mem⟩)
      (ha : x.val = a) (point : Rd_entry_d a b j₂) : Rd_entry_d x.val b t₀ :=
    (commute x x a b (low x hx) (natural x hx)
      ((graph x.val a).mpr ⟨(carrier x.val).mpr ⟨x.property,finite.transitive _ finite.omega_mem x hx⟩,ha⟩)).mpr point
  have iwBase : Rd_entry_d (ρ.bound 16).val.val (ι₂.bound 0).val.val t₀ := by
    rw [ew,eqω]
    exact pointω
  have pointBase : ∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
      (baseEnv.bound (i.castAdd 3)).val.val t₀ :=
    Fin.cases iwBase (Fin.cases (scalar _ _ _ heω (request 1) (issuedPoints 1))
      (Fin.cases (scalar _ _ _ hl (request 3) (issuedPoints 27))
        (Fin.cases (scalar _ _ _ hn' (request 4) (issuedPoints 28)) (fun i => Fin.elim0 i))))
  have members := common.reply_members_l hZF tree.omega root.model mn mp right rootMap
    sourceExt (certificate root).ext anchor anchor₂ layerg layerp
    (v_transitive_l (kp_pair_l hN) rankUc) VgU ⟨C,context.member⟩ Cp fs.transitive nc nd image rootC₂
    targetZF ⟨w₂,current.omega_mem⟩ agp (ε₂.bound 9).val omegaP fp rankGp limitGp
    (context.kernel_l mn.2.1 nc) ρ round baseEnv (Subtype.ext eqω) finiteNp lowBase baseTruth
    ft restrict predPool pointBase pointType
  have finiteL : Pn.mem (ε₂.bound 1).val ⟨w₂,current.omega_mem⟩ :=
    Eq.mp (congrArg (fun x : Pn.Domain => Pn.mem x ⟨w₂,current.omega_mem⟩) (values₂ 1).symm) hnReply
  have tableReply := tg_reply_table_l targetZF omegaP rankCp limitCp fp nd ε₂ finiteL reflected
    rq bq hq members.1 members.2.1 members.2.2
  let answerEnv : Env (rt_model_l Cp nd) 22 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,ε₂.bound 4,
      ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,ε₂.bound 9,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
      ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
      fun _ => ι₂.bound 0⟩
  have answerValues : (tg_reply_table_env_d ε₂ rq bq hq).bound = answerEnv.bound := by
    funext i
    exact Fin.cases (same 0).symm (Fin.cases (same 1).symm (Fin.cases (same 2).symm
      (Fin.cases (same 3).symm (Fin.cases rfl (Fin.cases (same 4).symm
        (Fin.cases (same 5).symm (Fin.cases (Subtype.ext domainEq) (Fin.cases (same 6).symm
          (Fin.cases rfl (Fin.cases (same 7).symm (Fin.cases (same 8).symm
            (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases (same 9).symm
              (Fin.cases (same 10).symm (Fin.cases (same 11).symm (Fin.cases (same 12).symm
                (Fin.cases (same 13).symm (Fin.cases (same 14).symm
                  (Fin.cases (same 15).symm (fun i => Fin.elim0 i)))))))))))))))))))))) i
  have answerTruth := (Formula.closed_env_l tg_reply0_m tg_reply0_closed_l
    (ρ := tg_reply_table_env_d ε₂ rq bq hq) (η := answerEnv) answerValues).mp tableReply
  let requestEnv : Env (rt_model_l Cp nd) 5 :=
    ⟨fun i => [ι₂.bound 0,ε₂.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,fun _ => ι₂.bound 0⟩
  have requestTruth : Formula.satisfies requestEnv tg_query_request0_m :=
    (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l
      (ρ := (⟨fun i => [ι₂.bound 0,ε₂.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        ι₂.free⟩ : Env (rt_model_l Cp nd) 5)) (η := requestEnv) rfl).mp key
  -- 实际数字图识别本轮；新奇数存档与当前回答共享全部原码和共同图。
  have digitsMap := (numbers.omega_map_l I hZF tree.omega mn mp embed sourceExt (certificate root).ext newNumbers).2
  have state₂ := (tg_issued_sat_l (rt_pair_l fp.transitive nd hP.1 fp.pair)
    (rt_model_ext_l hP.1 fp.transitive nd) ι₂).mp issued₂
  have finiteRound : Pn.mem (ι₂.bound 19).val ⟨w₂,current.omega_mem⟩ :=
    Eq.mp (congrArg (fun a => Rd_entry_d (ι₂.bound 19).val.val a R₂) eqω) state₂.round
  obtain ⟨m₀,index⟩ := tg_round_index_l I (ZF.modelsKP hZF) tree.omega mp.2.1 hP.1
    ⟨w₂,current.omega_mem⟩ (ι₂.bound 19).val newNumbers finiteRound
  obtain ⟨n₀,_,point₀⟩ := numbers.injection.1.2.2 m₀ index.finite
  have sameIndex := embed.1.2 n₀ (ι.bound 19).val.val (ι₂.bound 19).val.val
    (digitsMap m₀ n₀ (ι₂.bound 19).val.val point₀ index.point) (issuedPoints 19)
  have sourceIndex : Rd_entry_d m₀ (ι.bound 19).val.val z := sameIndex ▸ point₀
  let archiveRow : Tg_archive_row_d M.Domain := ⟨m,d,N,R,w,η,C,L.val,W.val,r,q₁,B,σ⟩
  have archiveBasis : Tg_basis_d I γ Bγ C₀ w N R C q₁ :=
    ⟨keep C₀ C image,aγ,Vγ,sγ,tγ,heightg,layerg,rankg,limitg₀,omegaG,
      fun x y hxy => keep x y (fixedg x y hxy)⟩
  have commonSaved := adjacent
  rw [congrArg Subtype.val (ZF.v_unique_l (kp_pair_l hN) native rankUc rW)] at commonSaved
  have savedLower : It_lower_d I γ N R (ρ.bound 15).val.val :=
    lower γ ⟨bγ,sb,baseHeight,down⟩
  have domainView : Rd_entry_d (ρ.bound 15).val.val (ε₂.bound 4).val.val t :=
    (congrArg Subtype.val (values₂ 4)).symm ▸ iτ
  have priorRoot := (extension₂.2.2.2.1 o n q hnθ).mpr oldRoot
  have rootComp := tree₂.diagram.comp o n θ q j₂ q₂ priorRoot edge₂ root₂
  have targetTree := rootComp S₀ (ι.bound 7).val.val (ι₂.bound 7).val.val treeName (issuedPoints 7)
  have treeEq : (ρ.bound 19).val.val = (ι.bound 7).val.val := congrArg (fun x => x.val.val) (head 3)
  have sourceTree : Rd_entry_d S₀ (ρ.bound 19).val.val q₁ :=
    Eq.mpr (congrArg (fun S => Rd_entry_d S₀ S q₁) treeEq) (keep _ _ treeName)
  have archiveName : Tg_saved_name_d I S₀ archiveRow.X archiveRow.R archiveRow.w archiveRow.U archiveRow.q archiveRow.p :=
    Tg_saved_name_d.of_code_l I hZF.1 code sourceTree
  -- 重置短前缀就是实际空集；同一原边与共同图给出它的目标像。
  have short_eq : (ρ.bound 40).val.val = (ρ.bound 41).val.val :=
    (congrArg (fun x => x.val.val) zero).trans
      ((request 18).trans (congrArg (fun x => x.val.val) empty)).symm
  have empty_image : (ι₂.bound 23).val.val = (ι₂.bound 1).val.val :=
    embed.1.1.1.2 (ι.bound 1).val.val _ _
      (Eq.mp (congrArg (fun x => Rd_entry_d x (ι₂.bound 23).val.val j₂)
        (congrArg (fun x => x.val.val) empty)) (issuedPoints 23)) (issuedPoints 1)
  have short_view : Rd_entry_d (ρ.bound 40).val.val (ι₂.bound 1).val.val t :=
    Eq.mpr (congrArg (fun x => Rd_entry_d x (ι₂.bound 1).val.val t) short_eq)
      (Eq.mp (congrArg (fun x => Rd_entry_d (ρ.bound 41).val.val x t) empty_image) iLabel)
  have rules := state₂.control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at rules
  have rules := rules.2.2.1
  simp only [tg_rules_m,Formula.satisfies_conj_iff,Formula.satisfies_isEmpty_iff] at rules
  have short_play : Tg_play_d I P R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val
      (ι₂.bound 20).val.val (ι₂.bound 1).val.val :=
    (tg_play_native_l I mp.2.1 hP.1 Cp fp.transitive nd (rt_pair_l fp.transitive nd hP.1 fp.pair)
      (ι₂.bound 4) (ι₂.bound 3) (ι₂.bound 20) (ι₂.bound 1)).mpr
      (fun _ _ ⟨p,_,hp⟩ => (rules.2.1 p hp).elim)
  have answered := current.answer_native_l hZF mp.2.1 hP nd ι₂ issued₂ eqω ω z₁ m₀ index
    lp (v_ordinal_l (kp_pair_l hP) rankVp) candidateBound
    (ε₂.bound 4) (ε₂.bound 9) Aq Uq Dq rq mq bq hq qq belowτ requestTruth table answerTruth
    γ Bγ C₀ S₀ B₂ σ₂ t q₂ rootMap.1.1.1 (targetBasis.anchor_l I) targetTree
    archiveRow newFrame targetLower root₂ newLink archiveName mn saved ⟨z,numbers⟩ archiveBasis
    ⟨_,_,_,_,commonSaved⟩ (fun i => (ρ.bound i).val.val) code savedLower iLabel domainView iType
    ⟨_,short_view,short_play⟩
  have ready : Tg_answer_step_d I d₂ P R₂ t₀ t j₂ q l w η C N R (ρ.bound 41).val.val
      B σ B₂ σ₂ (ρ.bound 21).val.val ω z γ Bγ C₀ S₀ archiveRow oldFrame newFrame
      (fun i => (ι.bound i).val.val) (fun i => (vals i).val) :=
    ⟨newLink,oldLinks,mp,(certificate root).ext,w₂,η₂,C₂,iw,iη,iC,current,q₂,root₂,
      rootMap.1.1.1,rootMap.1.2,targetBasis,nd,ι₂,ε₂,
      issuedPoints,rootComp,issued₂,eqω,targetLower,belowδ,member,
      fun i => (congrArg Subtype.val (values₂ i)).symm ▸ points i,reflected,
      ((restrict.2 _ _).mp iLabel).2,iLabel,domainView,iType,same,belowτ,key,
      Aq,Uq,Dq,rq,mq,bq,hq,qq,(Subtype.ext domainEq).symm,table,
      members.1,members.2.1,members.2.2,language₂,queries,
      z₁,m₀,numbers,sourceIndex,index,
      (fun k A s hA hk prior => prior.map_l hZF tree.omega mn mp embed sourceExt (certificate root).ext
        numbers index.numbers (fun x hx => by
          obtain ⟨_,_,_,t,_,layer,_,fixed⟩ := anchor
          obtain ⟨y,hy,point⟩ := layer.injection.1.2.2 x (layer.transitive A hA x hx)
          exact ⟨y,hy,fixed x y point⟩) hk rootMap.1.1.1 rootComp
        iC (issuedPoints 4) (issuedPoints 3) (issuedPoints 20)),
      (fun u i => index.even_l hZF targetZF fp nd
        (tg_position_env_d ⟨fun k => ι₂.bound (k.castAdd 27),fun _ => ι₂.bound 0⟩ (ι₂.bound 19) u i)
        (.bound 0) (.bound 19) (Subtype.ext eqω) rfl),
      answered,traces,archiveMove,
      fun D b bd lo links views => columns D b bd lo links views (ι₂.bound 20).val.val
        (ι₂.bound 20).property (fun _ _ h => h)⟩
  -- 只有首轮语言直接给出字母的原生 Vκ 界；此出口不冒充全部重置轮的满像。
  have firstPrefix (zero : ι.bound 19 = ι.bound 1) : ∃ n A₀ A₂ t' f,
      Rd_entry_d n (ι₂.bound 19).val.val z₁ ∧
      (∀ x, M.mem x A₀ ↔ M.mem x N ∧ Rd_entry_d x (ι.bound 6).val.val R) ∧
      (∀ x, M.mem x A₂ ↔ M.mem x P ∧ Rd_entry_d x (ι₂.bound 6).val.val R₂) ∧
      M.IsSetBijectionFromTo I t' A₀ A₂ ∧ M.IsRestrictionOf I t' j₂ A₀ ∧
      Tg_prefix_d I n A₀ P R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val z₁ j₂ f := by
    obtain ⟨A₀,A₂,t',f,source,range,bijection,rest,play⟩ :=
      cert.first_reset_prefix_l hZF mn hN rankX graph context nc ι issued empty zero eκ
        mp (certificate root).ext current nd ι₂ issued₂ issuedPoints newNumbers index.point
    exact ⟨m₀,A₀,A₂,t',f,index.point,source,range,bijection,rest,play⟩
  exact ⟨w₂,η₂,C₂,iw,iη,iC,current,nd,ι₂,ε₂,issuedPoints,issued₂,eqω,
    fun x hx => candidateBound ⟨x,(mp.2.2.2 x l hx).1⟩ hx,belowδ,member,regular,
    z₁,newNumbers,newLink,oldLinks,archiveMove,
    fun D links views => columns D χ bound belowκ links views (ι₂.bound 20).val.val
      (ι₂.bound 20).property (fun _ _ h => h),
    fun i => (congrArg Subtype.val (values₂ i)).symm ▸ points i,
    iLabel,(congrArg Subtype.val (values₂ 4)).symm ▸ iτ,iType,
    reflected,same,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,(Subtype.ext domainEq).symm,table,language₂,queries,ready,firstPrefix⟩

end YesMetaZFC.SetTheory.LargeCardinal
