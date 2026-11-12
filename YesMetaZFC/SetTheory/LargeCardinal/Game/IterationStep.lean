import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerNativeInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeEntry
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveEdge

/-! # 原字母表输入、实际落子与同一次下一请求

根图先将给定输入送入回答所在反射层，再执行已有落子。当前档案沿同一
原边搬运并追加新行，返回该次落子产生的请求记录，保持原轮号和根图。
数字图校准外部奇偶，背景中的完整原前缀恰好追加本次实际落子。
追加以前的前缀就是原状态所给的背景函数，沿同一原边和根图复合保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_answer_step_d.input_l
    {c X R t g j q₀ χ w η C Y S s A π A' π' κ Ω z γ Bγ Cᵣ S₀ k D b L x s₀ : M.Domain}
    {r₀ : Tg_archive_row_d M.Domain} {f f' : Tg_archive_frame_d M.Domain}
    {v : Fin 46 → M.Domain} {p : Fin 22 → M.Domain}
    (h : Tg_answer_step_d I c X R t g j q₀ χ w η C Y S s A π A' π' κ Ω z γ Bγ Cᵣ S₀ r₀ f f' v p)
    (index : M.PairMember I k (v 19) z) (seq : M.IsSequenceOfLength I D k)
    (bound : Ic_bound_d I f.H f.Q Y S π f.n b) (below : M.PairMember I b κ S)
    (links : Tg_archive_links_d I f D)
    (names : Tg_archive_names_d I S₀ D)
    (views : Tg_archive_views_d I Ω γ Bγ Cᵣ D Y S A π w C (v 4) (v 1) (v 2) (v 3) z (v 20))
    (hL : M.mem L Bγ) (alphabet : M.PairMember I L (v 6) q₀) (hx : M.mem x L)
    (prior : Tg_prefix_d I k L Y S C (v 4) (v 3) (v 20) z q₀ s₀) :
    ∃ target : Smdl_d I c X R, ∃ w' η' C' z' q',
    ∃ context : Tg_context_d I w' X R η' C',
      It_map_d f'.G f'.o f'.n q' ∧ Tg_basis_d I γ Bγ Cᵣ w' X R C' q' ∧
    ∃ nc : Nonempty {a : (smdl_structure_l I (R := R) target.2.1).Domain //
      (smdl_structure_l I (R := R) target.2.1).mem a ⟨C',context.member⟩},
    ∃ ι ε : Env (rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C',context.member⟩ nc) 46,
      (∀ i, M.PairMember I (v i) (ι.bound i).val.val j) ∧
      Formula.satisfies ι tg_issued0_m ∧
    ∃ k' D' r', M.SuccessorOf k' k ∧
      Tg_request_state_d I Ω γ Bγ Cᵣ S₀ X R w' η' C' A' π' χ z' k' D' r' f'
        (fun i => (ε.bound i).val.val) ∧
      (∀ i : Fin 19, M.PairMember I (v (i.castAdd 27)) (ε.bound (i.castAdd 27)).val.val j) ∧
      (∀ i : Fin 19, ∀ a, M.PairMember I a (v (i.castAdd 27)) q₀ →
        M.PairMember I a (ε.bound (i.castAdd 27)).val.val q') ∧
      M.PairMember I L (ε.bound 6).val.val q' ∧
    ∃ r, Rt_tuple_d r₀.values_d r ∧
      (∀ l a, M.PairMember I l a D' ↔ M.PairMember I l a D ∨ l = k ∧ a = r) ∧
      let P := rt_model_l (M := smdl_structure_l I (R := R) target.2.1) ⟨C',context.member⟩ nc
      ∃ a y u i u' : P.Domain,
        M.PairMember I x a.val.val q' ∧ P.mem y (ι.bound 6) ∧
        let ψ := tg_position_env_d
          (⟨fun n => ι.bound (n.castAdd 27),fun _ => ι.bound 0⟩ : Env P 19) (ι.bound 19) u i
        ∃ y₀ : M.Domain, M.mem y₀ L ∧ M.PairMember I y₀ y.val.val q' ∧
        (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) ↔
          Descriptive.Gm_even_d I Ω k) ∧
        (Descriptive.Gm_even_d I Ω k → y₀ = x) ∧
        Formula.satisfies ψ (tg_position0_m 2) ∧
        (Descriptive.Gm_even_d I Ω k → y = a) ∧
        (¬ Descriptive.Gm_even_d I Ω k →
          Rd_entry_d (ψ.bound 20) y (ψ.bound 17)) ∧
        Formula.satisfies (⟨fun n => [ψ.bound 0,u',ψ.bound 20,y].get n,fun _ => y⟩ : Env P 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
        Rd_entry_d u' (ε.bound 21) (ψ.bound 17) ∧
        Formula.satisfies (⟨fun n => [ψ.bound 0,ε.bound 20,u',ε.bound 21].get n,fun _ => ε.bound 21⟩ : Env P 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
        P.mem (ι.bound 24) (ε.bound 24) ∧
        (smdl_structure_l I (R := R) target.2.1).MemberSubset (ι.bound 20).val (ε.bound 20).val ∧
        (ι.bound 20).val ≠ (ε.bound 20).val ∧
        ∃ t, Tg_prefix_d I k L X R C' (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val z' q' s₀ ∧
          Tg_prefix_d I k' L X R C' (ε.bound 4).val.val (ε.bound 3).val.val (ε.bound 20).val.val z' q' t ∧
          Fseq_end_d I Ω t s₀ y₀ := by
  obtain ⟨_,oldLinks,target,ext,w',η',C',_,_,_,context,q',root,function,injective,basis,nc,ι,ρ,
    points,comp,issued,_,_,_,_,_,_,_,_,_,_,_,_,_,
    Bq,Uq,Dq,rq,mq,bq,hq,qq,_,_,_,_,_,_,_,z',m,numbers,source,index',transfer,parity,answer,_,_,columns⟩ := h
  have eq := numbers.injection.2 m k (v 19) source index
  subst m
  have roots (i : Fin 46) (a : M.Domain) (ha : M.PairMember I a (v i) q₀) :
      M.PairMember I a (ι.bound i).val.val q' := comp a (v i) (ι.bound i).val.val ha (points i)
  obtain ⟨_,u,i,_,position,_,_,_,_,inputs⟩ := answer
  obtain ⟨a,point,move⟩ := inputs L hL (roots 6 L alphabet) x hx
  obtain ⟨y,u',i',n',hy,even,odd,endt,succ,start,ε,head,num,issued',value,aux,
    growth,keepχ,lower,keep,proper,trace,view,preserve,k',succ',next,r,code,append⟩ := move
  obtain ⟨D',seq',entries,updated,linked,named,select,state⟩ := append D seq
  -- 旧列先沿原边搬运，再向同一列追加本次真实回答；下一记录使用这一份列。
  obtain ⟨r',state⟩ := state (columns D b bound below links views) (oldLinks D links) names
  have control (i : Fin 19) : ε.bound (i.castAdd 27) = ι.bound (i.castAdd 27) := by
    simpa only [tg_position_env_d,Fin.addCases_left] using head i
  have same (i : Fin 19) : (ε.bound (i.castAdd 27)).val.val = (ι.bound (i.castAdd 27)).val.val :=
    congrArg (fun a => a.val.val) (control i)
  have rootValues (i : Fin 19) (a : M.Domain) (ha : M.PairMember I a (v (i.castAdd 27)) q₀) :
      M.PairMember I a (ε.bound (i.castAdd 27)).val.val q' :=
    Eq.mpr (congrArg (fun b => M.PairMember I a b q') (same i)) (roots (i.castAdd 27) a ha)
  -- 原状态中的同一个背景前缀沿原边保持，再从实际下一请求读取延伸前缀。
  have prefix₀ := transfer k L s₀ hL (index'.omega.transitive (ZF.modelsKP hZF) k index'.finite) prior
  obtain ⟨L₁,t₁,carrier,bijection,restriction⟩ :=
    (basis.anchor_l I).alphabet_l hZF function hL (rootValues 6 L alphabet)
  obtain ⟨s₁,prefix₁⟩ := context.prefix_l hZF target.2.1 (ext.native_l I target.2.1) nc ε issued'
    state.numbers state.index carrier bijection restriction
  -- 同一数字图识别外部奇偶；实际落子在偶数轮读回给定输入，奇数轮服从原策略。
  have hy' : Rd_entry_d y.val.val (ε.bound 6).val.val R :=
    Eq.mpr (congrArg (fun A => Rd_entry_d y.val.val A R) (same 6)) hy
  obtain ⟨y₀,hyL,hyb⟩ := bijection.2 y.val.val ((carrier y.val.val).mpr ⟨y.val.property,hy'⟩)
  have played : M.PairMember I y₀ y.val.val q' := ((restriction.2 y₀ y.val.val).mp hyb).2
  -- 同一阶段2位置给出最后一个真实事件，完整前缀因此恰好追加读回的字母。
  have extN := ext.native_l I target.2.1
  have fs := context.finite_l target.2.1 extN
  let J := rt_pair_l fs.transitive nc extN fs.pair
  have ep := rt_model_ext_l extN fs.transitive nc
  let ψ := tg_position_env_d
    ⟨fun n => ι.bound (n.castAdd 27),fun _ => ι.bound 0⟩ (ι.bound 19) u i
  have event := tg_position_digit_event_l J ep ψ position
    ((fseq_end_sat_l J ep ..).mp endt) ((fseq_end_sat_l J ep ..).mp aux)
  have ends := prefix₀.append_l hZF target.2.1 extN ⟨C',context.member⟩ fs.transitive nc J ι ε y
    issued' control prefix₁ index'.numbers.injection.1.1 injective index'.omega index'.finite
    succ' keep index'.point played event
  refine ⟨target,w',η',C',z',q',context,root,basis,nc,ι,ε,points,issued,
    k',D',r',succ',state,?_,rootValues,rootValues 6 L alphabet,r,code,entries,
    a,y,u,i,u',point,hy,y₀,hyL,played,parity u i,?_,position,
    (fun e => even ((parity u i).mpr e)),(fun e => odd (fun h => e ((parity u i).mp h))),
    endt,value,aux,growth,keep,proper,s₁,prefix₀,prefix₁,ends⟩
  · intro i
    exact Eq.mpr (congrArg (fun b => M.PairMember I (v (i.castAdd 27)) b j) (same i)) (points (i.castAdd 27))
  · intro e
    have eq := congrArg (fun a => a.val.val) (even ((parity u i).mpr e))
    exact injective y₀ x a.val.val (Eq.mp (congrArg (fun a => M.PairMember I y₀ a q') eq) played) point

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树、工作复制、请求与原对局的共同有限状态

所有对象码都来自同一次实际后继。当前所属模型保留自己的关系和数字图，
工作复制独立保存历史及末行；原局前缀仍是背景中的同一个函数。
本层保存下一次构造所需的数据及实际奇数边的三图方程，并历史的分支性质由运行上层处理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- X,R,w,z,η,C,m,n,T,Q,G,E,Λ,D,χ,c,q,r,B,σ,H,ST,QT,GT,u,U,β,k,s。
structure Tg_iteration_d (ω c₀ o C₀ S₀ γ Bγ A : M.Domain)
    (v : Fin 29 → M.Domain) (a : Fin 46 → M.Domain) : Prop where
  finite : M.mem (v 7) ω
  successor : M.SuccessorOf (v 6) (v 7)
  tree : It_tree_d hZF ω c₀ (v 6) (v 8) (v 9) (v 10) (v 11)
  history : Ic_history_d hZF ω (v 8) (v 9) (v 10) (v 11) (v 12) (v 6) (v 20) (v 21) (v 22) (v 23)
  levels_function : M.IsSetFunction I (v 12)
  levels : ∀ i L, Rd_entry_d i L (v 12) ↔ ∃ p κ F, Rd_entry_d i p (v 11) ∧ It_payload_d p κ L F
  row : Ic_at_d (v 20) (v 7) (v 0) (v 18) (v 19) (v 24) (v 25) (v 26)
  node : Rd_entry_d (v 7) (v 15) (v 9)
  model : Smdl_d I (v 15) (v 0) (v 1)
  root_node : Rd_entry_d o c₀ (v 9)
  root_map : It_map_d (v 10) o (v 7) (v 16)
  basis : Tg_basis_d I γ Bγ C₀ (v 2) (v 0) (v 1) (v 5) (v 16)
  bound : Ic_bound_d I (v 20) (v 9) (v 0) (v 1) (v 19) (v 7) (v 14)
  request : Tg_request_state_d I ω γ Bγ C₀ S₀ (v 0) (v 1) (v 2) (v 4) (v 5)
    (v 18) (v 19) (v 14) (v 3) (v 27) (v 13) (v 17)
    ⟨o,v 7,v 9,v 10,v 12,v 20⟩ a
  alphabet : M.PairMember I A (a 6) (v 16)
  play : Tg_prefix_d I (v 27) A (v 0) (v 1) (v 5) (a 4) (a 3) (a 20) (v 3) (v 16) (v 28)
  critical : It_critical_bound_d I γ (v 9) (v 11)

/-- 实际所选父行、奇数边及该边上的三图方程共同确定本轮的新存档。 -/
def Tg_iteration_parent_d (v : Fin 29 → M.Domain) (a : Fin 46 → M.Domain)
    (k G : M.Domain) (row : Tg_archive_row_d M.Domain) : Prop :=
  ∃ j, It_map_d G k (v 6) j ∧
    ((a 23 = a 1 ∧ k = v 7 ∧ Tg_archive_reset_d I row (a 7) j) ∨
      (a 23 ≠ a 1 ∧ ∃ l r, ∃ old : Tg_archive_row_d M.Domain,
        M.mem l (v 27) ∧ M.PairMember I l (a 22) (v 3) ∧ M.PairMember I l r (v 13) ∧
          Rt_tuple_d old.values_d r ∧ old.i = k ∧ Tg_archive_step_d I old row j))

/-- 两次树延伸及同一次原局追加，保存原列和完整复制列的包含关系。 -/
def Tg_iteration_next_d (ω c₀ x : M.Domain) (v w : Fin 29 → M.Domain)
    (a b : Fin 46 → M.Domain) : Prop :=
  ∃ k T Q G E j,
    It_tree_d hZF ω c₀ (w 7) T Q G E ∧
    It_extension_d (v 6) (v 7) k (v 8) (v 9) (v 10) (v 11) (w 7) T Q G E ∧
    It_extension_d (w 7) (v 6) (v 7) T Q G E (w 6) (w 8) (w 9) (w 10) (w 11) ∧
    It_map_d (w 10) (v 7) (w 7) j ∧
    (∀ i : Fin 19, M.PairMember I (a (i.castAdd 27)) (b (i.castAdd 27)) j) ∧
    (∃ t, M.PairMember I (a 20) t j ∧ t ≠ b 20 ∧
      ∀ x, M.mem x (w 0) → M.PairMember I x t (w 1) → M.PairMember I x (b 20) (w 1)) ∧
    M.MemberSubset (v 20) (w 20) ∧ M.MemberSubset (v 22) (w 22) ∧ M.MemberSubset (v 23) (w 23) ∧
    M.SuccessorOf (w 27) (v 27) ∧
    ∃ y, Fseq_end_d I ω (w 28) (v 28) y ∧ (Descriptive.Gm_even_d I ω (v 27) → y = x) ∧
      ∃ row : Tg_archive_row_d M.Domain, ∃ r, row.i = v 6 ∧ Rt_tuple_d row.values_d r ∧
        Tg_iteration_parent_d hZF v a k G row ∧
        (∀ l t, M.PairMember I l t (w 13) ↔ M.PairMember I l t (v 13) ∨ l = v 27 ∧ t = r)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一两步树延伸与实际落子闭合下一有限状态

树、工作复制和最后一行来自已经选择的两次后继；回答入口只在这份数据上
执行输入并追加档案。原局、原树和复制历史不再各自重选下一状态。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际回答的任意原字母输入同时保存下一次构造所需的全部对象。 -/
theorem Tg_iteration_d.finish_l
    {ω c₀ o C₀ S₀ γ Bγ A x : M.Domain} {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (h : Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A v a)
    {k n m T₁ Q₁ G₁ E₁ T₂ Q₂ G₂ E₂ Λ₂ H₂ ST₂ QT₂ GT₂ X R B σ u U β c χ j t g κ s : M.Domain}
    {row : Tg_archive_row_d M.Domain} {p : Fin 22 → M.Domain} {a' : Fin 46 → M.Domain}
    (mid : It_tree_d hZF ω c₀ n T₁ Q₁ G₁ E₁)
    (first : It_extension_d (v 6) (v 7) k (v 8) (v 9) (v 10) (v 11) n T₁ Q₁ G₁ E₁)
    (tree : It_tree_d hZF ω c₀ m T₂ Q₂ G₂ E₂)
    (second : It_extension_d n (v 6) (v 7) T₁ Q₁ G₁ E₁ m T₂ Q₂ G₂ E₂)
    (lf : M.IsSetFunction I Λ₂)
    (levels : ∀ i L, Rd_entry_d i L Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ L F)
    (history : Ic_history_d hZF ω T₂ Q₂ G₂ E₂ Λ₂ m H₂ ST₂ QT₂ GT₂)
    (keep_h : M.MemberSubset (v 20) H₂) (keep_q : M.MemberSubset (v 22) QT₂)
    (keep_g : M.MemberSubset (v 23) GT₂)
    (last : Ic_at_d H₂ n X B σ u U β) (node : Rd_entry_d n c Q₂)
    (edge : It_map_d G₂ (v 7) n j) (bound : Ic_bound_d I H₂ Q₂ X R σ n χ)
    (critical : It_critical_bound_d I γ Q₂ E₂)
    (ready : Tg_answer_step_d I c X R t g j (v 16) χ (v 2) (v 4) (v 5) (v 0) (v 1) s
      (v 18) (v 19) B σ κ ω (v 3) γ Bγ C₀ S₀ row
      ⟨o,v 7,v 9,v 10,v 12,v 20⟩ ⟨o,n,Q₂,G₂,Λ₂,H₂⟩ a' p)
    (eq : a' = a)
    (parent : Tg_iteration_parent_d hZF v a k G₁ row)
    (row_index : row.i = v 6)
    (below : M.PairMember I (v 14) κ (v 1)) (letters : M.mem A Bγ) (hx : M.mem x A) :
    ∃ w b, Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A w b ∧ Tg_iteration_next_d hZF ω c₀ x v w a b := by
  have request₀ := Eq.mpr (congrArg (Tg_request_state_d I ω γ Bγ C₀ S₀ (v 0) (v 1) (v 2)
    (v 4) (v 5) (v 18) (v 19) (v 14) (v 3) (v 27) (v 13) (v 17)
    ⟨o,v 7,v 9,v 10,v 12,v 20⟩) eq) h.request
  have alphabet₀ := Eq.mpr (congrArg (fun a => M.PairMember I A (a 6) (v 16)) eq) h.alphabet
  have play₀ := Eq.mpr (congrArg (fun a => Tg_prefix_d I (v 27) A (v 0) (v 1) (v 5)
    (a 4) (a 3) (a 20) (v 3) (v 16) (v 28)) eq) h.play
  obtain ⟨model,w',η',C',z',q',context,root,basis,nc,ι,ε,points,issued,
    k',D',r',succ,request,images,_,alphabet,r,code,entries,
    a',y,t',i,t'',_,_,y₀,_,_,_,even,_,_,_,_,_,_,_,keep,proper,f,_,play,ends⟩ :=
    ready.input_l hZF request₀.index request₀.sequence h.bound below
      request₀.links request₀.names request₀.views letters alphabet₀ hx play₀
  obtain ⟨m₀,hm₀,hmω⟩ := h.tree.omega.1.2 (v 7) h.finite
  have em : m₀ = v 6 := hm₀.eq hZF.1 h.successor
  obtain ⟨n₀,hn₀,hnω⟩ := h.tree.omega.1.2 (v 6) (em ▸ hmω)
  have en : n₀ = n := hn₀.eq hZF.1 first.1
  let w : Fin 29 → M.Domain := fun i =>
    [X,R,w',z',η',C',m,n,T₂,Q₂,G₂,E₂,Λ₂,D',χ,c,q',r',B,σ,H₂,ST₂,QT₂,GT₂,u,U,β,k',f].get i
  refine ⟨w,(fun i => (ε.bound i).val.val),?_,?_⟩
  · exact ⟨(show M.mem n ω from en ▸ hnω),second.1,tree,history,lf,levels,last,node,model,
      second.2.2.1 o c₀ (first.2.2.1 o c₀ h.root_node),root,basis,bound,request,alphabet,play,critical⟩
  · refine ⟨k,T₁,Q₁,G₁,E₁,j,mid,first,second,edge,?_,?_,keep_h,keep_q,keep_g,succ,
      y₀,ends,even,row,r,row_index,code,parent,entries⟩
    · intro i
      exact Eq.mp (congrArg (fun x => M.PairMember I x (ε.bound (i.castAdd 27)).val.val j)
        (congrFun eq (i.castAdd 27))) (images i)
    · exact ⟨(ι.bound 20).val.val,
        Eq.mp (congrArg (fun x => M.PairMember I x (ι.bound 20).val.val j) (congrFun eq 20)) (points 20),
        (fun e => proper (Subtype.ext e)),fun x hx hmem => keep ⟨x,hx⟩ hmem⟩

end YesMetaZFC.SetTheory.LargeCardinal
