import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchive
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.SetTheory.CumulativeRelativeRead
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationState
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationUnion
import YesMetaZFC.SetTheory.Descriptive.Game.GameStrategyProjection

/-! # 辅助游戏 II 获胜迫使原树含空根

II 负责首个辅助走法，故其获胜策略在空历史上的实际值必须合法。
零轮不能继续较早轮，只能采用原重置类型；其中的同一个节点查询
给出长度为空的实际树节点。因此不预设树非空，也不要求原字母表非空。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 首步合法性只来自实际获胜策略和原检查规则，不使用带空根字段的控制记录。 -/
private theorem tg_win_first_aux_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g)
    (win : Cg_win_d I false p.ω X F J B W σ) : ∃ v, Tg_aux_d hZF p p.e p.e v := by
  have hw := game.setup.omega
  have empty := game.setup.empty
  have he := num_mem_l hZF.1 hw (show Num_d 0 p.e from empty)
  obtain ⟨hc,_⟩ := tg_clock_l hZF hw empty game.setup.one game.setup.two game.setup.three he
  have oc := hw.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ec := oc.transitive p.b game.setup.three.predecessor_mem p.e
    ((oc.mem game.setup.three.predecessor_mem).transitive p.a game.setup.two.predecessor_mem
      p.e game.setup.one.predecessor_mem)
  have clock : M.IsOrdinalDivision I p.e p.c p.e p.e :=
    ⟨hw.members_areOrdinals (ZF.modelsKP hZF) p.e he,ec,p.e,
      (ZF.ordinalMultiplication_zero_iff hZF I oc empty).mpr empty,
      (ZF.ordinalAddition_zero_iff hZF I empty).mpr rfl⟩
  have ne₁ : p.e ≠ p.a := fun eq => empty p.e (eq.symm ▸ game.setup.one.predecessor_mem)
  have ne₂ : p.e ≠ p.b := fun eq => empty p.a (eq.symm ▸ game.setup.two.predecessor_mem)
  have turn : ¬ M.mem p.e J := fun own =>
    ((game.owner.read_l hZF (hw.isOrdinal (ZF.modelsKP hZF)) oc
      ⟨p.b,game.setup.three.predecessor_mem⟩ he he clock).mp own).elim ne₁ (fun h => ne₂ h.1)
  have fe : Fn0_d p.e X p.e := ⟨fun x hx => (empty x hx).elim,
    fun x hx => (empty x hx).elim,fun x hx => (empty x hx).elim⟩
  obtain ⟨R,control⟩ := cg_control_l hZF hw empty game.histories.1 game.legal
    (game.empty_l hZFC) game.runs game.payoff win
  have heF := ((control.legal p.e).mp ((control.positions p.e).mp control.root).1).1
  obtain ⟨v,hv,value⟩ := control.strategy.2.1 p.e heF
  obtain ⟨j,t,_,_,ends⟩ := ZF.fseq_end_exists_l I hZF hw he (fn0_function_l (ZF.modelsKP hZF) fe) hv
  have next := control.step p.e p.e v t he control.root hv fe ends (Or.inr ⟨turn,value⟩)
  have check := ((game.histories.2 t).mp (control.legal.current_l ((control.positions t).mp next).1)).2
  have step := (tg_step_read_l hZF (hw.members_areOrdinals (ZF.modelsKP hZF) p.e he)
    oc ⟨p.b,game.setup.three.predecessor_mem⟩ he clock).mp (check.end_l hZF fe ends)
  exact ⟨v,step.elim And.right (fun h => h.elim (fun h => (ne₁ h.1).elim) (fun h => (ne₂ h.1).elim))⟩

/-- 原完整重置类型中的节点查询把 II 获胜的首步还原为空根属于原树。 -/
theorem Tg_game_d.win_root_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g)
    (win : Cg_win_d I false p.ω X F J B W σ) : M.mem p.e p.S := by
  obtain ⟨v,aux⟩ := tg_win_first_aux_l hZFC game win
  obtain ⟨ℓ,t,κ,u,k,l,n,x,s,C,U,D,r,m,b,q,f,V,Y,E,g₀,g₁,g₂,g₃,
    _,hk,ft,first,last,_,_,request,data,_,_,_,member,_,branch⟩ := aux
  rcases branch with ⟨eq,reset⟩ | ⟨_,past⟩
  · subst t
    have emptyk : ∀ i, ¬ M.mem i k := by
      intro i hi
      obtain ⟨a,_,p,_,hp⟩ := ft.2.1 i hi
      exact game.setup.empty p hp
    obtain ⟨l',n',first',last',_,_,node,_⟩ := game.setup.queries.read_l hZFC hk request data
    have eq := first'.eq hZF.1 first
    subst l'
    have eq := last'.eq hZF.1 last
    subst n'
    obtain ⟨η,K,c,R,a,_,rank,model,realized,treeName,_⟩ := reset
    obtain ⟨f',_,_,valid⟩ :=
      (node.2 c K R a p.δ u p.S model (v_transitive_l I rank) realized treeName).mp member
    obtain ⟨q,hq,graph,_⟩ := valid.2.2.2
    have emptyq : ∀ p, ¬ M.mem p q := by
      intro p hp
      obtain ⟨i,a,pair⟩ := graph.1.1 p hp
      exact emptyk i ((graph.2 i).mpr ⟨a,p,pair,hp⟩)
    exact hZF.1.eq_of_same_members q p.e (fun x => iff_of_false (emptyq x) (game.setup.empty x)) ▸ hq
  · exact (game.setup.empty ℓ past.1).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原控制记录的真实零轮

控制、反射与首请求都在给定关系结构内构造，背景只保存原对象码。
背景自然数用于树指标，原生自然数及原生空对象仍由完整数字图解释；两者不作字面混同。
原字母对象的全部成员构成实际外部字母集，完整有限列译码和空树框架一并构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 在同一个原关系结构内反射完整更新核，并保存原生有限读写闭包。 -/
private theorem tg_context_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ground : (smdl_structure_l I (R := R) nx).Models ZFC)
    (w A : (smdl_structure_l I (R := R) nx).Domain)
    (hw : (smdl_structure_l I (R := R) nx).IsOmega w) (Φ : List Lr_formula) :
    ∃ η C : (smdl_structure_l I (R := R) nx).Domain,
      Tg_context_d I w.val X R η.val C.val ∧
      (smdl_structure_l I (R := R) nx).mem A C ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let N := smdl_structure_l I (R := R) nx
  let hN := ZFC.models_zf_l ground
  let J := kp_pair_l (ZF.modelsKP hN)
  obtain ⟨P,pair⟩ := KP.exists_pair (ZF.modelsKP hN) w A
  obtain ⟨η,C,rank,limit,hP,reflect⟩ :=
    ZF.lr_finite_l J hN (⟨0,tg_kernel_m,tg_kernel_closed_l⟩ :: Φ) P
  have trans := v_transitive_l J rank
  have hwC := trans P hP w ((pair w).mpr (Or.inl rfl))
  have hAC := trans P hP A ((pair A).mpr (Or.inr rfl))
  have algebra := sc_v_algebra_l ground limit rank
  have finite : Fs_read_d w C := by
    refine ⟨trans,hwC,algebra.pair,
      fun _ _ _ hn hA hf => sc_finite_function_l (ZF.modelsKP hN) hw trans
        algebra.pair algebra.union hwC hA hn hf,?_⟩
    intro B n hB hn
    exact v_fspace_exists_l J (ZF.modelsKP hN) rank limit (trans w hwC n hn) hB
  let ρ : Env N 0 := ⟨Fin.elim0,fun _ => w⟩
  have kernel := (reflect ⟨0,tg_kernel_m,tg_kernel_closed_l⟩ (List.mem_cons_self ..)
    ρ (fun i => Fin.elim0 i)).mp (tg_kernel_true_l ground w)
  let ηr : Env N 2 := ⟨Fin.cases C (fun _ => η),fun _ => C⟩
  let ηf : Env N 2 := ⟨Fin.cases C (fun _ => w),fun _ => C⟩
  have context : Tg_context_d I w.val X R η.val C.val := by
    refine ⟨?_,?_,?_,?_⟩
    · have truth := (rr_truth_native_l I nx (v_sigma_m (.bound 1) .newest)
        (by simp -implicitDefEqProofs) ηr.bound).mpr
        ((v_sigma_sat_l (ZF.modelsKP hN) ηr (.bound 1) .newest).mpr rank)
      have values : (fun i => (ηr.bound i).val) = Fin.cases C.val (fun _ : Fin 1 => η.val) :=
        funext (Fin.cases rfl (fun _ => rfl))
      exact values ▸ truth
    · exact (rr_truth_native_l I nx (Formula.isLimitOrdinal .newest)
        (by simp -implicitDefEqProofs) (fun _ : Fin 1 => η)).mpr
        ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limit)
    · have truth := (rr_truth_native_l I nx (fs_read_m (.bound 1) .newest)
        (by simp -implicitDefEqProofs) ηf.bound).mpr
        ((fs_read_sat_l hN.1 ηf (.bound 1) .newest).mpr finite)
      have values : (fun i => (ηf.bound i).val) = Fin.cases C.val (fun _ : Fin 1 => w.val) :=
        funext (Fin.cases rfl (fun _ => rfl))
      exact values ▸ truth
    · exact (rr_truth_native_l I nx tg_context_m tg_context_closed_l (fun _ : Fin 1 => C)).mpr
        ((Formula.closed_env_l tg_context_m tg_context_closed_l
          (ρ := ρ.push C) (η := ⟨fun _ => C,fun _ => C⟩)
          (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel)
  exact ⟨η,C,context,hAC,fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

/-- 同一十九项控制记录直接产生零轮；规则中的 ω 与空对象由原公式读回。 -/
theorem tg_control_zero_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D σ H : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (control : Formula.satisfies (⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,
      fun _ => p.ω⟩ : Env (smdl_structure_l I (R := R) certificate.model.2.1) 19) tg_control0_m) :
    ∃ η C r, Tg_context_d I p.ω.val X R η C ∧
      Rf_record_d I X R tg_issued0_m C r ∧ ∃ u : Fin 46 → M.Domain,
      Rf_tuple_d I X R u r ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H.val].get i) ∧
      u 19 = p.e.val ∧ u 23 = p.e.val ∧ u 26 = p.e.val ∧
      Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => u 24) ∧
      Rr_rank_d I X R (u 24) (u 29) ∧ Rd_entry_d p.ω.val (u 29) R ∧
      Rd_entry_d p.A.val (u 29) R ∧ Rd_entry_d p.e.val (u 24) R ∧
      ∃ o α T Q J, (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α o ∧
        It_tree_d hZF Ω c α T Q J o ∧ Rd_entry_d o c Q ∧
        ∃ q A₀ F₀ J₀ D₀ t₀ k₀ f,
          It_map_d J o o q ∧ (∀ x, M.mem x X → Rd_entry_d x x q) ∧
          Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧
          (∀ x, M.mem x A₀ ↔ M.mem x X ∧ Rd_entry_d x p.A.val R) ∧ Fseq_space_d I Ω A₀ J₀ ∧
          (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
          M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
          (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
          M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
          Tg_prefix_d I o A₀ X R C (u 4) (u 3) (u 20) z q f ∧
          Tg_raw_archive_links_d I ⟨o,o,Q,J,o⟩ o := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have ground := certificate.native_l I hZF hΩ
  have hN := ZFC.models_zf_l ground
  let ν : Env N 19 := ⟨fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,fun _ => p.ω⟩
  have facts := control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at facts
  have rules : Tg_rules_d hN p A F L D :=
    (tg_rules_sat_l hN ν (tg_control_params_d Term.bound) (.bound 12) (.bound 13) (.bound 14) (.bound 16)).mp facts.2.2.1
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hN) ν.bound
  have valid : Formula.satisfies ((⟨Fin.elim0,fun _ => p.ω⟩ : Env N 0).push r)
      (rt_record_m tg_control0_m .newest) :=
    (rt_record_sat_l hN.1 _ tg_control0_m .newest tg_control0_closed_l).mpr ⟨ν.bound,tuple,control⟩
  let φ : Formula 1 1 := rt_record_m tg_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ tg_control0_closed_l rfl
  obtain ⟨η,C,context,hr,reflect⟩ :=
    tg_context_native_l hZF certificate.model.2.1 ground p.ω r rules.omega [⟨1,φ,hc⟩]
  let ξ : Env N 1 := (⟨Fin.elim0,fun _ => p.ω⟩ : Env N 0).push r
  have reflection : Lr_reflect_d φ C := reflect ⟨1,φ,hc⟩ (List.mem_cons_self ..)
  have reflected := (reflection ξ (Fin.cases hr (fun i => Fin.elim0 i))).mp valid
  have record : Rt_record_in_d tg_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr,?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ξ.push C)
      (η := ⟨Fin.cases C (fun _ => r),fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  have fs := context.finite_l certificate.model.2.1 hN.1
  let nc : Nonempty {x : N.Domain // N.mem x C} := ⟨⟨p.ω,fs.omega_mem⟩⟩
  obtain ⟨_,v,pack,control⟩ :=
    (rt_record_in_read_l hN.1 tg_control0_m tg_control0_closed_l fs.transitive nc).mp record
  let ρ : Env (rt_model_l C nc) 19 := ⟨v,fun _ => v 0⟩
  have eqρ (i) : (ρ.bound i).val =
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i :=
    congrFun (rt_tuple_inj_l pack tuple) i
  let Kp := rt_pair_l fs.transitive nc hN.1 fs.pair
  have en := rt_model_ext_l hN.1 fs.transitive nc
  obtain ⟨a,h,j,_,_,_,_,_,_,_,_,_,w,seed,hw,_,_,_,_,hk,_,_,ht,_,_,_,_,nativeLetters,ℓ,issued⟩ :=
    tg_control_start_l Kp en ρ control
  let ε : Env (rt_model_l C nc) 38 := ⟨w,ρ.free⟩
  let ι := tg_issued_start_env_d ρ ε a h ℓ j
  -- 首请求中的 Vκ 是原模型的实际秩层；不把它解释成背景中的 Vκ。
  have facts := seed
  simp only [tg_seed0_m,tg_seed_m,Formula.satisfies_conj_iff] at facts
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,language,_⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0,.bound 5,.bound 7,.bound 14,.bound 15,
    .bound 16,.bound 27,.bound 28,.bound 29,.bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m :=
    (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m,Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hN) (w 5)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have inner : Vr_d C (w 5).val (w 14).val :=
    (vr_sat_l (ZF.modelsKP hN) fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have rankC := (rr_rank_native_l I certificate.model.2.1 (ZF.modelsKP hN) η C).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have rank : V_d (kp_pair_l (ZF.modelsKP hN)) (w 5).val (w 14).val :=
    inner.absolute_l (ZF.modelsKP hN) fs.transitive (w 14).property
      (fun A B hA sub => v_subset_mem_l (kp_pair_l (ZF.modelsKP hN)) rankC (A := A) (B := B) hA sub)
  have ew : (w 0).val = p.ω := (congrArg Subtype.val hw).trans (eqρ 0)
  have below₀ : N.mem (w 0).val (w 5).val :=
    tg_successor_omega_l ε ((context.kernel_l certificate.model.2.1 nc).renew_l ε seed)
  have below : N.mem p.ω (w 5).val :=
    Eq.mp (congrArg (fun x : N.Domain => N.mem x (w 5).val) ew) below₀
  have eA : (ρ.bound 6).val = p.A := eqρ 6
  have letters₀ : N.mem p.A (w 14).val :=
    eA ▸ (show N.mem (ρ.bound 6).val (w 14).val from nativeLetters)
  have omega := KP.v_ordinal_subset_l (ZF.modelsKP hN) rank p.ω below
  have emptyBelow := limit.1.transitive p.ω below p.e
    (num_mem_l hN.1 rules.omega (show Num_d 0 p.e from rules.empty))
  have rawLimit := (rr_truth_native_l I certificate.model.2.1 (Formula.isLimitOrdinal .newest)
    (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (w 5).val)).mpr
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limit)
  have rawRank := (rr_rank_native_l I certificate.model.2.1 (ZF.modelsKP hN) (w 5).val (w 14).val).mpr rank
  obtain ⟨r',saved,values⟩ := rf_record_save_l I certificate.model.2.1 hN.1
    tg_issued0_m tg_issued0_closed_l C fs.transitive fs.pair nc ι issued
  obtain ⟨K,source⟩ := certificate.source_l hZF hΩ numbers
  obtain ⟨o,α,T,Q,J,empty,succ,tree⟩ :=
    it_root_l hZF ⟨hΩ,X,R,p.ω.val,K,z,certificate.model,source,numbers⟩
  obtain ⟨q,edge⟩ := tree.diagram.map_l hZF (tree.diagram.order.refl o succ.predecessor_mem)
  have node := tree.root o empty
  have rootMap := tree.diagram.elementary o o q c X R c X R edge node node certificate.model certificate.model
  have fixed x (hx : M.mem x X) : Rd_entry_d x x q := by
    obtain ⟨y,_,image⟩ := rootMap.1.1.2.2 x hx
    exact (tree.diagram.identity o q edge x y image).symm ▸ image
  obtain ⟨F₀,finite⟩ := source.sequences.space_l I p.A.property
  obtain ⟨A₀,J₀,D₀,t₀,carrier,space,domain,bijection,codes,_⟩ :=
    numbers.finite_codes_l hZF hN.1 (KP.exists_pair (ZF.modelsKP hN)) (KP.exists_union (ZF.modelsKP hN))
      hΩ p.A ⟨F₀,finite.mem_l⟩ finite
  obtain ⟨k₀,rest⟩ := ZF.exists_restriction hZF I q A₀
  have fk := fn0_of_function_l (ZF.modelsKP hZF)
    (rest.isSetFunctionFromTo rootMap.1.1 (fun x hx => ((carrier x).mp hx).1))
  have letter x y (hxy : Rd_entry_d x y k₀) : x = y :=
    tree.diagram.identity o q edge x y ((rest.2 x y).mp hxy).2
  have fk' := fn0_function_l (ZF.modelsKP hZF) (fk.retarget_l
    (fun x y hxy => letter x y hxy ▸ ((rest.2 x y).mp hxy).1))
  have letters : M.IsSetBijectionFromTo I k₀ A₀ A₀ :=
    ⟨⟨fk',fun x y v hx hy => (letter x v hx).trans (letter y v hy).symm⟩,
      fun x hx => ⟨x,hx,(rest.2 x x).mpr ⟨hx,fixed x ((carrier x).mp hx).1⟩⟩⟩
  have zero : (ι.bound 19).val.val = p.e.val := congrArg Subtype.val (eqρ 1)
  have alphabet : (ι.bound 6).val.val = p.A.val := congrArg Subtype.val (eqρ 6)
  have ho := num_mem_l hZF.1 hΩ (show Num_d 0 o from empty)
  obtain ⟨e',he',point⟩ := numbers.injection.1.2.2 o ho
  have eq : e' = p.e.val := congrArg Subtype.val (hN.1.eq_of_same_members (⟨e',he'⟩ : N.Domain) p.e
    (fun x => iff_of_false (fun hx => by
      obtain ⟨i,hi,_⟩ := (numbers.predecessors o e' point x.val).mp hx
      exact empty i hi) (rules.empty x)))
  have point : Rd_entry_d o (ι.bound 19).val.val z := zero.symm ▸ eq ▸ point
  obtain ⟨f,play⟩ := context.prefix_l hZF certificate.model.2.1 hN.1 nc ι issued numbers point
    (fun y => alphabet.symm ▸ carrier y) letters rest
  refine ⟨η.val,C.val,r'.val,context,saved,(fun i => (ι.bound i).val.val),values,?_,
    zero,congrArg Subtype.val ((congrArg Subtype.val ht).trans (eqρ 1)),
    congrArg Subtype.val ((congrArg Subtype.val hk).trans (eqρ 1)),rawLimit,rawRank,omega,
    letters₀,emptyBelow,o,α,T,Q,J,empty,succ,tree,node,
    q,A₀,F₀,J₀,D₀,t₀,k₀,f,edge,fixed,finite,carrier,space,domain,bijection,codes,letters,rest,play,
    Tg_raw_archive_links_d.empty_l I empty⟩
  intro i
  simp only [ι,tg_issued_start_env_d,Fin.addCases_left]
  rw [eqρ]
  exact (List.getElem_map Subtype.val
    (l := [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H])
    (i := i.val) (h := i.isLt)).symm

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原辅助游戏直接生产共享零轮控制实例 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定原生游戏实际产生原控制及首请求，并在同一原模型码上建立单根树。 -/
theorem Tg_game_d.zero_native_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D B W O Z g σ : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (root : (smdl_structure_l I (R := R) certificate.model.2.1).mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ) :
    ∃ H η C r, M.mem H X ∧ Tg_context_d I p.ω.val X R η C ∧
      Rf_record_d I X R tg_issued0_m C r ∧ ∃ u : Fin 46 → M.Domain,
      Rf_tuple_d I X R u r ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H].get i) ∧
      u 19 = p.e.val ∧ u 23 = p.e.val ∧ u 26 = p.e.val ∧
      Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => u 24) ∧
      Rr_rank_d I X R (u 24) (u 29) ∧ Rd_entry_d p.ω.val (u 29) R ∧
      Rd_entry_d p.A.val (u 29) R ∧ Rd_entry_d p.e.val (u 24) R ∧
      ∃ o α T Q J, (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α o ∧
        It_tree_d hZF Ω c α T Q J o ∧ Rd_entry_d o c Q ∧
        ∃ q A₀ F₀ J₀ D₀ t₀ k₀ f,
          It_map_d J o o q ∧ (∀ x, M.mem x X → Rd_entry_d x x q) ∧
          Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧
          (∀ x, M.mem x A₀ ↔ M.mem x X ∧ Rd_entry_d x p.A.val R) ∧ Fseq_space_d I Ω A₀ J₀ ∧
          (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
          M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
          (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
          M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
          Tg_prefix_d I o A₀ X R C (u 4) (u 3) (u 20) z q f ∧
          Tg_raw_archive_links_d I ⟨o,o,Q,J,o⟩ o := by
  have ground := certificate.native_l I hZF hΩ
  obtain ⟨H,_,_,control,_⟩ := game.control_l ground woodin root win
  obtain ⟨η,C,r,context,record,u,tuple,header,rest⟩ :=
    tg_control_zero_l hZF hΩ certificate numbers control
  exact ⟨H.val,η,C,r,H.property,context,record,u,tuple,header,rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一控制记录的完整首请求

直接消费零轮生产者返回的原记录、原树、根图和前缀。首请求的根切片
由这一次请求自身的原生 Vκ 建立；所有字母图仍是同一根图的同一限制。
这里只闭合实际初态，不预设尚未构造的原运行后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一控制记录自产首请求、根切片及原前缀，全部根对象保持原值。 -/
theorem tg_control_raw_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D σ H : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (control : Formula.satisfies (⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,
      fun _ => p.ω⟩ : Env (smdl_structure_l I (R := R) certificate.model.2.1) 19) tg_control0_m) :
    ∃ η C r, ∃ u : Fin 46 → M.Domain, ∃ o m T Q J q A₀ F₀ J₀ D₀ t₀ k₀ f Dₛ,
      M.mem H.val X ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H.val].get i) ∧
      u 23 = u 1 ∧
      (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf m o ∧ It_tree_d hZF Ω c m T Q J o ∧ Rd_entry_d o c Q ∧
      M.IsSetFunction I o ∧
      (∀ i L, Rd_entry_d i L o ↔ ∃ p κ F, Rd_entry_d i p o ∧ It_payload_d p κ L F) ∧
      Tg_root_cut_d I c X R p.ω.val (u 24) (u 29) p.A.val Dₛ A₀ ∧
      Tg_raw_request_d I Ω p.S.val X R (u 24) Dₛ C p.A.val X R p.ω.val η C p.e.val z o o r q
        ⟨o,o,Q,J,o⟩ u ∧
      Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧ Fseq_space_d I Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
      M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
      Tg_prefix_d I o A₀ X R C (u 4) (u 3) (u 20) z q f := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have ground := certificate.native_l I hZF hΩ
  have native := ZF.modelsKP (ZFC.models_zf_l ground)
  let ν : Env N 19 := ⟨fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,fun _ => p.ω⟩
  have facts := control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at facts
  have rules : Tg_rules_d (ZFC.models_zf_l ground) p A F L D :=
    (tg_rules_sat_l (ZFC.models_zf_l ground) ν (tg_control_params_d Term.bound)
      (.bound 12) (.bound 13) (.bound 14) (.bound 16)).mp facts.2.2.1
  have hH := H.property
  obtain ⟨η,C,r,context,record,u,tuple,header,zero,tagZero,_,limit,rank,omega,alphabet,emptyBelow,
    o,m,T,Q,J,empty,succ,tree,node,q,A₀,F₀,J₀,D₀,t₀,k₀,f,edge,fixed,finite,carrier,space,domain,
    bij,codes,_,restriction,play,links⟩ := tg_control_zero_l hZF hΩ certificate numbers control
  have omegaEq : u 0 = p.ω.val := header 0
  have alphabetEq : u 6 = p.A.val := header 6
  have nameEq : u 7 = p.S.val := header 7
  have map := tree.diagram.elementary o o q c X R c X R edge node node certificate.model certificate.model
  obtain ⟨Dₛ,cut⟩ := tg_root_cut_l hZF certificate.model rank limit omega alphabet carrier
  obtain ⟨t,slice⟩ := cut.identity_l hZF native map.1.1.1 fixed context.member
  have name : Rd_entry_d p.S.val (u 7) q := by
    rw [nameEq]
    exact fixed p.S.val p.S.property
  have image : Rd_entry_d p.A.val (u 6) q := by
    rw [alphabetEq]
    exact fixed p.A.val p.A.property
  -- 新切片读取出的字母图与零轮已有图具有同一限制方程，故仍保留原 k₀。
  obtain ⟨E,k,range,letters,rest⟩ := cut.alphabet_l hZF native slice map.1.1.1 image
  have eqE : E = A₀ := hZF.1.eq_of_same_members E A₀ (fun y =>
    (range y).trans (by simpa only [alphabetEq] using (carrier y).symm))
  subst E
  have eqk := rest.eq hZF.1 restriction
  subst k
  have ho := num_mem_l hZF.1 hΩ (show Num_d 0 o from empty)
  obtain ⟨e,he,point⟩ := numbers.injection.1.2.2 o ho
  have eq : e = p.e.val := congrArg Subtype.val (native.1.eq_of_same_members (⟨e,he⟩ : N.Domain) p.e
    (fun x => iff_of_false (fun hx => by
      obtain ⟨i,hi,_⟩ := (numbers.predecessors o e point x.val).mp hx
      exact empty i hi) (rules.empty x)))
  have index : M.PairMember I o (u 19) z := zero.symm ▸ eq ▸ point
  have heω := num_mem_l native.1 rules.omega (show Num_d 0 p.e from rules.empty)
  have ordinal : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => p.e.val) :=
    (rr_truth_native_l I certificate.model.2.1 (KP.ord0_m .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => p.e)).mpr
        ((KP.ord0_sat_l native _ .newest).mpr (rules.omega.members_areOrdinals native p.e heω))
  have no_entry {i x} (h : M.PairMember I i x o) : False := h.elim fun p hp => empty p hp.2
  have sequence : M.IsSequenceOfLength I o o :=
    ⟨hΩ.members_areOrdinals (ZF.modelsKP hZF) o ho,
      ⟨fun p hp => (empty p hp).elim,fun _ _ _ hp _ => (no_entry hp).elim⟩,
      fun i => ⟨fun hi => (empty i hi).elim,fun ⟨x,hx⟩ => (no_entry hx).elim⟩⟩
  have levels i L : Rd_entry_d i L o ↔ ∃ p κ F, Rd_entry_d i p o ∧ It_payload_d p κ L F :=
    ⟨fun h => (no_entry h).elim,fun ⟨_,_,_,h,_⟩ => (no_entry h).elim⟩
  have reset : u 23 = u 1 := tagZero.trans (show u 1 = p.e.val from header 1).symm
  have views : Tg_raw_archive_views_d I Ω p.S.val X R (u 24) Dₛ C q o X R p.e.val p.ω.val C
      (u 4) (u 1) (u 2) (u 3) z (u 20) := Tg_raw_archive_views_d.empty_l I empty
  have request : Tg_raw_request_d I Ω p.S.val X R (u 24) Dₛ C p.A.val X R p.ω.val η C p.e.val z o o r q
      ⟨o,o,Q,J,o⟩ u :=
    ⟨context,record,tuple,omegaEq,hΩ,numbers,ho,index,sequence,links,edge,name,image,
      views,
      ordinal,emptyBelow,u 24,u 29,t,slice,omega,fun _ h => h⟩
  exact ⟨η,C,r,u,o,m,T,Q,J,q,A₀,F₀,J₀,D₀,t₀,k₀,f,Dₛ,hH,header,reset,empty,succ,tree,node,
    sequence.2.1,levels,cut,request,
    finite,space,domain,bij,codes,letters,restriction,play⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原辅助游戏直接调用共享的完整控制初态 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原生游戏的同一次零轮直接给出有完整根切片的首请求与原前缀。 -/
theorem Tg_game_d.raw_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D B W O Z g σ : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (root : (smdl_structure_l I (R := R) certificate.model.2.1).mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ) :
    ∃ H η C r, ∃ u : Fin 46 → M.Domain, ∃ o m T Q J q A₀ F₀ J₀ D₀ t₀ k₀ f Dₛ,
      M.mem H X ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H].get i) ∧
      u 23 = u 1 ∧
      (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf m o ∧ It_tree_d hZF Ω c m T Q J o ∧ Rd_entry_d o c Q ∧
      M.IsSetFunction I o ∧
      (∀ i L, Rd_entry_d i L o ↔ ∃ p κ F, Rd_entry_d i p o ∧ It_payload_d p κ L F) ∧
      Tg_root_cut_d I c X R p.ω.val (u 24) (u 29) p.A.val Dₛ A₀ ∧
      Tg_raw_request_d I Ω p.S.val X R (u 24) Dₛ C p.A.val X R p.ω.val η C p.e.val z o o r q
        ⟨o,o,Q,J,o⟩ u ∧
      Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧ Fseq_space_d I Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
      M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
      Tg_prefix_d I o A₀ X R C (u 4) (u 3) (u 20) z q f := by
  obtain ⟨H,_,_,control,_⟩ := game.control_l (certificate.native_l I hZF hΩ) woodin root win
  exact ⟨H.val,tg_control_raw_start_l hZF hΩ certificate numbers control⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一般原模型的实际六十六项初态

同一次零轮给出原树、空支撑列、完整请求、根切片及原前缀。
二十项头部只打包这些已经生成的对象；原有限列的双射仍保留，
供运行上层把外部原局与给定模型中的原游戏对应。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_control_iteration_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D σ H : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (control : Formula.satisfies (⟨fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,D,σ,H].get i,
      fun _ => p.ω⟩ : Env (smdl_structure_l I (R := R) certificate.model.2.1) 19) tg_control0_m) :
    ∃ η C r, ∃ u : Fin 46 → M.Domain, ∃ o m T Q J q A₀ F₀ J₀ D₀ t₀ k₀ f Dₛ,
      M.mem H.val X ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H.val].get i) ∧
      u 23 = u 1 ∧ (∀ x, ¬ M.mem x o) ∧
      Tg_root_cut_d I c X R p.ω.val (u 24) (u 29) p.A.val Dₛ A₀ ∧
      Tg_raw_iteration_d hZF Ω c o X R (u 24) Dₛ C p.S.val p.A.val A₀
        (fun i => [X,R,p.ω.val,z,η,C,m,o,T,Q,J,o,o,o,p.e.val,c,q,r,o,f].get i) u ∧
      Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧ Fseq_space_d I Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
      M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
      ∃ s, Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain)
        (fun i => [X,R,p.ω.val,z,η,C,m,o,T,Q,J,o,o,o,p.e.val,c,q,r,o,f].get i) u) s ∧
        Tg_raw_iteration_code_d hZF Ω c o X R (u 24) Dₛ C p.S.val p.A.val A₀ s := by
  obtain ⟨η,C,r,u,o,m,T,Q,J,q,A₀,F₀,J₀,D₀,t₀,k₀,f,Dₛ,hH,header,reset,empty,succ,tree,node,
    function,levels,cut,request,finite,space,domain,bij,codes,letters,restriction,play⟩ :=
    tg_control_raw_start_l hZF hΩ certificate numbers control
  let v : Fin 20 → M.Domain := fun i => [X,R,p.ω.val,z,η,C,m,o,T,Q,J,o,o,o,p.e.val,c,q,r,o,f].get i
  have state : Tg_raw_iteration_d hZF Ω c o X R (u 24) Dₛ C p.S.val p.A.val A₀ v u :=
    ⟨request.finite,succ,tree,function,levels,node,certificate.model,node,request,play,
      Tg_raw_critical_d.empty_l I empty⟩
  obtain ⟨s,tuple,code⟩ := state.pack_l hZF
  exact ⟨η,C,r,u,o,m,T,Q,J,q,A₀,F₀,J₀,D₀,t₀,k₀,f,Dₛ,hH,header,reset,empty,cut,state,
    finite,space,domain,bij,codes,letters,restriction,s,tuple,code⟩


theorem Tg_game_d.raw_iteration_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D B W O Z g σ : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (root : (smdl_structure_l I (R := R) certificate.model.2.1).mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ) :
    ∃ H η C r, ∃ u : Fin 46 → M.Domain, ∃ o m T Q J q A₀ F₀ J₀ D₀ t₀ k₀ f Dₛ,
      M.mem H X ∧
      (∀ i : Fin 19, u (i.castAdd 27) =
        [p.ω.val,p.e.val,p.a.val,p.b.val,p.c.val,p.δ.val,p.A.val,p.S.val,p.ν.val,
          p.E.val,p.P.val,p.Q.val,A.val,F.val,L.val,G.val,D.val,σ.val,H].get i) ∧
      u 23 = u 1 ∧ (∀ x, ¬ M.mem x o) ∧
      Tg_root_cut_d I c X R p.ω.val (u 24) (u 29) p.A.val Dₛ A₀ ∧
      Tg_raw_iteration_d hZF Ω c o X R (u 24) Dₛ C p.S.val p.A.val A₀
        (fun i => [X,R,p.ω.val,z,η,C,m,o,T,Q,J,o,o,o,p.e.val,c,q,r,o,f].get i) u ∧
      Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧ Fseq_space_d I Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
      M.IsSetBijectionFromTo I k₀ A₀ A₀ ∧ M.IsRestrictionOf I k₀ q A₀ ∧
      ∃ s, Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain)
        (fun i => [X,R,p.ω.val,z,η,C,m,o,T,Q,J,o,o,o,p.e.val,c,q,r,o,f].get i) u) s ∧
        Tg_raw_iteration_code_d hZF Ω c o X R (u 24) Dₛ C p.S.val p.A.val A₀ s := by
  obtain ⟨H,_,_,control,_⟩ := game.control_l (certificate.native_l I hZF hΩ) woodin root win
  exact ⟨H.val,tg_control_iteration_start_l hZF hΩ certificate numbers control⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原辅助游戏直接产生统一的原运行表

根模型中的实际胜策给出零轮，随后在所有原输入之前固定一次响应表。
原字母及有限列的解释仍取自同一次初始化。字母成员条件置于响应表之后，
不把原字母集的非空性偷偷加入开局构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.raw_recursion_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G D B W O Z g σ : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l I hZF hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F D B W σ) :
    ∃ o γ V Dₛ C A₀ F₀ J₀ D₀ t₀ r Xs Ds K,
      (∀ x, ¬ M.mem x o) ∧ Tg_root_cut_d I c X R p.ω.val γ V p.A.val Dₛ A₀ ∧
      Sc_fseq_d I p.ω.val p.A.val F₀ X R ∧ Fseq_space_d I Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo I t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d I Ω A₀ X R z s t) ∧
      Tg_raw_iteration_choice_d hZF Ω c o X R γ Dₛ C p.S.val p.A.val A₀ r Xs Ds K ∧
      Rt_coord_d (18 : Fin 66) r o ∧
      ∀ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain,
        (smdl_structure_l I (R := R) certificate.model.2.1).mem a p.A →
        M.mem a.val A₀ ∧ ∀ f, Fn0_d Ω A₀ f → ∃ H,
          Tg_raw_iteration_run_d hZF Ω c o X R γ Dₛ C p.S.val p.A.val A₀ Xs K r a.val f H := by
  have root := game.win_root_l (certificate.native_l I hZF hΩ) win
  obtain ⟨H,η,C,r₀,u,o,m,T,Q,J,q,A₀,F₀,J₀,D₀,t₀,k₀,f₀,Dₛ,_,_,_,empty,cut,initial,
    finite,space,domain,bij,codes,_,_,r,tuple,code⟩ :=
    game.raw_iteration_start_l hZF hΩ certificate numbers woodin root win
  obtain ⟨Xs,Ds,K,choice⟩ := code.choice_l hZFC certificate cut
  have zero : Rt_coord_d (18 : Fin 66) r o := ⟨_,tuple,by rfl⟩
  refine ⟨o,u 24,u 29,Dₛ,C,A₀,F₀,J₀,D₀,t₀,r,Xs,Ds,K,
    empty,cut,finite,space,domain,bij,codes,choice,zero,?_⟩
  intro a ha
  have member : M.mem a.val A₀ := (cut.letters a.val).mpr ⟨a.property,ha⟩
  refine ⟨member,fun f ff => ?_⟩
  exact choice.run_l hZF zero empty member (fn0_function_l (ZF.modelsKP hZF) ff).1
    (fun _ _ h => (ff.bound_l h).2)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原状态中的实际对局前缀及末项

坐标 19 保存背景原局，坐标 18 为其精确定义域。两次实际原边给出的
追加关系直接确定末项；整个读取不更换原关系模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_code_d.play_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r f : M.Domain}
    (h : Tg_raw_iteration_code_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r)
    (play : Rt_coord_d (19 : Fin 66) r f) :
    ∃ n, Rt_coord_d (18 : Fin 66) r n ∧ Fn0_d n A f := by
  obtain ⟨v,code,state⟩ := h
  exact ⟨v 18,⟨v,code,rfl⟩,(play.read_l v code) ▸ state.play.1⟩

/-- 完整原后继的同一次追加同时给出末值及偶数轮的输入规则。 -/
theorem Tg_raw_iteration_edge_d.last_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A x s t n : M.Domain}
    (edge : Tg_raw_iteration_edge_d hZF ω c A x s t)
    (old : Tg_raw_iteration_code_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s)
    (index : Rt_coord_d (18 : Fin 66) s n) :
    ∃ m f g y, Rt_coord_d (18 : Fin 66) t m ∧ Rt_coord_d (19 : Fin 66) s f ∧
      Rt_coord_d (19 : Fin 66) t g ∧ M.SuccessorOf m n ∧ Fseq_end_d I ω g f y ∧
      Rd_entry_d n y g ∧ (Gm_even_d I ω n → y = x) := by
  obtain ⟨v,w,ps,pt,next⟩ := edge
  have current : Rt_coord_d (19 : Fin 66) s (v 19) := ⟨v,ps,rfl⟩
  obtain ⟨n',num,fn⟩ := old.play_l hZF current
  have fn : Fn0_d n A (v 19) := num.unique_l index ▸ fn
  have vn : v 18 = n := index.read_l v ps
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,succ,y,_,ends,even,_⟩ := next
  obtain ⟨l,k,last⟩ := ends
  have kn := last.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  exact ⟨w 18,v 19,w 19,y,⟨w,pt,rfl⟩,current,⟨w,pt,rfl⟩,vn ▸ succ,
    ⟨l,k,last⟩,kn ▸ last.last_value,vn ▸ even⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一响应表上的实际原博弈策略

有限输入先递归到其长度，再用固定字母查询下一状态，并读取该状态原局的末项。
递归因果性和状态码唯一性保证输出唯一；替换实际收集整张策略函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_raw_iteration_response_d (ω X K r a s y : M.Domain) : Prop := ∃ n H u p t q,
  M.IsDomainOf I n s ∧ Gi_d hZF true ω X K r a s H ∧ Rd_entry_d n u H ∧
    (I).Codes p u a ∧ Rd_entry_d p t K ∧ Rt_coord_d (19 : Fin 66) t q ∧ Rd_entry_d n y q

def tg_raw_iteration_response_m {d} (ω X K r a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H u p t q,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n,⌜s⌝ₛ) ∧
  ⌜(gi_m true)⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜s⌝ₛ,H) ∧
  ⌜rd_entry0_m⌝ₚ(n,u,H) ∧ ⌜kpair_m⌝ₚ(p,u,⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ) ∧
  ⌜(rt_coord_m (19 : Fin 66))⌝ₚ(t,q) ∧ ⌜rd_entry0_m⌝ₚ(n,⌜y⌝ₛ,q)⟫
derive_free_closed tg_raw_iteration_response_m

theorem tg_raw_iteration_response_sat_l {d} (ρ : Env M d) (ω X K r a s y : Term d) :
    Formula.satisfies ρ (tg_raw_iteration_response_m ω X K r a s y) ↔
      Tg_raw_iteration_response_d hZF (ω.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [tg_raw_iteration_response_m,Tg_raw_iteration_response_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_isDomain_iff I,gi_sat_l hZF true,
    rd_entry0_sat_l hZF.1,kpair_sat_l M hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_raw_iteration_choice_d.response_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a s n : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) :
    ∃ y, Tg_raw_iteration_response_d hZF ω X K r a s y := by
  obtain ⟨H,run⟩ := h.run_l hZF zero empty ha fs.1 (fun _ _ hi => fs.output_mem_of_pairMember hi)
  obtain ⟨u,hu,nu⟩ := run.recursion.1.2.1 n hn
  obtain ⟨p,pair⟩ := (I).total u a
  obtain ⟨t,_,pt⟩ := h.function.2.1 p ((h.product p).mpr ⟨u,hu,a,ha,pair⟩)
  have state := run.rows n u nu
  obtain ⟨_,edge⟩ := h.step u a t p state.1 pair pt
  obtain ⟨_,_,q,y,_,_,coord,_,_,last,_⟩ := edge.last_l hZF state.1 state.2
  exact ⟨y,n,H,u,p,t,q,fs.2.1,run.recursion,nu,pair,pt,coord,last⟩

theorem Tg_raw_iteration_choice_d.response_bound_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a s y : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (answer : Tg_raw_iteration_response_d hZF ω X K r a s y) : M.mem y A := by
  obtain ⟨n,H,u,p,t,q,_,run,nu,pair,pt,coord,last⟩ := answer
  have state := (h.validate_l hZF zero empty run).rows n u nu
  have next := (h.step u a t p state.1 pair pt).1
  obtain ⟨_,_,fn⟩ := next.play_l hZF coord
  exact (fn.bound_l last).2

theorem Tg_raw_iteration_choice_d.response_unique_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a s x y : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (fs : M.IsSetFunction I s) (hx : Tg_raw_iteration_response_d hZF ω X K r a s x)
    (hy : Tg_raw_iteration_response_d hZF ω X K r a s y) : x = y := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  obtain ⟨n,H,u,p,t,q,dom,run,nu,pair,pt,coord,last⟩ := hx
  obtain ⟨n',H',u',p',t',q',dom',run',nu',pair',pt',coord',last'⟩ := hy
  have nn := dom'.eq hZF.1 dom
  subst n'
  have fk := (fn0_function_l (ZF.modelsKP hZF) h.function).1
  have uu := run.agree_l hZF hw fk fs run' (run.1.bound_l nu).1 (fun _ _ _ => Iff.rfl) u u' nu nu'
  have pp := (I).unique pair (uu.symm ▸ pair')
  have tt := fk.2 p t t' pt (pp.symm ▸ pt')
  have qq := coord.unique_l (tt.symm ▸ coord')
  have state := (h.validate_l hZF zero empty run).rows n u nu
  have next := (h.step u a t p state.1 pair pt).1
  obtain ⟨_,_,fn⟩ := next.play_l hZF coord
  exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n x y last (qq.symm ▸ last')

theorem Tg_raw_iteration_choice_d.strategy_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a F : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) : ∃ σ, Fn0_d F A σ ∧
      ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_raw_iteration_response_d hZF ω X K r a s y := by
  let ρ : Env M 5 := ⟨fun i => [ω,X,K,r,a].get i,fun _ => ω⟩
  let φ : BinarySchema 5 := { body := (tg_raw_iteration_response_m (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 1) .newest) }
  have sat s y : φ.denote ρ s y ↔ Tg_raw_iteration_response_d hZF ω X K r a s y :=
    tg_raw_iteration_response_sat_l hZF ..
  obtain ⟨σ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := A) (by
    intro s hs
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨y,hy⟩ := h.response_l hZF zero empty ha hn fs
    exact ⟨y,(sat s y).mpr hy⟩) (by
    intro s hs x y hx hy
    obtain ⟨_,_,fs⟩ := (space s).mp hs
    exact h.response_unique_l hZF zero empty fs.1 ((sat s x).mp hx) ((sat s y).mp hy)) (by
    intro s y _ hy
    exact h.response_bound_l hZF zero empty ((sat s y).mp hy))
  exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun s y => (values s y).trans (and_congr_right fun _ => sat s y)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 服从同一实际策略的原运行与精确前缀

偶数轮读取输入，奇数轮用同一响应表及有限输入因果性读取策略。
模型内部归纳保证每个状态中的原局恰是给定对局的限制；随后直接取并
得到同一运行的原树与完整档案列，不附加工作初态或未证明的枝性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_choice_d.play_l {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a F σ f H : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_raw_iteration_response_d hZF ω X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f)
    (run : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H) :
    ∀ n u q, Rd_entry_d n u H → Rt_coord_d (19 : Fin 66) u q → M.IsRestrictionOf I q f n := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  have read {n u q} (nu : Rd_entry_d n u H) (play : Rt_coord_d (19 : Fin 66) u q) : Fn0_d n A q := by
    obtain ⟨k,num,fn⟩ := (run.rows n u nu).1.play_l hZF play
    exact num.unique_l (run.rows n u nu).2 ▸ fn
  let ρ : Env M 2 := ⟨fun i => [H,f].get i,fun _ => H⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ u q,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,u,⌜(.bound 1 : Term 3)⌝ₛ) →
    ⌜(rt_coord_m (19 : Fin 66))⌝ₚ(u,q) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(q,⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ u q, Rd_entry_d n u H → Rt_coord_d (19 : Fin 66) u q →
      M.IsRestrictionOf I q f n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_isRestriction_iff I,
      Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ u q, Rd_entry_d n u H → Rt_coord_d (19 : Fin 66) u q →
      M.IsRestrictionOf I q f n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz u q nu play
      have fq := read nu play
      exact ⟨(fn0_function_l (ZF.modelsKP hZF) fq).1.1,fun i y =>
        ⟨fun hi => (hz i (fq.bound_l hi).1).elim,fun hi => (hz i hi.1).elim⟩⟩
    · intro n hn ih m succ t q mt play
      obtain ⟨u,_,nu⟩ := run.recursion.1.2.1 n hn
      have state := run.rows n u nu
      obtain ⟨x,p,input,pair,pt⟩ := run.recursion.2.2 n m u t succ nu mt
      have edge := (h.step u x t p state.1 pair pt).2
      obtain ⟨_,s,q',y,_,old,new,_,ends,last,even⟩ := edge.last_l hZF state.1 state.2
      have qq := new.unique_l play
      subst q'
      have cut := ih u s nu old
      have fs := fn0_function_l (ZF.modelsKP hZF) (read nu old)
      obtain ⟨z,_,nz⟩ := ff.2.1 n hn
      have yz : y = z := by
        rcases Classical.em (Gm_even_d I ω n) with he | he
        · exact (even he).trans (input.elim (fun hx => fn.1.2 n x z hx.2 nz)
            (fun hx => (hx.1 ⟨he,z,nz⟩).elim))
        · have xa : x = a := input.elim (fun hx => (he hx.1).elim) And.right
          obtain ⟨G,grun⟩ := h.run_l hZF zero empty ha fs.1 (fun _ _ hi => fs.output_mem_of_pairMember hi)
          obtain ⟨u',_,nu'⟩ := grun.recursion.1.2.1 n hn
          have uu := run.recursion.prefix_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1
            fn.1 grun.recursion hn cut u u' nu nu'
          have response : Tg_raw_iteration_response_d hZF ω X K r a s y :=
            ⟨n,G,u,p,t,q,fs.2.1,grun.recursion,uu.symm ▸ nu',xa ▸ pair,pt,play,last⟩
          have sy := (values s y).mpr ⟨(space s).mpr ⟨n,hn,fs⟩,response⟩
          exact (fn0_function_l (ZF.modelsKP hZF) sf).1.2 s y z sy (follows n hn he s cut z nz)
      have fq := fn0_function_l (ZF.modelsKP hZF) (read mt play)
      apply (ds_restrict_iff_l I fq fn.1).mpr
      intro p hp
      obtain ⟨i,v,pair⟩ := fq.1.1 p hp
      have iv : Rd_entry_d i v q := ⟨p,pair,hp⟩
      have entry : Rd_entry_d i v f := by
        rcases (succ i).mp (fq.input_mem_of_pairMember iv) with hi | eq
        · obtain ⟨l,k,d⟩ := ends
          have kn := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
          exact ((cut.2 i v).mp ((d.prefix_restriction.2 i v).mpr ⟨kn.symm ▸ hi,iv⟩)).2
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          exact (fq.1.2 n v y iv last).symm ▸ yz.symm ▸ nz
      obtain ⟨p',pair',hp'⟩ := entry
      exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  exact fun n u q nu play => all n (run.recursion.1.bound_l nu).1 u q nu play

/-- 一张实际策略同时服务所有服从它的完整输入，同一次运行给出原并树。 -/
theorem Tg_raw_iteration_choice_d.strategy_run_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K a F : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) : ∃ σ, Fn0_d F A σ ∧
      (∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_raw_iteration_response_d hZF ω X K r a s y) ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d I false ω σ f → ∃ H U,
        Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H ∧
        Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U ∧
        ∀ n u q, Rd_entry_d n u H → Rt_coord_d (19 : Fin 66) u q → M.IsRestrictionOf I q f n := by
  obtain ⟨σ,sf,values⟩ := h.strategy_l hZF zero empty ha space
  refine ⟨σ,sf,values,fun f ff follows => ?_⟩
  obtain ⟨H,run⟩ := h.run_l hZF zero empty ha (fn0_function_l (ZF.modelsKP hZF) ff).1
    (fun _ _ hi => (ff.bound_l hi).2)
  obtain ⟨U,tree⟩ := run.union_l hZF
  exact ⟨H,U,run,tree,h.play_l hZF zero empty ha space sf values ff follows run⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 真实原初态、根切片和有限列空间直接构造策略及全部同表运行。 -/
theorem Tg_raw_iteration_d.strategy_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A a F : M.Domain}
    {v : Fin 20 → M.Domain} {u : Fin 46 → M.Domain}
    (root : Zc_model_d J ω c X₀ R₀)
    (cut : Tg_root_cut_d J c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (initial : Tg_raw_iteration_d hZ ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v u)
    (zero : v 18 = o) (empty : ∀ z, ¬ M.mem z o) (ha : M.mem a A)
    (space : Fseq_space_d J ω A F) : ∃ r X D K σ,
      Tg_raw_iteration_choice_d hZ ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K ∧
      Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain) v u) r ∧ Fn0_d F A σ ∧
      (∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_raw_iteration_response_d hZ ω X K r a s y) ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d J false ω σ f → ∃ H U,
        Tg_raw_iteration_run_d hZ ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H ∧
        Tg_raw_iteration_union_d hZ ω c o X₀ R₀ γ₀ D₀ C₀ H U ∧
        ∀ n u q, Rd_entry_d n u H → Rt_coord_d (19 : Fin 66) u q → M.IsRestrictionOf J q f n := by
  obtain ⟨r,X,D,K,code,choice⟩ := initial.choice_l hZFC root cut
  have index : Rt_coord_d (18 : Fin 66) r o := ⟨_,code,
    (Fin.addCases_left (m := 20) (n := 46) (motive := fun _ => M.Domain) (left := v) (right := u) 18).trans zero⟩
  obtain ⟨σ,sf,values,runs⟩ := choice.strategy_run_l hZ index empty ha space
  exact ⟨r,X,D,K,σ,choice,code,sf,values,runs⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原字母表上的实际 II 策略

统一响应表先于所有原输入固定。非空字母表使用已经构造的总策略，
仅保留 II 的回合；空字母表使用实际空策略。两种情形均遵循同一本方
策略定义，不给原游戏附加字母集非空的假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_iteration_choice_d.turn_strategy_l
    {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K F : M.Domain}
    (h : Tg_raw_iteration_choice_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A r X D K)
    (zero : Rt_coord_d (18 : Fin 66) r o) (empty : ∀ z, ¬ M.mem z o)
    (space : Fseq_space_d I ω A F) : ∃ σ, Gm_strategy_d I false ω A F σ ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d I false ω σ f → ∃ a H U, M.mem a A ∧
        Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H ∧
        Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U ∧
        ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n := by
  have hw := h.initial.elim fun _ h => h.2.tree.omega
  apply gm_ii_strategy_l hZF hw space
  intro a ha
  obtain ⟨σ,total,_,runs⟩ := h.strategy_run_l hZF zero empty ha space
  refine ⟨σ,total,fun f input follows => ?_⟩
  obtain ⟨H,U,run,tree,played⟩ := runs f input follows
  exact ⟨a,H,U,ha,run,tree,played⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 原辅助胜策的同一次开局直接产生原 II 策略及每份服从对局的完整原迭代。 -/
theorem Tg_game_d.raw_strategy_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d J Ω c X R)
    {p : Tg_params_d (smdl_structure_l J (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d J Ω X R p.ω.val z)
    {A F L G D B W O Z g σ : (smdl_structure_l J (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l J hZ hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l J hZ hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l J hZ hΩ)))) false p.ω A F D B W σ) :
    ∃ o γ V Dₛ C A₀ F₀ J₀ D₀ t₀ r Xs Ds K σ₀,
      (∀ x, ¬ M.mem x o) ∧ Tg_root_cut_d J c X R p.ω.val γ V p.A.val Dₛ A₀ ∧
      Sc_fseq_d J p.ω.val p.A.val F₀ X R ∧ Fseq_space_d J Ω A₀ J₀ ∧
      (∀ s, M.mem s D₀ ↔ M.mem s X ∧ Rd_entry_d s F₀ R) ∧
      M.IsSetBijectionFromTo J t₀ J₀ D₀ ∧
      (∀ s t, Rd_entry_d s t t₀ ↔ Rr_finite_d J Ω A₀ X R z s t) ∧
      Tg_raw_iteration_choice_d hZ Ω c o X R γ Dₛ C p.S.val p.A.val A₀ r Xs Ds K ∧
      Rt_coord_d (18 : Fin 66) r o ∧ Gm_strategy_d J false Ω A₀ J₀ σ₀ ∧
      ∀ f, Fn0_d Ω A₀ f → Gm_follows_d J false Ω σ₀ f → ∃ a H U, M.mem a A₀ ∧
        Tg_raw_iteration_run_d hZ Ω c o X R γ Dₛ C p.S.val p.A.val A₀ Xs K r a f H ∧
        Tg_raw_iteration_union_d hZ Ω c o X R γ Dₛ C H U ∧
        ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf J q f n := by
  obtain ⟨o,γ,V,Dₛ,C,A₀,F₀,J₀,D₀,t₀,r,Xs,Ds,K,empty,cut,finite,space,domain,bij,codes,choice,zero,_⟩ :=
    game.raw_recursion_l hZFC hΩ certificate numbers woodin win
  obtain ⟨σ₀,strategy,runs⟩ := choice.turn_strategy_l hZ zero empty space
  exact ⟨o,γ,V,Dₛ,C,A₀,F₀,J₀,D₀,t₀,r,Xs,Ds,K,σ₀,
    empty,cut,finite,space,domain,bij,codes,choice,zero,strategy,runs⟩

end YesMetaZFC.SetTheory.LargeCardinal
