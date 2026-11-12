import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawReset
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawContinue
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyStart
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate

/-! # 原 II 胜策的 demanding 迭代初态

首请求由原策略在空历史上的实际值产生。以它自身的 Vκ 建立根切片，
单根树、恒等根图和零长档案均在背景中构造；原模型的空集仍由数字图解释。
辅助字母的选择只用于已有的重置构造。主线使用原模型内部的实际幂集
编码及幂集计数，并将两者接入首请求，不要求整个原模型可数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 非空辅助域上的真实初态；所有根几何和空档案条件由原游戏构造。 -/
theorem Td_game_d.raw_start_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d I Ω c X R)
    {p : Tg_params_d (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d I Ω X R p.ω.val z)
    {A F L G J B W O Z g σ U₁ U₂ a : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (game : Td_game_d (certificate.native_l I hZF hΩ) p A F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) false p.ω A F J B W σ)
    (treeS : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l I hZF hΩ)))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) certificate.model.2.1).mem a U₁)
    (separated : Td_separated_d p.S)
    (powerCount : Pc_count_d I Ω X R p.δ.val)
    (coding : ∃ P, (smdl_structure_l I (R := R) certificate.model.2.1).IsPowerSetOf P p.δ ∧
      (smdl_structure_l I (R := R) certificate.model.2.1).CardinalLessOrEqual
        (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) U₁ P) :
    ∃ H, ∃ ι : Env (smdl_structure_l I (R := R) certificate.model.2.1) 47,
      (∀ i : Fin 19, ι.bound (i.castAdd 28) =
        [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i) ∧
      Formula.satisfies ι td_issued0_m ∧
      Formula.satisfies (ι.reindex (fun i : Fin 19 => i.castAdd 28))
        (td_reset_control_m (tg_control_params_d Term.bound)) ∧
      ι.bound 19 = p.e ∧ ι.bound 23 = ι.bound 1 ∧
      Rd_entry_d p.e (ι.bound 21) σ ∧
      Fseq_end_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ))))
        p.ω (ι.bound 20) p.e (ι.bound 21) ∧
    ∃ o m T Q G₀ q A₀ D₀ V t,
      (∀ x, ¬ M.mem x o) ∧ M.mem o Ω ∧ M.SuccessorOf m o ∧
      It_tree_d hZF Ω c m T Q G₀ o ∧ Rd_entry_d o c Q ∧ It_map_d G₀ o o q ∧
      (∀ x, M.mem x X → Rd_entry_d x x q) ∧
      Rd_entry_d p.A.val (ι.bound 6).val q ∧ Rd_entry_d p.S.val (ι.bound 7).val q ∧
      Tg_root_cut_d I c X R p.ω.val (ι.bound 24).val V p.A.val D₀ A₀ ∧
      Tg_root_slice_d I X R (ι.bound 24).val D₀ p.e.val X R p.e.val q (ι.bound 24).val V t ∧
      Rd_entry_d (ι.bound 0).val V R ∧ Rd_entry_d (ι.bound 6).val V R ∧
      Rd_entry_d p.e.val (ι.bound 5).val R ∧ Rd_entry_d p.e.val (ι.bound 24).val R ∧
      Rr_layer_d I Ω X R (ι.bound 0).val z ∧
      M.IsSequenceOfLength I o o ∧ Rd_entry_d o (ι.bound 19).val z ∧
      Td_archive_d I Ω c X p.A.val p.S.val o X R p.e.val
        (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ q ∧
      Td_archive_links_d o Q G₀ o o ∧ Pc_count_d I Ω X R (ι.bound 5).val ∧
      Td_code_d I X R (ι.bound 7).val (ι.bound 5).val := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have ground := certificate.native_l I hZF hΩ
  have native := ZFC.models_zf_l ground
  let K := kp_pair_l (ZF.modelsKP native)
  obtain ⟨v,pair⟩ := K.total p.e a
  have root := (show Td_pending_d K p.ω p.A p.e p.S v from
    ⟨treeS,a,pair,(alphabet.1 a).mp chosen⟩).root_l native game.setup.omega game.setup.empty
  obtain ⟨H,_,_,control,_⟩ := game.control_record_l ground woodin root win
  let ν : Env N 19 := ⟨fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,A,F,L,G,J,σ,H].get i,fun _ => p.ω⟩
  obtain ⟨ι,head,issued,zero,reset,first,ending⟩ := td_issued_start_l native ν control
  have h0 : ι.bound 0 = p.ω := head 0
  have h1 : ι.bound 1 = p.e := head 1
  have h5 : ι.bound 5 = p.δ := head 5
  have h6 : ι.bound 6 = p.A := head 6
  have h7 : ι.bound 7 = p.S := head 7
  have zero : ι.bound 19 = p.e := zero
  have hp : tg_control_params_d (fun i => ι.bound (i.castAdd 28)) = p :=
    congrArg tg_control_params_d (funext head)
  have setup : Td_setup_d ground
      ((tg_control_params_d (Term.bound : Fin 19 → Term 19)).map_l
        (fun t => t.eval (ι.reindex (fun i : Fin 19 => i.castAdd 28)))) A := by
    change Td_setup_d ground (tg_control_params_d (fun i => ι.bound (i.castAdd 28))) A
    rw [hp]
    exact game.setup
  have resetControl := td_reset_control_l ground (ι.reindex (fun i : Fin 19 => i.castAdd 28))
    (tg_control_params_d Term.bound) setup
    (show Woodin_d K (ι.bound 5) from h5.symm ▸ woodin)
  have heω := num_mem_l native.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have heδ := game.setup.limit.1.transitive p.ω game.setup.above p.e heω
  have reset' : ι.bound 23 = ι.bound 1 := reset.trans h1.symm
  have tree' : Td_tree_d K (ι.bound 0) (ι.bound 6) (ι.bound 7) := by
    exact h0.symm ▸ h6.symm ▸ h7.symm ▸ treeS
  obtain ⟨ξ,_,_,low,mid,ρ,same,round,_,_,_⟩ := td_issued_reset_l ground ι issued resetControl reset'
    tree' (h7.symm ▸ alphabet) chosen (h5.symm ▸ heδ) (h7.symm ▸ separated)
  -- 首个短扩展器本身给出 ω<κ；不把内部基数性当作背景基数性。
  obtain ⟨_,_,_,_,_,L₁,W₁,X₁,K₁,R₁,F₁,c₁,d₁,Y₁,S₁,j₁,κ₁,U',E',u',image⟩ :=
    td_round_native_l (ZF.modelsKP native) ρ round
  obtain ⟨_,_,_,_,_,_,_,locality,_,_,model,_⟩ := image
  obtain ⟨_,_,_,_,short⟩ := (it_local_mem_l K ⟨c₁,model⟩).mp locality
  have pre := (Formula.satisfies_conj_iff ..).mp short |>.1
  simp only [ex_pre_m,Formula.satisfies_conj_iff] at pre
  have above : N.mem (ρ.bound 19) (ρ.bound 24) := (Formula.satisfies_mem_iff ..).mp pre.2.2.1
  have hw : ρ.bound 19 = p.ω := (same 0).trans ((low 0).trans (head 0))
  have hκ : ρ.bound 24 = ι.bound 24 := (same 5).trans (mid 2)
  have above : N.mem p.ω (ι.bound 24) := hw ▸ hκ ▸ above
  -- 零轮的增长规则强制原字母表已经落在本次 Vκ 内。
  have state := (td_issued_sat_l K native.1 ι).mp issued
  have aux := state.auxiliary
  simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_end_sat_l K native.1,td_aux_sat_l native] at aux
  obtain ⟨h,_,aux⟩ := aux
  change Td_aux_d native (tg_control_params_d (fun i => ι.bound (i.castAdd 28)))
    (ι.bound 19) h (ι.bound 21) at aux
  rw [hp] at aux
  obtain ⟨ℓ,k,κ,u,d,q₁,n₁,m₁,x,s,B₁,U,Du,Dw,pn,pm,pp,pb,ph,C₁,V₁,E₁,g₀,g₁,g₂,g₃,
    move,_,hκδ,_,_,_,request,query,_,_,_,_,growth,_⟩ := aux
  have eqκ : κ = ι.bound 24 := (move.unique_l state.payload.1).2.2.1
  obtain ⟨_,_,_,_,_,rank,_,_⟩ := game.setup.queries.read_l ground hκδ request query
  have letters : N.mem p.A B₁ := growth.elim And.right (fun old => by
    obtain ⟨j,_,_,_,_,_,succ,_⟩ := old
    exact (game.setup.empty j (zero ▸ succ.predecessor_mem)).elim)
  have rank : V_d K (ι.bound 24) B₁ := eqκ ▸ rank
  have limit : N.IsLimitOrdinal (ι.bound 24) := eqκ ▸ request.1
  have omegaLow := ZF.v_ordinal_mem_l K native rank above
  have emptyBelow := limit.1.transitive p.ω above p.e heω
  have rawRank := (rr_rank_native_l I certificate.model.2.1 (ZF.modelsKP native) (ι.bound 24) B₁).mpr rank
  have rawLimit := (rr_truth_native_l I certificate.model.2.1 (Formula.isLimitOrdinal .newest)
    (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ι.bound 24)).mpr
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limit)
  obtain ⟨K₀,source⟩ := certificate.source_l hZF hΩ numbers
  obtain ⟨o,m,T,Q,G₀,empty,succ,tree⟩ :=
    it_root_l hZF ⟨hΩ,X,R,p.ω.val,K₀,z,certificate.model,source,numbers⟩
  have node := tree.root o empty
  obtain ⟨q,edge⟩ := tree.diagram.map_l hZF (tree.diagram.order.refl o succ.predecessor_mem)
  have map := tree.diagram.elementary o o q c X R c X R edge node node certificate.model certificate.model
  have fixed x (hx : M.mem x X) : Rd_entry_d x x q := by
    obtain ⟨y,_,xy⟩ := map.1.1.2.2 x hx
    exact (tree.diagram.identity o q edge x y xy).symm ▸ xy
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨A₀,as⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases p.A.val (fun _ => R),fun _ => X⟩ X
  have carrier x : M.mem x A₀ ↔ M.mem x X ∧ Rd_entry_d x p.A.val R :=
    (as x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨D₀,cut⟩ := tg_root_cut_l hZF certificate.model rawRank rawLimit omegaLow
    letters carrier
  obtain ⟨t,slice⟩ := cut.identity_l hZF (ZF.modelsKP native) map.1.1.1 fixed p.e.property
  have ho := num_mem_l hZF.1 hΩ (show Num_d 0 o from empty)
  obtain ⟨e,he,point⟩ := numbers.injection.1.2.2 o ho
  have ee : e = p.e.val := congrArg Subtype.val (native.1.eq_of_same_members (⟨e,he⟩ : N.Domain) p.e
    (fun x => iff_of_false (fun hx => by
      obtain ⟨i,hi,_⟩ := (numbers.predecessors o e point x.val).mp hx
      exact empty i hi) (game.setup.empty x)))
  obtain ⟨sequence,archive⟩ := td_archive_empty_l I (Ar := p.A.val) (Sr := p.S.val)
    (Ω := Ω) (c₀ := c) (X₀ := X) (N := X) (R := R) (χ := p.e.val)
    (c := (ι.bound 4).val) (e := (ι.bound 1).val) (a := (ι.bound 2).val)
    (z := z) (h := (ι.bound 20).val) (D₀ := D₀) (q := q) empty
  obtain ⟨P,hP,code⟩ := coding
  have alphabetCode := td_code_l hZF certificate.model.2.1 (ZF.modelsKP native)
    p.S p.δ U₁ U₂ P alphabet hP code
  refine ⟨H,ι,head,issued,resetControl,zero,reset',first,?_,o,m,T,Q,G₀,q,A₀,D₀,B₁.val,t,
    empty,ho,succ,tree,node,edge,fixed,?_,?_,cut,slice,?_,?_,?_,emptyBelow,?_,sequence,?_,
    archive,Td_archive_links_d.empty_l empty,(congrArg Subtype.val h5).symm ▸ powerCount,
    (congrArg Subtype.val h7).symm ▸ (congrArg Subtype.val h5).symm ▸ alphabetCode⟩
  · exact ending
  · exact (congrArg Subtype.val h6).symm ▸ fixed p.A.val p.A.property
  · exact (congrArg Subtype.val h7).symm ▸ fixed p.S.val p.S.property
  · exact (congrArg Subtype.val h0).symm ▸ omegaLow
  · exact (congrArg Subtype.val h6).symm ▸ letters
  · exact (congrArg Subtype.val h5).symm ▸ heδ
  · exact (congrArg Subtype.val h0).symm ▸ numbers
  · exact (congrArg Subtype.val zero).symm ▸ ee ▸ point

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 内部运行的统一有限状态

固定数据是原根及其切片；十九项头部保存实际树、当前模型、档案和支撑列。
四十七槽请求保留原控制。额外静态句只记录已由初态产生、沿原边运输的
重置控制、树、两侧分离和第一字母域非空性。
活动边还保存所属关系模型内的实际秩源、最大强度及不可达支撑，供后续复制读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u v
variable {M : Structure.{u}}

def td_static0_m : Formula 1 19 := .conj
  (td_reset_control_m (tg_control_params_d Term.bound))
  (.conj (td_tree_m (.bound 0) (.bound 6) (.bound 7))
    (.conj (td_separated_m (.bound 7)) (.existsE (td_letter_m false (.bound 8) .newest))))

theorem td_static0_closed_l : td_static0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_static0_m,Definitional.Formula.FreeClosed,tg_control_params_d]
  exact td_reset_control_closed_l _ ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem td_static0_sat_l (hKP : M.Models KP) (ρ : Env M 19) :
    Formula.satisfies ρ td_static0_m ↔
      Formula.satisfies ρ (td_reset_control_m (tg_control_params_d Term.bound)) ∧
      Td_tree_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 6) (ρ.bound 7) ∧
      Td_separated_d (ρ.bound 7) ∧ ∃ z, Td_letter_d false (ρ.bound 7) z := by
  simp only [td_static0_m,Formula.satisfies_conj_iff,td_tree_sat_l (kp_pair_l hKP) hKP.1,
    td_separated_sat_l hKP.1,Formula.satisfies_exists_iff,td_letter_sat_l hKP.1]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- 固定项：Ω,c₀,o,X₀,R₀,γ₀,D₀,C₀,Ar,Sr。
-- 头部：N,R,c,q,z,n,m,T,Q,G,E,Da,a,χ,C,γ,V,t,Λ。
structure Td_state_d (g : Fin 10 → M.Domain) (v : Fin 19 → M.Domain)
    (a : Fin 47 → M.Domain) : Prop where
  finite : M.mem (v 5) (g 0)
  successor : M.SuccessorOf (v 6) (v 5)
  tree : It_tree_d hZF (g 0) (g 1) (v 6) (v 7) (v 8) (v 9) (v 10)
  model : Smdl_d I (v 2) (v 0) (v 1)
  node : Rd_entry_d (v 5) (v 2) (v 8)
  root_node : Rd_entry_d (g 2) (g 1) (v 8)
  origin : It_map_d (v 9) (g 2) (v 5) (v 3)
  issued : Rr_truth_d I (v 0) (v 1) td_issued0_m a
  static : Rr_truth_d I (v 0) (v 1) td_static0_m (fun i => a (i.castAdd 28))
  numbers : Rr_layer_d I (g 0) (v 0) (v 1) (a 0) (v 4)
  slice : Tg_root_slice_d I (g 3) (g 4) (g 5) (g 6) (g 7)
    (v 0) (v 1) (v 14) (v 3) (v 15) (v 16) (v 17)
  below : ∀ x, Rd_entry_d x (v 15) (v 1) → Rd_entry_d x (a 24) (v 1)
  omega_low : Rd_entry_d (a 0) (v 16) (v 1)
  letters_low : Rd_entry_d (a 6) (v 16) (v 1)
  letters_root : Rd_entry_d (g 8) (a 6) (v 3)
  tree_root : Rd_entry_d (g 9) (a 7) (v 3)
  round : M.mem (v 12) (g 0)
  sequence : M.IsSequenceOfLength I (v 11) (v 12)
  index : Rd_entry_d (v 12) (a 19) (v 4)
  bound : Rd_entry_d (v 13) (a 24) (v 1)
  height : Rd_entry_d (v 13) (a 5) (v 1)
  archive : Td_archive_d I (g 0) (g 1) (g 3) (g 8) (g 9) (v 11)
    (v 0) (v 1) (v 13) (a 4) (a 1) (a 2) (v 4) (a 20) (g 6) (v 3)
  links : Td_archive_links_d (g 2) (v 8) (v 9) (v 10) (v 11)
  power : Pc_count_d I (g 0) (v 0) (v 1) (a 5)
  coding : Td_code_d I (v 0) (v 1) (a 7) (a 5)
  levels_function : M.IsSetFunction I (v 18)
  levels : ∀ i ρ, Rd_entry_d i ρ (v 18) ↔ ∃ p κ F, Rd_entry_d i p (v 10) ∧ It_payload_d p κ ρ F
  clear : Td_clear_d (v 11) (v 5) (v 7)
  critical : Tg_raw_critical_d I (g 3) (g 4) (g 5) (g 6) (g 7) (g 2) (v 8) (v 9) (v 10)
  owned : It_owned_d I (g 0) (v 8) (v 10)

/-- 同一内部响应只读当前状态和原根字母，不依赖未来输入。 -/
def Td_parent_d (J : kpair_convention_l.Interpretation M) (Ω : M.Domain)
    (v : Fin 19 → M.Domain) (k G : M.Domain) (row : Td_archive_row_d M.Domain) : Prop :=
  ∃ j, It_map_d G k (v 6) j ∧
    ((k = v 5 ∧ ∀ x, ¬ M.mem x row.depth) ∨
      ∃ l r, ∃ old : Td_archive_row_d M.Domain,
        M.mem l (v 12) ∧ Rd_entry_d l r (v 11) ∧ Rt_tuple_d old.values_d r ∧ old.i = k ∧
        M.SuccessorOf row.depth old.depth ∧
        (∀ p y, Rd_entry_d p y row.ancestors ↔
          Td_depth_next_d Ω old.depth old.ancestors old.enumeration j p y) ∧
        Td_aux_growth_d J row.X row.R j old.v row.v)

-- ω、原轮号、实数字母域、原策略、回答后历史、实数后历史、新历史、新请求、落子、输入像、旧历史像。
def td_digit0_m : Formula 1 11 := let v : Fin 11 → Term 11 := Term.bound
  set[11] ⟪⌜v 8⌝ₛ ∈ ⌜v 2⌝ₛ ∧
    (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ) → ⌜v 8⌝ₛ = ⌜v 9⌝ₛ) ∧
    (¬ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ) → ⌜rd_entry0_m⌝ₚ(⌜v 4⌝ₛ,⌜v 8⌝ₛ,⌜v 3⌝ₛ)) ∧
    ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 5⌝ₛ,⌜v 4⌝ₛ,⌜v 8⌝ₛ) ∧
    ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜v 7⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜v 5⌝ₛ,⌜v 7⌝ₛ,⌜v 3⌝ₛ) ∧
    (∃ b, ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 0⌝ₛ,⌜v 4⌝ₛ,⌜v 10⌝ₛ,b))⟫

theorem td_digit0_closed_l : td_digit0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_digit0_m,Definitional.Formula.FreeClosed]

theorem td_digit0_sat_l (hKP : M.Models KP) (ρ : Env M 11) :
    Formula.satisfies ρ td_digit0_m ↔
      M.mem (ρ.bound 8) (ρ.bound 2) ∧
      (Gm_even_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 1) → ρ.bound 8 = ρ.bound 9) ∧
      (¬ Gm_even_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 1) → Rd_entry_d (ρ.bound 4) (ρ.bound 8) (ρ.bound 3)) ∧
      Fseq_end_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4) (ρ.bound 8) ∧
      Fseq_end_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 6) (ρ.bound 5) (ρ.bound 7) ∧
      Rd_entry_d (ρ.bound 5) (ρ.bound 7) (ρ.bound 3) ∧
      ∃ b, Fseq_end_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 4) (ρ.bound 10) b := by
  simp only [td_digit0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_neg_iff,gm_even_sat_l (kp_pair_l hKP) hKP.1,
    Formula.satisfies_extensionalEq_iff_eq hKP.1,rd_entry0_sat_l hKP.1,Formula.satisfies_exists_iff,
    fseq_end_sat_l (kp_pair_l hKP) hKP.1,Definitional.Term.eval_weaken]
  rfl

/-- 两条实际原边、原策略的实数步、精确追加行及奇父深度一起保存。 -/
def td_digit_values_d {α : Type u} (u b : Fin 47 → α) (h t y z : α) : Fin 11 → α :=
  fun i => [u 0,u 19,u 6,u 17,h,t,b 20,b 21,y,z,u 20].get i

theorem td_digit_values_map_l {α : Type u} {β : Type v} (f : α → β) (u b : Fin 47 → α) (h t y z : α) :
    (fun i => f (td_digit_values_d u b h t y z i)) =
      td_digit_values_d (fun i => f (u i)) (fun i => f (b i)) (f h) (f t) (f y) (f z) :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun i => Fin.elim0 i))))))))))))

def td_copy_frame_d {α : Type u} (v : Fin 19 → α) : Fin 9 → α :=
  fun i => v ([5,6,7,8,9,10,0,1,13].get i)

theorem td_copy_frame_values_l {α : Type u} (v : Fin 19 → α) :
    td_copy_frame_d v = fun i => [v 5,v 6,v 7,v 8,v 9,v 10,v 0,v 1,v 13].get i :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))))

def Td_run_step_d (g : Fin 10 → M.Domain) (x : M.Domain) (v w : Fin 19 → M.Domain)
    (a b : Fin 47 → M.Domain) : Prop :=
  Ic_round_d hZF (g 0) (td_copy_frame_d v) (td_copy_frame_d w) ∧
  ∃ k T Q G E J,
    It_tree_d hZF (g 0) (g 1) (w 5) T Q G E ∧
    It_extension_d (v 6) (v 5) k (v 7) (v 8) (v 9) (v 10) (w 5) T Q G E ∧
    It_extension_d (w 5) (v 6) (v 5) T Q G E (w 6) (w 7) (w 8) (w 9) (w 10) ∧
    It_map_d (w 9) (v 5) (w 5) J ∧ M.SuccessorOf (w 12) (v 12) ∧
    (∃ u : Fin 47 → M.Domain, (∀ i, Rd_entry_d (a i) (u i) J) ∧
      (∀ i : Fin 19, b (i.castAdd 28) = u (i.castAdd 28)) ∧
      ∃ h t y z, Rd_entry_d x z (w 3) ∧
        Rr_truth_d I (w 0) (w 1) td_digit0_m
          (td_digit_values_d u b h t y z)) ∧
    ∃ row : Td_archive_row_d M.Domain, ∃ r,
      row.i = v 6 ∧ Rt_tuple_d row.values_d r ∧ Td_parent_d I (g 0) v k G row ∧
      (∀ i t, Rd_entry_d i t (w 11) ↔ Rd_entry_d i t (v 11) ∨ i = v 12 ∧ t = r)

end YesMetaZFC.SetTheory.LargeCardinal
