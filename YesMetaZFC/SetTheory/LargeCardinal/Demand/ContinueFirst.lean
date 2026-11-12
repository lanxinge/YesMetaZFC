import YesMetaZFC.SetTheory.LargeCardinal.Demand.NodeProgram
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ContinueNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Types.RawSubtype
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundRecovery
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ContinueInput
import YesMetaZFC.SetTheory.LargeCardinal.Demand.OldView
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveHistory
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Types.CandidateModel
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AuxGrowth

/-! # 双图节点名字列沿同一完整前驱图的运输

三个存在见证均从原查询码及列值回收。这里只搬运有界矩阵；
程序正确性仍由共同根负责，未将完整查询语义假设为绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem td_node_code_image_l {N R P S Γ t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (hP : (smdl_structure_l I (R := S) ny).Models KP)
    (Y : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet Y)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x Y.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (pred : ∀ x E, M.PairMember I x E t → ∀ y,
      M.PairMember I y E S ↔ ∃ a, M.PairMember I a x R ∧ M.PairMember I a y t)
    (ρ : Env (smdl_structure_l I (R := R) nx) 7)
    (η : Env (smdl_structure_l I (R := S) ny) 7)
    (points : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val t)
    (code : Td_node_code_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3)
      (ρ.bound 4) (ρ.bound 5) (ρ.bound 6)) :
    Td_node_code_d (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3)
      (η.bound 4) (η.bound 5) (η.bound 6) := by
  let A := smdl_structure_l I (R := R) nx
  let B := smdl_structure_l I (R := S) ny
  obtain ⟨C,a,b,pair,sa,kb,old,si,kj⟩ := code
  have hp : A.mem (ρ.bound 4) Y := ((carrier _).mp (ft.1.input_mem_of_pairMember (points 4))).2
  have hC := (pair.mem_l A trans hp).2
  have ha := (rd_entry_transitive_l trans hC si).2
  have hb := (rd_entry_transitive_l trans hC kj).2
  have image (x : A.Domain) (hx : A.mem x Y) : ∃ y : B.Domain, M.PairMember I x.val y.val t := by
    obtain ⟨y,hy,xy⟩ := ft.1.2.2 x.val ((carrier _).mpr ⟨x.property,hx⟩)
    exact ⟨⟨y,hy⟩,xy⟩
  obtain ⟨C',CC⟩ := image C hC
  obtain ⟨a',aa⟩ := image a ha
  obtain ⟨b',bb⟩ := image b hb
  let φ : Formula 1 10 := .conj (kpair0_m (.bound 7) (.bound 6) (.bound 2))
    (.conj (kpair0_m (.bound 1) (.bound 8) (.bound 8))
      (.conj (kpair0_m (.bound 0) (.bound 9) (.bound 9))
        (.conj (Formula.forallMem (.bound 3) (rd_entry0_m .newest .newest (.bound 3)))
          (.conj (rd_entry0_m (.bound 4) (.bound 1) (.bound 2))
            (rd_entry0_m (.bound 5) (.bound 0) (.bound 2))))))
  have matrix : Formula.satisfies (ρ.push C |>.push a |>.push b) φ := by
    simp only [φ,Formula.satisfies_conj_iff,kpair0_sat_l hN.1,
      Formula.satisfies_forallMem_iff,rd_entry0_sat_l hN.1]
    exact ⟨pair,sa,kb,old,si,kj⟩
  have moved := (rr_graph_delta_l I nx ny ⟨(ρ.bound 4).val,ft.1.input_mem_of_pairMember (points 4)⟩
    (fun x hx => ((carrier x).mp hx).1)
    (fun x y hx hy hxy => (carrier y).mpr ⟨hy,
      trans ⟨x,((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨y,hy⟩ hxy⟩)
    ft pred φ (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]) (.conj (kpair0_delta_l ..)
      (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
        (.conj (.forallMem _ (rd_entry0_delta_l ..)) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    (ρ.push C |>.push a |>.push b) (η.push C' |>.push a' |>.push b')
    (Fin.cases bb (Fin.cases aa (Fin.cases CC points)))).mp matrix
  simp only [φ,Formula.satisfies_conj_iff,kpair0_sat_l hP.1,
    Formula.satisfies_forallMem_iff,rd_entry0_sat_l hP.1] at moved
  exact ⟨C',a',b',moved⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 非重置第一施加的实际生产

四十七槽请求在完整档案中选中原轮，旧视图与当前 exceeds 构造二十九槽
继续输入。一步引理选出的 extender 经旧共同层逆图施加到旧奇模型。
原六十二槽沿父边搬运，同次 subtype、节点和 max 查询经完整代表池
进入新奇模型。数值程序沿共同根运输，名字列沿池图运输。

旧树携带两个辅助出现域不交的不变量。零、后继及元数对齐后，原 u 的
同一次实现恢复旧高度，两张旧图各精确追加一项。当前语言与 dcp 沿本次
共同层运输；旧实数字母域由临界点以下方块识别。以共同层端点作为历史界，
新待填字母由奇祖先深度调度选出，旧图追加仍用旧轮字母。实际组装完整
四十三槽输入并调用原更新定理，产出下一六十二槽回合。
档案保存旧奇模型的幂集计数和支撑上界；第一原边产生新奇模型的计数，
并将当前支撑相对原偶模型 δ 的界交给第二施加。原树的内部字母编码
沿同一奇父边保持，第二施加登记新行时直接消费该编码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

set_option maxRecDepth 2048 in
theorem Td_archive_d.demand_first_l
    {Ω c₀ X₀ R₀ wr zr cN N R qN z Da m D₀ γ₀ C₀ CN γN VN tN o Q G E : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (mn : Smdl_d I cN N R) (fromN : Smap_d I Ω c₀ cN X₀ N qN)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m) (ne : ι.bound 23 ≠ ι.bound 1)
    (numbers : Rr_layer_d I Ω N R (ι.bound 0).val z)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R CN qN γN VN tN)
    (omegaLow : Rd_entry_d (ι.bound 0).val VN R)
    (lettersLow : Rd_entry_d (ι.bound 6).val VN R)
    (lettersRoot : Rd_entry_d Ar (ι.bound 6).val qN)
    (sequence : M.IsSequenceOfLength I Da m) (index : Rd_entry_d m (ι.bound 19).val z)
    (χ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (hχ : (smdl_structure_l I (R := R) mn.2.1).mem χ (ι.bound 5))
    (archive : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ.val
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ qN)
    (treeLinks : Td_archive_links_d o Q G E Da)
    (powerCount : Pc_count_d I Ω N R (ι.bound 5).val) :
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let ground := (root.map_l hZF hΩ mn fromN).native_l I hZF hΩ
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ s : Td_archive_row_d M.Domain, ∃ saved : Td_archive_source_d I Ω c₀ X₀ Ar Sr D₀ s,
    (∃ r n, M.mem n m ∧ Rd_entry_d n r Da ∧ Rt_tuple_d s.values_d r) ∧
    Rd_entry_d s.i s.c Q ∧ It_map_d G o s.i s.p ∧
    let old : Env (smdl_structure_l I (R := s.R) saved.model.2.1) 62 :=
      ⟨fun i => ⟨s.v i,saved.round.1 i⟩,fun _ => ⟨s.v 0,saved.round.1 0⟩⟩
    ∃ l V Δ g, ∃ common : Ic_common_d I s.X s.R N R s.L l s.U V Δ g,
      (Rd_entry_d l χ.val R ∨ l = χ.val) ∧ Tg_root_square_d D₀ s.p qN g ∧
    ∃ τ w : Nn.Domain, ∃ θ : Env Nn 10,
      Formula.satisfies θ ee_language0_m ∧ θ.bound 0 = ι.bound 0 ∧
      θ.bound 1 = τ ∧ Ee_elastic_d ⟨θ.bound 6,θ.bound 7,θ.bound 8,θ.bound 9⟩ w ∧
      (∀ i : Fin 5, Rd_entry_d (old.bound ([19,9,0,2,4].get i)).val
        ([θ.bound 0,θ.bound 2,θ.bound 1,θ.bound 4,w].get i).val g) ∧
    ∃ ρ : Env Nn 29, Formula.satisfies ρ tc_seed0_m ∧
      (∀ i : Fin 10, ρ.bound ([0,1,3,4,5,6,17,18,19,20].get i) = θ.bound i) ∧
      ρ.bound 7 = w ∧ ρ.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ρ.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get i) =
        ι.bound ([0,5,24,28,25,37,38,39,40,41,42,43,44,45].get i)) ∧
      ρ.bound 28 = χ ∧
    ∃ s₀ pn pm : Nn.Domain,
      Td_node_query_d (kp_pair_l hN) (ρ.bound 0) (ι.bound 1) (ρ.bound 9) (ι.bound 27)
        (ρ.bound 11) (ρ.bound 12) s₀ (ι.bound 23) pn ∧
      Tg_max_query_d (kp_pair_l hN) (ρ.bound 0) (ι.bound 27) (ρ.bound 9)
        (ρ.bound 11) (ρ.bound 12) pm ∧ Nn.mem pn (ρ.bound 13) ∧ Nn.mem pm (ρ.bound 13) ∧
    let σ := Fin.cases (ρ.bound 21) (Fin.cases (ρ.bound 22) (Fin.cases (ρ.bound 23)
      (Fin.cases (ρ.bound 24) (Fin.cases (ρ.bound 25) (Fin.cases (ρ.bound 26) (fun _ : Fin 1 => ρ.bound 27))))))
    ∃ X K R' L F c d Y T j κ' U' D' u' : Nn.Domain,
      V_d (kp_pair_l hN) (ρ.bound 2) X ∧ Ep_source_d (kp_pair_l hN) (ρ.bound 0) (ρ.bound 1) K X R' ∧
      Nn.IsLimitOrdinal (ρ.bound 2) ∧ Nn.mem L (ρ.bound 2) ∧
      Nn.mem (ρ.bound 1) L ∧ Nn.mem (ρ.bound 8) L ∧ Rd_entry_d l L.val R ∧
      It_local_d (kp_pair_l hN) (ρ.bound 0) X R' (ρ.bound 1) L F ∧
      Sc_inaccessible_d (ρ.bound 0) X L ∧ Ex_strength_d (kp_pair_l hN) (ρ.bound 0) (ρ.bound 1) L X F ∧
      Smem_d (kp_pair_l hN) c X R' ∧ Smem_d (kp_pair_l hN) d Y T ∧
      It_ultra_d (kp_pair_l hN) (ρ.bound 0) (ρ.bound 1) L F c d j ∧
      Wd_crit_d (kp_pair_l hN) X j (ρ.bound 1) κ' ∧ Nn.MemberSubset L κ' ∧ Nn.IsLimitOrdinal κ' ∧
      Rd_entry_d (ρ.bound 5) U' j ∧ Rd_entry_d (ρ.bound 6) D' j ∧ Rd_entry_d (ρ.bound 7) u' j ∧
      Tt_pool_d (kp_pair_l hN) (ρ.bound 0) (ρ.bound 3) U' D' ∧
      Ts_subtype_d (ρ.bound 0) (ρ.bound 3) κ' (ρ.bound 8) (ρ.bound 9) U'
        (ρ.bound 13) (ρ.bound 14) σ (ρ.bound 16) u' ∧
    ∃ α β : Nn.Domain, ∃ B v,
      Nn.mem α ⟨l,common.right_rank.1⟩ ∧ Nn.IsLimitOrdinal α ∧ V_d (kp_pair_l hN) α β ∧
      Nn.mem (ρ.bound 1) β ∧
      (∀ x, M.mem x B ↔ M.mem x N ∧ Rd_entry_d x V R) ∧ M.IsSetInjectionFromTo I v B s.X ∧
      (∀ x y, Rd_entry_d x y v ↔ Rd_entry_d y x g) ∧
    ∃ Ls Js Os Zs Ds ps Vs Ws qs cP P S jP qP pP,
      Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ s.c s.X s.R s.p B v N R z cN mn.2.1 hN
        ⟨V,common.right_rank.2.1⟩ (ρ.bound 0) (ρ.bound 1) L F β X K j
        Ls Js Os Zs Ds ps Vs Ws qs cP P S jP qP pP ∧
    ∃ mp : Smdl_d I cP P S,
    ∃ Ul : Nn.Domain, ∃ lp Vp Δp gp,
      Ic_common_d I N R P S L.val lp Ul.val Vp Δp gp ∧
    ∃ CP γP VP tP,
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S CP qP γP VP tP ∧
      Rd_entry_d γN γP gp ∧ Rd_entry_d VN VP gp ∧ It_comp_d tN gp tP ∧
      Tg_root_square_d D₀ qN qP gp ∧
    ∃ Ac Qc Yc ec : Nn.Domain, ∃ Dc Γc t,
      Eb_collapse_d (ρ.bound 0) (ρ.bound 1) L K X β F Ac Qc Yc ec ∧
      (∀ x, M.mem x Dc ↔ M.mem x N ∧ Rd_entry_d x Ac.val R) ∧
      (∀ x, M.mem x Γc ↔ M.mem x N ∧ Rd_entry_d x Yc.val R) ∧
      M.IsSetInjectionFromTo I t Γc P ∧ M.IsRestrictionOf I gp t Δp ∧
      Rd_entry_d L.val lp t ∧ Rd_entry_d Ul.val Vp t ∧
      Er_present_d I Ω Ls N R z B s.X v qs ec.val Dc t ∧
      (∀ x E, Rd_entry_d x E t → ∀ y,
        Rd_entry_d y E S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t) ∧
      (∀ x y : Nn.Domain, ∀ a E, Nn.mem x β → Rd_entry_d x y j →
        Rd_entry_d x.val a v → (Rd_entry_d y.val E t ↔ Rd_entry_d a E jP)) ∧
    ∃ η : Env (smdl_structure_l I (R := S) mp.2.1) 17,
      (∀ i, Rd_entry_d
        ([ρ.bound 0,ρ.bound 3,κ',ρ.bound 8,ρ.bound 9,U',ρ.bound 13,ρ.bound 14,ρ.bound 16,u',
          ρ.bound 21,ρ.bound 22,ρ.bound 23,ρ.bound 24,ρ.bound 25,ρ.bound 26,ρ.bound 27].get i).val
        (η.bound i).val t) ∧ Formula.satisfies η tg_subtype0_m ∧
    ∃ ζ : Env (smdl_structure_l I (R := S) mp.2.1) 62,
      (∀ i, Rd_entry_d (old.bound i).val (ζ.bound i).val jP) ∧
      Formula.satisfies ζ td_round0_m ∧
      (∀ i : Fin 5, η.bound ([0,1,2,5,9].get i) = ζ.bound ([19,9,0,2,4].get i)) ∧
      Formula.satisfies (η.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i))
        ts_numeric0_m ∧
    let Pn := smdl_structure_l I (R := S) mp.2.1
    ∃ nativeP : Pn.Models ZF, ∃ Bc Vc Dc : Pn.Domain,
      V_d (kp_pair_l (ZF.modelsKP nativeP)) (η.bound 3) Bc ∧
      (∀ x, Pn.mem x Vc ↔ Pn.mem x Bc ∨ x = η.bound 3) ∧
      Tt_pool_d (kp_pair_l (ZF.modelsKP nativeP)) (η.bound 0) (η.bound 4) Vc Dc ∧
      Ts_real_d nativeP (η.bound 0) (ζ.bound 21) (η.bound 1) (ζ.bound 10)
        (η.bound 4) Vc Dc (η.bound 6) (ζ.bound 5) ∧
    ∃ pn' pm' : Pn.Domain,
      Rd_entry_d pn.val pn'.val t ∧ Rd_entry_d pm.val pm'.val t ∧
      Pn.mem pn' (η.bound 6) ∧ Pn.mem pm' (η.bound 6) ∧
    ∃ e' l' s' k' pc' qc' : Pn.Domain,
      (∀ i : Fin 4, Rd_entry_d ([ι.bound 1,ι.bound 27,s₀,ι.bound 23].get i).val
        ([e',l',s',k'].get i).val t) ∧
      Td_node_query_d (kp_pair_l (ZF.modelsKP nativeP)) (η.bound 0) e' (η.bound 4) l' Vc Dc s' k' pc' ∧
      Pn.mem pc' (η.bound 6) ∧
      Tg_max_query_d (kp_pair_l (ZF.modelsKP nativeP)) (η.bound 0) l' (η.bound 4) Vc Dc qc' ∧
      Pn.mem qc' (η.bound 6) ∧
    ∃ ν₁ X₁ c₁ R₁ r₁ a₁ b₁ z₁ π₁ : Pn.Domain,
      (Pn.mem ν₁ (ζ.bound 5) ∧ V_d (kp_pair_l (ZF.modelsKP nativeP)) ν₁ X₁ ∧
      Smem_d (kp_pair_l (ZF.modelsKP nativeP)) c₁ X₁ R₁ ∧
      Tt_realized_d (kp_pair_l (ZF.modelsKP nativeP)) (ζ.bound 19) c₁ X₁ R₁ (η.bound 4) r₁
        (ζ.bound 21) Vc Dc (η.bound 6) ∧
      Pn.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP nativeP)) π₁ (η.bound 4) (η.bound 4) ∧
      (∀ i v x, Rd_entry_d v i π₁ → Pn.mem i (ζ.bound 9) →
        (Rd_entry_d i x (ζ.bound 10) ↔ Rd_entry_d v x r₁)) ∧
      Pn.SuccessorOf ν₁ (ζ.bound 23) ∧ Rd_entry_d (ζ.bound 20) (ζ.bound 22) r₁ ∧
      Rd_entry_d (ζ.bound 9) (ζ.bound 23) r₁ ∧
      Td_labels_d (kp_pair_l (ZF.modelsKP nativeP)) (ζ.bound 20) (ζ.bound 9) r₁ a₁ b₁ ∧
      Tg_node_d (kp_pair_l (ZF.modelsKP nativeP)) k' (ζ.bound 22) s' a₁ b₁ ∧
      Td_groups_d (kp_pair_l (ZF.modelsKP nativeP)) (ζ.bound 19) (ζ.bound 20) (ζ.bound 9) r₁ a₁ b₁ ∧
      Pn.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP nativeP)) a₁ k' (ζ.bound 47) ∧
      Pn.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP nativeP)) b₁ k' (ζ.bound 48) ∧
      Pn.MemberSubset (ζ.bound 45) a₁ ∧ Pn.MemberSubset (ζ.bound 46) b₁ ∧
      Rd_entry_d (ζ.bound 25) (ζ.bound 49) a₁ ∧
      (∀ x, Pn.mem x a₁ ↔ Pn.mem x (ζ.bound 45) ∨ KPair_d Pn x (ζ.bound 25) (ζ.bound 49)) ∧
      Pn.mem z₁ (ζ.bound 48) ∧ Rd_entry_d (ζ.bound 25) z₁ b₁ ∧
      (∀ x, Pn.mem x b₁ ↔ Pn.mem x (ζ.bound 46) ∨ KPair_d Pn x (ζ.bound 25) z₁)) ∧
    ∃ dep tab, M.SuccessorOf dep s.depth ∧
      Td_depth_d I Ω P S (ζ.bound 47).val dep tab ∧
      (∀ p y, Rd_entry_d p y tab ↔
        Td_depth_next_d Ω s.depth s.ancestors s.enumeration jP p y) ∧
    ∃ ξ : Env Pn 43, Formula.satisfies ξ td_seed0_m ∧
      Td_pick_d I Ω dep tab (ξ.bound 30).val ∧
      (∀ i : Fin 8, ξ.bound ([0,1,2,3,4,28,29,31].get i) =
        ζ.bound ([19,20,21,22,23,47,48,50].get i)) ∧
      ξ.bound 5 = η.bound 3 ∧ ξ.bound 6 = k' ∧ ξ.bound 8 = η.bound 1 ∧
      ξ.bound 9 = η.bound 4 ∧ ξ.bound 14 = r₁ ∧ ξ.bound 19 = η.bound 6 ∧
      ξ.bound 25 = s' ∧ ξ.bound 26 = a₁ ∧ ξ.bound 27 = b₁ ∧
    ∃ ε : Env Pn 62,
      (∀ i : Fin 43, ε.bound ⟨19+i.val,by omega⟩ = ξ.bound i) ∧
      Formula.satisfies ε td_round0_m ∧
      (ε.bound 43).val = lp ∧
      (∀ i : Fin 17, Rd_entry_d
        (ι.bound ([0,23,24,27,28,25,31,32,37,38,39,40,41,42,43,44,45].get i)).val
        (ε.bound ([19,25,24,27,28,38,35,36,40,42,55,56,57,58,59,60,61].get i)).val gp) ∧
      Td_depth_d I Ω P S (ε.bound 47).val dep tab ∧ Td_pick_d I Ω dep tab (ε.bound 49).val ∧
      (∀ x, Rd_entry_d x γP S → Rd_entry_d x (ξ.bound 5).val S) ∧
      (∀ a x, M.mem a D₀ → Rd_entry_d a x qP → Rd_entry_d x (ε.bound 1).val S) ∧
      Rd_entry_d Ar (ε.bound 50).val qP ∧ Rd_entry_d Sr (ε.bound 22).val qP ∧
      Rd_entry_d (ε.bound 19).val VP S ∧ Rd_entry_d (ε.bound 50).val VP S ∧
      (∀ i : Fin 2, Rd_entry_d (ι.bound ([1,6].get i)).val
        (ε.bound ([20,50].get i)).val gp) ∧
      Pc_count_d I Ω P S (ε.bound 21).val ∧ Rd_entry_d L.val (ι.bound 5).val R ∧
      Td_code_d I P S (ε.bound 22).val (ε.bound 21).val ∧
      Td_aux_growth_d I P S jP s.v (fun i => (ε.bound i).val) ∧
      Td_play_at_d I N R (ι.bound 4).val (ι.bound 2).val (ι.bound 20).val s₀.val ∧
      Rd_entry_d s₀.val (ε.bound 44).val gp ∧
      (∀ x, Rd_entry_d x γN R → Rd_entry_d x (ρ.bound 1).val R) := by
  intro Nn ground hN
  have native := ZFC.models_zf_l ground
  obtain ⟨n,r,hn,selected,hr,entry⟩ :=
    archive.select_l hZF mn native ι issued ne numbers sequence index
  have stored := entry
  obtain ⟨s,code,_⟩ := stored
  obtain ⟨saved,l,V,Δ,g,common,upper,roots,view⟩ := entry.read_l I code
  obtain ⟨parentNode,parentRoot,_⟩ := treeLinks n r s hr code
  refine ⟨s,saved,⟨r,n,hn,hr,code⟩,parentNode,parentRoot,?_⟩
  intro old
  let cA := s.c
  let A := s.X
  let RA := s.R
  let qA := s.p
  let L₀ := s.L
  let U := s.U
  let ma := saved.model
  refine ⟨l,V,Δ,g,common,upper,roots,?_⟩
  have fromA : Smap_d I Ω c₀ cA X₀ A qA := saved.origin
  have oldRound : Formula.satisfies old td_round0_m :=
    (rr_truth_native_l I ma.2.1 td_round0_m td_round0_closed_l old.bound).mp saved.round
  have oldNumbers : Rr_layer_d I Ω A RA (old.bound 19).val s.z := saved.numbers
  have cofinal : Tg_raw_cofinal_d I (old.bound 19).val A RA L₀ := saved.cofinal
  have small : Rr_small_d I A RA U := saved.small
  have below : Rd_entry_d (old.bound 0).val L₀ RA := saved.below
  have control := (td_issued_sat_l (kp_pair_l hN) hN.1 ι).mp issued |>.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have geometry := control.2.2.2.2.2.2.2.2.2
  simp only [td_geometry_m,Formula.satisfies_conj_iff] at geometry
  have woodin := (woodin_sat_l (kp_pair_l hN) native.1 ..).mp geometry.1
  obtain ⟨_,_,_,_,regular,_⟩ := woodin
  have ordχ := regular.isLimitOrdinal.1.mem hχ
  have historyBound x (hx : Rd_entry_d x l R) : Rd_entry_d x χ.val R := upper.elim
    (fun hl => ordχ.transitive ⟨l,common.right_rank.1⟩ hl ⟨x,(mn.2.2.2 x l hx).1⟩ hx)
    (fun eq => eq ▸ hx)
  obtain ⟨j₀,τ,w,past,trace⟩ := view.read_l I mn hN
    (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 22) (ι.bound 20) numbers.injection.1.1 selected
  obtain ⟨a,ℓ,κ₀,u₀,b,request,move,answer,pair⟩ := past
  have source := ZFC.models_zf_l ((root.map_l hZF hΩ ma fromA).native_l I hZF hΩ)
  obtain ⟨θ,w',j',d₀,q₀,n₀,language,hw,elastic,arity,view⟩ :=
    common.demand_view_l hZF hΩ root.model ma mn source ground fromA fromN root.ext
      rootNumbers old oldRound oldNumbers numbers below
  have ew : w' = w := Subtype.ext (common.injection.1.1.2 _ _ _ (view 10) (trace 2))
  have ej : j' = j₀ := Subtype.ext (common.injection.1.1.2 _ _ _ (view 11) (trace 0))
  subst w' j'
  have eτ : θ.bound 1 = τ := Subtype.ext (common.injection.1.1.2 _ _ _ (view 1) (trace 1))
  have sameω : θ.bound 0 = ι.bound 0 := Subtype.ext hw
  have oldLinks : ∀ i : Fin 5, Rd_entry_d (old.bound ([19,9,0,2,4].get i)).val
      ([θ.bound 0,θ.bound 2,θ.bound 1,θ.bound 4,w].get i).val g :=
    Fin.cases (view 0) (Fin.cases (view 2) (Fin.cases (view 1)
      (Fin.cases (view 4) (Fin.cases (view 10) (fun i => Fin.elim0 i)))))
  refine ⟨τ,w,θ,language,sameω,eτ,elastic,oldLinks,?_⟩
  have pair : KPair_d Nn b (θ.bound 1) w := eτ.symm ▸ pair
  -- 依次读取继续请求、节点查询及其规范实现，保留同一输入的全部对应。
  obtain ⟨ρ,seed,oldCoords,typeEq,arityEq,newCoords,boundEq,next,_,input⟩ :=
    td_continue_input_l native ι issued ne θ language sameω w χ elastic request move answer pair arity hχ
  obtain ⟨s₀,pn,pm,nodeQuery,maxQuery,nodeMember,maxMember,input⟩ := input
  obtain ⟨is,ik,zn,pc,heq,hqn,his,hik,nodeProgram,nodeCode,canonicalMember,input⟩ := input
  obtain ⟨zm,qm,maxProgram,maxCode,canonicalMax,ψ,candidate,candidateLinks,candidateU,candidateE,shortMem,shortPlay⟩ := input
  refine ⟨ρ,seed,oldCoords,typeEq,arityEq,newCoords,boundEq,
    s₀,pn,pm,nodeQuery,maxQuery,nodeMember,maxMember,?_⟩
  intro σ
  have numbers : Rr_layer_d I Ω N R (ρ.bound 0).val z :=
    (congrArg Subtype.val (newCoords 0)).symm ▸ numbers
  have values : ∀ i : Fin 5, ρ.bound ([0,3,1,5,7].get i) =
      [θ.bound 0,θ.bound 2,θ.bound 1,θ.bound 4,w].get i :=
    Fin.cases (oldCoords 0) (Fin.cases (oldCoords 2) (Fin.cases (oldCoords 1)
      (Fin.cases (oldCoords 4) (Fin.cases typeEq (fun i => Fin.elim0 i)))))
  have links (i : Fin 5) : Rd_entry_d (old.bound ([19,9,0,2,4].get i)).val
      (ρ.bound ([0,3,1,5,7].get i)).val g :=
    (congrArg Subtype.val (values i)).symm ▸ oldLinks i
  have historyBound (x) (hx : Rd_entry_d x l R) : Rd_entry_d x (ρ.bound 28).val R :=
    (congrArg Subtype.val boundEq).symm ▸ historyBound x hx
  have actual := seed
  simp only [tc_seed0_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    ts_program_sat_l native,ee_language_sat_l ground,Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff,v_sigma_sat_l hN,tt_constants0_sat_l native.1,
    ee_elastic_sat_l,tx_exceeds_sat_l native,tt_eval_cases_l] at actual
  obtain ⟨omega,program,language,limit,hτδ,rank,constants,elastic,exceeds,hχ⟩ := actual
  have one := ee_one_step_l ground omega program language limit hτδ rank constants elastic exceeds
  have previous := exceeds
  obtain ⟨_,_,η,Z,c₁,R₁,r,hZ,model,type,_,_,_,_,witness⟩ := previous
  obtain ⟨_,regular,_⟩ := sc_v_inaccessible_read_l native hZ
    ((language.inaccessible c₁ Z R₁ r (ρ.bound 2) (ρ.bound 7) model type).mp elastic.2.1)
  obtain ⟨_,_,_,_,_,_,_,_,_,realized,_⟩ := witness
  obtain ⟨X,K,R',L,F,c,d,Y,T,j,κ',U',D',u',image⟩ :=
    one.image_l native omega regular.isLimitOrdinal program language hZ model type limit realized.finite hχ
  obtain ⟨rankX,source,hL,hκ,hτ,high,loc,card,strong,mx,my,ultra,critical,bound,limitκ,iU,iD,iu,pool,subtype⟩ := image
  have rankV := (rr_rank_native_l I mn.2.1 hN ⟨l,common.right_rank.1⟩
    ⟨V,common.right_rank.2.1⟩).mp common.right_rank
  have above : Rd_entry_d l L.val R :=
    ordinal_down_l hN (v_ordinal_l (kp_pair_l hN) rankV)
      (loc.ordinals_l hN source.transitive source.code).2 (fun x hx => historyBound x.val hx) high
  have groundA := ZFC.models_zf_l ((root.map_l hZF hΩ ma fromA).native_l I hZF hΩ)
  have omegaA := (td_round_native_l (ZF.modelsKP groundA) old oldRound).1
  have cf := cofinal.native_l I hZF.1 ma.2.1 (kp_pair_l (ZF.modelsKP groundA)) groundA.1
    (old.bound 19) ⟨L₀,common.left_rank.1⟩
  obtain ⟨α,β,hα,hβV,hκβ,limitα,rankβ,B,v,carrier,fv,reverseImage,_,inverse,cut⟩ :=
    common.return_cut_l hZFC hΩ root ma mn fromA ground (old.bound 19) (old.bound 0) omegaA cf small below
      source rankX regular.isLimitOrdinal loc card strong mx my ultra critical.image bound numbers (links 2) above
  -- 原输入的极限秩界同时覆盖旧类型及其完整名字域。
  have hUβ := tt_constants_rank_l native rankβ limitα
    (ZF.v_ordinal_height_l native rankβ language.limit.1 hκβ) language.rank language.constants
  have hwβ := v_subset_mem_l (kp_pair_l hN) rankβ hκβ (omega.subset_limitOrdinal hN language.limit)
  have hDβ := type.pool.rank_mem_l hN omega rankβ limitα hwβ type.finite hUβ
  have huβ := v_subset_mem_l (kp_pair_l hN) rankβ hDβ (fun x hx => ((type.truth x).mp hx).1)
  obtain ⟨An,names⟩ := tn_names_exists_l native (ρ.bound 3) (ρ.bound 5)
  have hAn := names.rank_mem_l hN omega rankβ limitα hwβ type.finite hUβ
  let ε : Env Nn 17 := ⟨fun i =>
    [ρ.bound 0,ρ.bound 3,κ',ρ.bound 8,ρ.bound 9,U',ρ.bound 13,ρ.bound 14,ρ.bound 16,u',
      ρ.bound 21,ρ.bound 22,ρ.bound 23,ρ.bound 24,ρ.bound 25,ρ.bound 26,ρ.bound 27].get i,ρ.free⟩
  let slots : Fin 7 → Term 17 := Fin.cases (.bound 10) (Fin.cases (.bound 11) (Fin.cases (.bound 12)
    (Fin.cases (.bound 13) (Fin.cases (.bound 14) (Fin.cases (.bound 15) (fun _ => .bound 16))))))
  have values : (fun i => (slots i).eval ε) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) i
  have truth : Formula.satisfies ε tg_subtype0_m := by
    apply (ts_subtype_sat_l hN ε (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) slots).mpr
    rw [values]
    exact subtype
  have finite i : Nn.mem (σ i) (ρ.bound 0) :=
    omega.transitive hN (ρ.bound 14) program.length _ (program.slots i)
  have codes : ∀ i : Fin 9, Nn.mem (ε.bound ([7,8,10,11,12,13,14,15,16].get i)) (ρ.bound 0) :=
    Fin.cases program.length (Fin.cases program.natural (Fin.cases (finite 0) (Fin.cases (finite 1)
      (Fin.cases (finite 2) (Fin.cases (finite 3) (Fin.cases (finite 4)
        (Fin.cases (finite 5) (Fin.cases (finite 6) (fun i => Fin.elim0 i)))))))))
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,cP,P,S,jP,qP,pP,cert⟩ := cut
  obtain ⟨ωA,_,hωA,aboveA,regularA,strongA,_⟩ := td_round_woodin_l (ZF.modelsKP groundA) old oldRound
  have rankA := (rr_rank_native_l I ma.2.1 (ZF.modelsKP groundA)
    ⟨L₀,common.left_rank.1⟩ ⟨U,common.left_rank.2.1⟩).mp common.left_rank
  have ownerLocal := it_local_short_l I mn.2.1 (kp_pair_l hN) native.1
    (loc.rank_absolute_l hN source.omega rankX regular.isLimitOrdinal source.code)
  have countρ : Pc_count_d I Ω N R (ρ.bound 2).val :=
    (congrArg Subtype.val (newCoords 1)).symm ▸ powerCount
  have nextCount := cert.power_l hZFC hΩ root ma fromA mn.2.1 native
    ⟨V,common.right_rank.2.1⟩ (ρ.bound 0) (ρ.bound 1) L F β X K j (ρ.bound 2)
      numbers ownerLocal regular.isCardinal.1 hL countρ
      ωA (old.bound 21) ⟨L₀,common.left_rank.1⟩ ⟨U,common.left_rank.2.1⟩
        hωA aboveA regularA strongA rankA
          (regularA.isCardinal.1.transitive _ saved.support_below) reverseImage saved.power_count
  -- 本次施加先确定共同层，再读取临界像和完整代表池；后续回答仍使用这个池。
  obtain ⟨hwβ',iω,inatural,mp,Ul,lp,Vp,Δp,gp,commonP,reply⟩ :=
    cert.subtype_native_l hZF hΩ root mn.2.1 hN native source mx my ultra ε rfl
      type.finite hUβ huβ hAn names iU iu codes truth
  obtain ⟨Klow,bκ,κcap,rankLow,lowSquare,iκv,iκj,capP,reply⟩ := reply
  obtain ⟨Ac,Qc,Yc,ec,Dc,Γc,t,owned,domain,carrier',ft,restrictP,endpointP,layerP,present,pred,commute,η,points,valid⟩ := reply
  have facts := cert
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,embed,rootMap,_,_,_,_,certificate,
    rootGraph,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := facts
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨w₀,w₁,z₀,z₁,ww₀,_,omegaEdge,_,newNumbers,oldGraph,_,numeric,_⟩ := rest
  obtain ⟨a,images⟩ := Classical.axiomOfChoice (fun i : Fin 62 =>
    embed.1.1.2.2 (old.bound i).val (old.bound i).property)
  let ζ : Env (smdl_structure_l I (R := S) mp.2.1) 62 :=
    ⟨fun i => ⟨a i,(images i).1⟩,fun _ => ⟨a 0,(images 0).1⟩⟩
  have transferred : Formula.satisfies ζ td_round0_m :=
    (smap_source_l I hZF hΩ ma mp embed td_round0_m td_round0_closed_l
      old ζ (fun i => (images i).2)).mp oldRound
  -- 旧轮沿父边的像与 subtype 沿池图的像由同一常值方块识别。
  have back i : Rd_entry_d (ρ.bound ([0,3,1,5,7].get i)).val
      (old.bound ([19,9,0,2,4].get i)).val v := (inverse _ _).mpr (links i)
  have carry (x : Nn.Domain) (i : Fin 17) (a : M.Domain) (hx : Nn.mem x β)
      (hi : Rd_entry_d x (ε.bound i) j) (ha : Rd_entry_d x.val a v) :
      Rd_entry_d a (η.bound i).val jP := (commute x (ε.bound i) a (η.bound i).val hx hi ha).mp (points i)
  have same : ∀ i : Fin 5, Rd_entry_d (old.bound ([19,9,0,2,4].get i)).val
      (η.bound ([0,1,2,5,9].get i)).val jP :=
    Fin.cases (carry (ρ.bound 0) 0 _ hwβ' iω (back 0))
      (Fin.cases (carry (ρ.bound 3) 1 _
        ((v_transitive_l (kp_pair_l hN) rankβ) _ hwβ' _ type.finite) inatural (back 1))
        (Fin.cases (carry (ρ.bound 1) 2 _ hκβ critical.image (back 2))
          (Fin.cases (carry (ρ.bound 5) 5 _ hUβ iU (back 3))
            (Fin.cases (carry (ρ.bound 7) 9 _ huβ iu (back 4)) (fun i => Fin.elim0 i)))))
  -- 程序的全公式经共同根传输，不能只凭十个参数属于自然数。
  let ix : Fin 11 → Fin 17 := fun i => [0,1,7,8,10,11,12,13,14,15,16].get i
  let π : Env Nn 11 := ρ.reindex (fun i => [0,3,14,16,21,22,23,24,25,26,27].get i)
  have coordinates : ∀ i, π.bound i = ε.bound (ix i) :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun i => Fin.elim0 i)))))))))))
  have compiled : Formula.satisfies π ts_numeric0_m := by
    apply (ts_numeric0_sat_l native π).mpr
    refine ⟨ρ.bound 15,?_⟩
    have eq : (fun i : Fin 7 => [ρ.bound 21,ρ.bound 22,ρ.bound 23,ρ.bound 24,
        ρ.bound 25,ρ.bound 26,ρ.bound 27].get i) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) i
    change Ts_program_d native (ρ.bound 0) (ρ.bound 3) (ρ.bound 14)
      (fun i => [ρ.bound 21,ρ.bound 22,ρ.bound 23,ρ.bound 24,ρ.bound 25,ρ.bound 26,ρ.bound 27].get i)
      (ρ.bound 15) (ρ.bound 16)
    rw [eq]
    exact program
  have low : ∀ i, ε.bound (ix i) = ρ.bound 0 ∨ Nn.mem (ε.bound (ix i)) (ρ.bound 0) :=
    Fin.cases (Or.inl rfl) (Fin.cases (Or.inr type.finite)
      (Fin.cases (Or.inr (codes 0)) (Fin.cases (Or.inr (codes 1))
        (Fin.cases (Or.inr (codes 2)) (Fin.cases (Or.inr (codes 3))
          (Fin.cases (Or.inr (codes 4)) (Fin.cases (Or.inr (codes 5))
            (Fin.cases (Or.inr (codes 6)) (Fin.cases (Or.inr (codes 7))
              (Fin.cases (Or.inr (codes 8)) (fun i => Fin.elim0 i)))))))))))
  have ew₀ : w₀ = (old.bound 19).val := fv.1.1.2 _ _ _ ww₀ (back 0)
  have ew₁ : (η.bound 0).val = w₁ := embed.1.1.1.2 _ _ _ (same 0) (ew₀ ▸ omegaEdge)
  have hj := ultra.elementary_l native mx.1 my.1
  have natural := hj.natural_l native source.omega source.transitive (ultra.transitive_l native my.1)
    mx my source.omega_mem
  -- 原池图在所有自然数上使用同一数字坐标，而不只核对 subtype 的七槽。
  have digits (x : Nn.Domain) (y : (smdl_structure_l I (R := S) mp.2.1).Domain)
      (hx : Nn.mem x (ρ.bound 0)) (xy : Rd_entry_d x.val y.val t) :
      ∃ a, Rd_entry_d a x.val z ∧ Rd_entry_d a y.val z₁ := by
    obtain ⟨a,_,ha⟩ := (numbers.image x.val).mp hx
    have hxβ := (v_transitive_l (kp_pair_l hN) rankβ) _ hwβ' x hx
    obtain ⟨b,_,hb⟩ := fv.1.2.2 x.val
      ((carrier _).mpr ⟨x.property,(v_transitive_l (kp_pair_l hN) rankV) _ hβV x hxβ⟩)
    exact ⟨a,ha,(numeric a b ((oldGraph a b).mpr ⟨_,ha,hb⟩) _).mpr
      ((commute x x b y.val hxβ (natural x hx) hb).mp xy)⟩
  have values i : ((π.bound i).val = (ρ.bound 0).val ∧ (η.bound (ix i)).val = w₁) ∨
      ∃ a, Rd_entry_d a (π.bound i).val z ∧ Rd_entry_d a (η.bound (ix i)).val z₁ := by
    rcases low i with eq | hi
    · exact Or.inl ⟨congrArg Subtype.val ((coordinates i).trans eq),
        (ft.1.1.2 _ _ _ (congrArg Subtype.val eq ▸ points (ix i)) (points 0)).trans ew₁⟩
    · obtain ⟨a,ha,hb⟩ := digits (ε.bound (ix i)) (η.bound (ix i)) hi (points (ix i))
      exact Or.inr ⟨a,(congrArg Subtype.val (coordinates i)).symm ▸ ha,hb⟩
  have program' := (smap_numeric_model_peer_l hZF hΩ root.model mn mp fromN rootMap root.ext
    (fromN.extensional_l hZF hΩ root.model mn root.ext) (certificate root).ext
    rootNumbers numbers newNumbers ts_numeric0_m ts_numeric0_closed_l π (η.reindex ix) values).mp compiled
  have coupled (i : Fin 5) : η.bound ([0,1,2,5,9].get i) = ζ.bound ([19,9,0,2,4].get i) :=
    Subtype.ext (embed.1.1.1.2 _ _ _ (same i) (images _).2)
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have nativeP : Pn.Models ZF := ZFC.models_zf_l ((certificate root).native_l I hZF hΩ)
  have hP := ZF.modelsKP nativeP
  -- 当前完整候选沿本次共同层进入 P，与原代表池上的 u、κ、n 逐字相同。
  have rankUl := (rr_rank_native_l I mn.2.1 hN
    ⟨L.val,commonP.left_rank.1⟩ Ul).mp commonP.left_rank
  have limitL : Nn.IsLimitOrdinal L := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => L)).mp commonP.limit)
  have hkUl := KP.v_ordinal_subset_l hN rankUl (ρ.bound 8) hτ
  have hUUl := tt_constants_rank_l native rankUl limitL hτ rank constants
  have hwUl := v_subset_mem_l (kp_pair_l hN) rankUl hkUl (omega.subset_limitOrdinal hN limit)
  have hDUl := realized.pool.rank_mem_l hN omega rankUl limitL hwUl realized.finite hUUl
  have huUl := v_subset_mem_l (kp_pair_l hN) rankUl hDUl (fun x hx => ((realized.truth x).mp hx).1)
  obtain ⟨ψp,candidatePoints,_,candidateP⟩ := commonP.candidate_model_l hZF hΩ root.model mn mp
    native ((certificate root).native_l I hZF hΩ) fromN rootMap root.ext rootNumbers numbers newNumbers
    ψ (congrArg Subtype.val (candidateLinks 2))
    ((congrArg Subtype.val (candidateLinks 3)).symm ▸ hkUl)
    ((congrArg Subtype.val (candidateLinks 0)).symm ▸ huUl)
    ((congrArg Subtype.val (candidateLinks 1)).symm ▸ realized.finite) candidate
  have candidateImages i := ((restrictP.2 _ _).mp (candidatePoints i)).2
  have candidateSame (i : Fin 5) : ψp.bound ([0,1,2,3,4].get i) =
      η.bound ([6,4,0,3,1].get i) := by
    apply Subtype.ext
    apply ft.1.1.2 _ _ _ ((congrArg Subtype.val (candidateLinks i)) ▸ candidateImages _)
    exact Fin.cases (points 6) (Fin.cases (points 4) (Fin.cases (points 0)
      (Fin.cases (points 3) (Fin.cases (points 1) (fun j => Fin.elim0 j))))) i
  have poolData := owned
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,collapse,_⟩ := poolData
  let a₁ : Env Nn 1 := ⟨fun _ => ρ.bound 8,ρ.free⟩
  let b₁ : Env Pn 1 := ⟨fun _ => η.bound 3,η.free⟩
  have transfer := rr_graph_delta_l I mn.2.1 mp.2.1
    ⟨(ρ.bound 8).val,ft.1.input_mem_of_pairMember (points 3)⟩
    (fun x hx => ((carrier' x).mp hx).1)
    (fun x y hx hy hyx => (carrier' y).mpr ⟨hy,collapse.transitive
      ⟨x,((carrier' x).mp hx).1⟩ ((carrier' x).mp hx).2 ⟨y,hy⟩ hyx⟩)
    ft pred (KP.limit0_m .newest) (by simp -implicitDefEqProofs) (KP.limit0_delta_l _)
    a₁ b₁ (fun _ => points 3)
  have limitP : Pn.IsLimitOrdinal (η.bound 3) :=
    (KP.limit0_sat_l hP b₁ .newest).mp (transfer.mp ((KP.limit0_sat_l hN a₁ .newest).mpr limit))
  have finiteP : Pn.mem (η.bound 4) (η.bound 0) :=
    (pred _ _ (points 0) _).mpr ⟨_,realized.finite,points 4⟩
  obtain ⟨Bc,Vc,Dq,rankBc,constantsVc,poolDc,realizedP⟩ :=
    td_round_realize_l nativeP ζ transferred η valid coupled program' limitP finiteP
  -- 查询码是同一 u 的成员，完整前驱图实际给出它们的像。
  have huY : Nn.mem (ρ.bound 13) Yc :=
    ((carrier' _).mp (ft.1.input_mem_of_pairMember (points 6))).2
  have carryQuery (q : Nn.Domain) (hq : Nn.mem q (ρ.bound 13)) :
      ∃ q' : Pn.Domain, Rd_entry_d q.val q'.val t ∧ Pn.mem q' (η.bound 6) := by
    obtain ⟨a,ha,qa⟩ := ft.1.2.2 q.val
      ((carrier' q.val).mpr ⟨q.property,collapse.transitive _ huY q hq⟩)
    exact ⟨⟨a,ha⟩,qa,(pred _ _ (points 6) _).mpr ⟨q.val,hq,qa⟩⟩
  obtain ⟨pn',ipn,hpn⟩ := carryQuery pn nodeMember
  obtain ⟨pm',ipm,hpm⟩ := carryQuery pm maxMember
  -- 原请求的节点码只用于同一实现内的比较；实际运输的是已编译的列及其数值程序。
  have hwY : Nn.mem (ρ.bound 0) Yc := ((carrier' _).mp (ft.1.input_mem_of_pairMember (points 0))).2
  have hpY := collapse.transitive _ huY pc canonicalMember
  have queryParts := nodeCode
  obtain ⟨Cq,as,ak,pair,ks,kk,_,si,ki⟩ := queryParts
  have hC := (pair.mem_l Nn collapse.transitive hpY).2
  have hsY := (ks.mem_l Nn collapse.transitive (rd_entry_transitive_l collapse.transitive hC si).2).1
  have hkY := (kk.mem_l Nn collapse.transitive (rd_entry_transitive_l collapse.transitive hC ki).2).1
  have hqω : Nn.mem (ι.bound 27) (ρ.bound 0) := arityEq ▸ type.finite
  have heω := omega.transitive hN _ hqω _ heq
  let ξ : Env Nn 10 := ⟨fun i => [ρ.bound 0,ι.bound 1,ι.bound 27,is,ik,zn,ρ.bound 9,pc,s₀,ι.bound 23].get i,ρ.free⟩
  have all : ∀ i, Nn.mem (ξ.bound i) Yc :=
    Fin.cases hwY (Fin.cases (collapse.transitive _ hwY _ heω)
      (Fin.cases (collapse.transitive _ hwY _ hqω) (Fin.cases (collapse.transitive _ hwY _ his)
        (Fin.cases (collapse.transitive _ hwY _ hik) (Fin.cases (collapse.transitive _ hwY _ nodeProgram.1)
          (Fin.cases (((carrier' _).mp (ft.1.input_mem_of_pairMember (points 4))).2)
            (Fin.cases hpY (Fin.cases hsY (Fin.cases hkY (fun i => Fin.elim0 i))))))))))
  obtain ⟨q,iq⟩ := Classical.axiomOfChoice (fun i : Fin 10 =>
    ft.1.2.2 (ξ.bound i).val ((carrier' _).mpr ⟨(ξ.bound i).property,all i⟩))
  let θ : Env Pn 10 := ⟨fun i => ⟨q i,(iq i).1⟩,η.free⟩
  have iw : θ.bound 0 = η.bound 0 := Subtype.ext (ft.1.1.2 _ _ _ (iq 0).2 (points 0))
  have inn : θ.bound 6 = η.bound 4 := Subtype.ext (ft.1.1.2 _ _ _ (iq 6).2 (points 4))
  let a : Env Nn 6 := ξ.reindex (fun i => i.castAdd 4)
  let b : Env Pn 6 := θ.reindex (fun i => i.castAdd 4)
  have nums : ∀ i : Fin 6, a.bound i = ρ.bound 0 ∨ Nn.mem (a.bound i) (ρ.bound 0) :=
    Fin.cases (Or.inl rfl) (Fin.cases (Or.inr heω) (Fin.cases (Or.inr hqω)
      (Fin.cases (Or.inr his) (Fin.cases (Or.inr hik) (Fin.cases (Or.inr nodeProgram.1) (fun i => Fin.elim0 i))))))
  have programImage := (smap_numeric_model_peer_l hZF hΩ root.model mn mp fromN rootMap root.ext
    (fromN.extensional_l hZF hΩ root.model mn root.ext) (certificate root).ext
    rootNumbers numbers newNumbers td_node_program0_m td_node_program0_closed_l a b (fun i => by
      rcases nums i with eq | hi
      · exact Or.inl ⟨congrArg Subtype.val eq,
          (ft.1.1.2 _ _ _ (congrArg Subtype.val eq ▸ (iq (i.castAdd 4)).2) (points 0)).trans ew₁⟩
      · exact Or.inr (digits _ _ hi (iq (i.castAdd 4)).2))).mp
        ((td_node_program_sat_l (kp_pair_l hN) native.1 a).mpr nodeProgram)
  have programTarget := (td_node_program_sat_l (kp_pair_l hP) nativeP.1 b).mp programImage
  let pick : Fin 7 → Fin 10 := fun i => [6,3,4,5,7,8,9].get i
  have codeTarget := td_node_code_image_l I mn.2.1 mp.2.1 hN hP Yc collapse.transitive
    carrier' ft pred (ξ.reindex pick) (θ.reindex pick) (fun i => (iq (pick i)).2) nodeCode
  have hlP : Pn.mem (θ.bound 2) (θ.bound 6) :=
    (pred _ _ (iq 6).2 _).mpr ⟨_,hqn,(iq 2).2⟩
  have heP : Pn.mem (θ.bound 1) (θ.bound 2) :=
    (pred _ _ (iq 2).2 _).mpr ⟨_,heq,(iq 1).2⟩
  have memberP : Pn.mem (θ.bound 7) (η.bound 6) :=
    (pred _ _ (points 6) _).mpr ⟨_,canonicalMember,(iq 7).2⟩
  have actualP := realizedP
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,typeP,_⟩ := actualP
  have hpD := ((typeP.truth (θ.bound 7)).mp memberP).1
  have omegaP : Pn.IsOmega (θ.bound 0) := iw.symm ▸ (coupled 0).symm ▸ (td_round_native_l hP ζ transferred).1
  have poolP : Tt_pool_d (kp_pair_l hP) (θ.bound 0) (θ.bound 6) Vc Dq := iw.symm ▸ inn.symm ▸ poolDc
  have nodeP := programTarget.query_l nativeP omegaP hlP heP poolP hpD codeTarget
  have nodeP : Td_node_query_d (kp_pair_l hP) (η.bound 0) (θ.bound 1) (η.bound 4)
      (θ.bound 2) Vc Dq (θ.bound 8) (θ.bound 9) (θ.bound 7) := iw ▸ inn ▸ nodeP
  obtain ⟨zm',hzm',izz⟩ := ft.1.2.2 zm.val
    ((carrier' _).mpr ⟨zm.property,collapse.transitive _ hwY zm maxProgram.1⟩)
  let zmP : Pn.Domain := ⟨zm',hzm'⟩
  obtain ⟨qmP,ipmP,hmP⟩ := carryQuery qm canonicalMax
  let am : Env Nn 3 := ⟨fun i => [ρ.bound 0,ι.bound 1,zm].get i,ρ.free⟩
  let bm : Env Pn 3 := ⟨fun i => [η.bound 0,θ.bound 1,zmP].get i,η.free⟩
  have maxImage := (smap_numeric_model_peer_l hZF hΩ root.model mn mp fromN rootMap root.ext
    (fromN.extensional_l hZF hΩ root.model mn root.ext) (certificate root).ext
    rootNumbers numbers newNumbers td_max_program0_m td_max_program0_closed_l am bm
    (Fin.cases (Or.inl ⟨rfl,ew₁⟩) (Fin.cases (Or.inr (digits _ _ heω (iq 1).2))
      (Fin.cases (Or.inr (digits zm zmP maxProgram.1 izz)) (fun i => Fin.elim0 i))))).mp
        ((td_max_program_sat_l (kp_pair_l hN) native.1 am).mpr maxProgram)
  let ac : Env Nn 4 := ⟨fun i => [ι.bound 1,ι.bound 27,zm,qm].get i,ρ.free⟩
  let bc : Env Pn 4 := ⟨fun i => [θ.bound 1,θ.bound 2,zmP,qmP].get i,η.free⟩
  have maxColumn := td_max_code_image_l I mn.2.1 mp.2.1 hN hP Yc collapse.transitive carrier'
    ft pred ac bc (Fin.cases (iq 1).2 (Fin.cases (iq 2).2
      (Fin.cases izz (Fin.cases ipmP (fun i => Fin.elim0 i))))) maxCode
  have maxP := ((td_max_program_sat_l (kp_pair_l hP) nativeP.1 bm).mp maxImage).query_l nativeP
    (iw ▸ omegaP) poolDc (((typeP.truth qmP).mp hmP).1) maxColumn
  -- 两个后继关系使用对象模型自己的计数；旧节点编号由父边常值方块识别。
  have issuedData := (td_issued_sat_l (kp_pair_l hN) hN.1 ι).mp issued
  have hkω : Nn.mem (ι.bound 23) (ρ.bound 0) := (newCoords 0).symm ▸ issuedData.payload.2.1
  have hjω := omega.transitive hN _ hkω _ next.predecessor_mem
  have hjβ := (v_transitive_l (kp_pair_l hN) rankβ) _ hwβ' _ hjω
  have ij : Rd_entry_d j₀.val (ζ.bound 25).val t :=
    (commute j₀ j₀ (old.bound 25).val (ζ.bound 25).val hjβ (natural j₀ hjω)
      ((inverse _ _).mpr (view 11))).mpr (images 25).2
  have currentArity := issuedData.payload.2.2.2.1
  have sn : Nn.SuccessorOf (ρ.bound 9) (ι.bound 27) := (newCoords 3).symm ▸ currentArity.2.2.1
  let sa : Env Nn 4 := ⟨fun i => [ι.bound 23,j₀,ρ.bound 9,ι.bound 27].get i,ρ.free⟩
  let sb : Env Pn 4 := ⟨fun i => [θ.bound 9,ζ.bound 25,η.bound 4,θ.bound 2].get i,η.free⟩
  let φ : Formula 1 4 := .conj (KP.succ0_m (.bound 0) (.bound 1)) (KP.succ0_m (.bound 2) (.bound 3))
  have successors : Formula.satisfies sb φ := (rr_graph_delta_l I mn.2.1 mp.2.1
    ⟨(ρ.bound 0).val,ft.1.input_mem_of_pairMember (points 0)⟩
    (fun x hx => ((carrier' x).mp hx).1)
    (fun x y hx hy hxy => (carrier' y).mpr ⟨hy,collapse.transitive
      ⟨x,((carrier' x).mp hx).1⟩ ((carrier' x).mp hx).2 ⟨y,hy⟩ hxy⟩)
    ft pred φ (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed])
    (.conj (KP.succ0_delta_l ..) (KP.succ0_delta_l ..)) sa sb
    (Fin.cases (iq 9).2 (Fin.cases ij (Fin.cases (points 4) (Fin.cases (iq 2).2 (fun i => Fin.elim0 i)))))).mp (by
      simp only [φ,Formula.satisfies_conj_iff,KP.succ0_sat_l hN.1]
      exact ⟨next,sn⟩)
  have steps := successors
  simp only [φ,Formula.satisfies_conj_iff,KP.succ0_sat_l hP.1] at steps
  have el : θ.bound 2 = ζ.bound 9 :=
    (Subtype.ext (ft.1.1.2 _ _ _ ((congrArg Subtype.val arityEq).symm ▸ (iq 2).2) (points 1))).trans (coupled 1)
  have rules := (td_rules_sat_l native ..).mp control.2.2.1
  have emptyP (x : Pn.Domain) (hx : Pn.mem x (θ.bound 1)) : False := by
    obtain ⟨a,ha,_⟩ := (pred _ _ (iq 1).2 x.val).mp hx
    exact rules.empty ⟨a,(mn.2.2.2 _ _ ha).1⟩ ha
  have oldSeed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp transferred).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at oldSeed
  have emptyOld := (Formula.satisfies_isEmpty_iff ..).mp oldSeed.2.1
  have ee : θ.bound 1 = ζ.bound 20 := nativeP.1.eq_of_same_members _ _
    (fun x => ⟨fun hx => (emptyP x hx).elim,fun hx => (emptyOld x hx).elim⟩)
  have recovery := td_round_recover_l nativeP ζ transferred
    (show Pn.SuccessorOf (θ.bound 9) (ζ.bound 25) from steps.1)
    (show Pn.SuccessorOf (η.bound 4) (ζ.bound 9) from el ▸ steps.2)
    ((coupled 0) ▸ (coupled 1) ▸ realizedP)
    ((coupled 0) ▸ ee ▸ el ▸ nodeP) ((coupled 0) ▸ el ▸ maxP) memberP hmP
  obtain ⟨ν₁,X₁,c₁,R₁,r₁,a₁,b₁,z₁,π₁,recovered⟩ := recovery
  -- 原加倍关系不是有界公式；五个内部自然数经共同根保留其完整定义。
  have hdω := ZF.ordinalAddition_mem_omega native (kp_pair_l hN) omega hkω hkω currentArity.1
  have hmω : Nn.mem (ι.bound 29) (ρ.bound 0) := by
    obtain ⟨m,sm,hm⟩ := omega.1.2 (ρ.bound 9) realized.finite
    have sm' : Nn.SuccessorOf (ι.bound 29) (ρ.bound 9) := (newCoords 3).symm ▸ currentArity.2.2.2
    exact sm.eq native.1 sm' ▸ hm
  obtain ⟨dp,hdp,idp⟩ := ft.1.2.2 (ι.bound 26).val
    ((carrier' _).mpr ⟨(ι.bound 26).property,collapse.transitive _ hwY _ hdω⟩)
  obtain ⟨mp₀,hmp,imp⟩ := ft.1.2.2 (ι.bound 29).val
    ((carrier' _).mpr ⟨(ι.bound 29).property,collapse.transitive _ hwY _ hmω⟩)
  let dP : Pn.Domain := ⟨dp,hdp⟩
  let mP : Pn.Domain := ⟨mp₀,hmp⟩
  let aa : Env Nn 5 := ⟨fun i => [ι.bound 23,ι.bound 26,ι.bound 27,ρ.bound 9,ι.bound 29].get i,ρ.free⟩
  let ab : Env Pn 5 := ⟨fun i => [θ.bound 9,dP,η.bound 1,η.bound 4,mP].get i,η.free⟩
  have arityPoints : ∀ i, Rd_entry_d (aa.bound i).val (ab.bound i).val t :=
    Fin.cases (iq 9).2 (Fin.cases idp (Fin.cases
      (congrArg Subtype.val arityEq ▸ points 1) (Fin.cases (points 4) (Fin.cases imp (fun i => Fin.elim0 i)))))
  have arityFinite : ∀ i, Nn.mem (aa.bound i) (ρ.bound 0) :=
    Fin.cases hkω (Fin.cases hdω (Fin.cases hqω (Fin.cases realized.finite (Fin.cases hmω (fun i => Fin.elim0 i)))))
  have arityImage := (smap_numeric_model_peer_l hZF hΩ root.model mn mp fromN rootMap root.ext
    (fromN.extensional_l hZF hΩ root.model mn root.ext) (certificate root).ext
    rootNumbers numbers newNumbers (td_arity_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (by simp -implicitDefEqProofs) aa ab
    (fun i => Or.inr (digits _ _ (arityFinite i) (arityPoints i)))).mp
      ((td_arity_sat_l (kp_pair_l hN) native.1 aa (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr
        (by
          change Td_arity_d (kp_pair_l hN) (ι.bound 23) (ι.bound 26) (ι.bound 27) (ρ.bound 9) (ι.bound 29)
          exact (show ι.bound 28 = ρ.bound 9 from (newCoords 3).symm) ▸ currentArity))
  have arityP := (td_arity_sat_l (kp_pair_l hP) nativeP.1 ab
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp arityImage
  -- 旧实数字母域在旧临界点以下，因此两个共同层与父边给出同一个像。
  obtain ⟨rankOld,lettersOld⟩ := td_round_letters_l groundA old oldRound
  let Uold : (smdl_structure_l I (R := s.R) ma.2.1).Domain := ⟨s.U,common.left_rank.2.1⟩
  have rankUold := (rr_rank_native_l I ma.2.1 (ZF.modelsKP groundA)
    ⟨L₀,common.left_rank.1⟩ Uold).mp common.left_rank
  have rankInside := ZF.v_mem_l (kp_pair_l (ZF.modelsKP groundA)) groundA rankOld rankUold below
  have lettersInside := (v_transitive_l (kp_pair_l (ZF.modelsKP groundA)) rankUold)
    _ rankInside _ lettersOld
  obtain ⟨an,han,ian⟩ := common.injection.1.2.2 (old.bound 50).val
    ((common.carrier _).mpr ⟨(old.bound 50).property,lettersInside⟩)
  let Acur : Nn.Domain := ⟨an,han⟩
  have pointBase : Rd_entry_d (old.bound 1).val (ρ.bound 4).val g :=
    (congrArg Subtype.val (oldCoords 3)).symm ▸ view 3
  -- 旧行保存的低秩条件经其共同图给出当前切片的界，不另设历史界回调。
  have rankγN := (rr_rank_native_l I mn.2.1 hN
    ⟨γN,slice.rank.1⟩ ⟨VN,slice.rank.2.1⟩).mp slice.rank
  have rootDomain : M.MemberSubset D₀ X₀ := by
    intro a ha
    obtain ⟨x,_,ax⟩ := slice.injection.1.2.2 a ha
    exact fromN.1.1.input_mem_of_pairMember (slice.root a x ax)
  have cutBelow : Nn.MemberSubset ⟨VN,slice.rank.2.1⟩ (ρ.bound 4) := by
    intro x hx
    obtain ⟨a,ha,ax⟩ := (slice.image x.val).mp hx
    obtain ⟨y,_,ay⟩ := fromA.1.1.2.2 a (rootDomain a ha)
    exact (common.pred _ _ pointBase x.val).mpr
      ⟨y,saved.root_low a y ha ay,(roots a ha y ay x.val).mpr (slice.root a x.val ax)⟩
  have lowerτ x (hx : Rd_entry_d x γN R) : Rd_entry_d x (ρ.bound 1).val R := by
    let a : Nn.Domain := ⟨x,(mn.2.2.2 x γN hx).1⟩
    exact ZF.v_ordinal_height_l native language.rank
      ((v_ordinal_l (kp_pair_l hN) rankγN).mem (show Nn.mem a ⟨γN,slice.rank.1⟩ from hx))
      (cutBelow a (KP.v_ordinal_subset_l hN rankγN a hx))
  have rootComp : It_comp_d qA jP qP := ⟨rootMap.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨a,xa,ay⟩ => ⟨fromA.1.1.input_mem_of_pairMember xa,a,xa,ay⟩⟩⟩
  obtain ⟨CP,_,contextP⟩ := rootMap.1.1.2.2 C₀
    (fromN.1.1.input_mem_of_pairMember slice.context)
  obtain ⟨γP,VP,tP,iγ,iV,comp,sliceP,_,rootsP⟩ :=
    slice.continue_step_l hZF commonP mn mp hN hP (ρ.bound 1) Klow rankLow hκ
      lowerτ roots inverse (fun x hx y E back => lowSquare x y E hx back)
      fromN.1.1.1 fromA.1.1 rootDomain rootComp contextP
  have memberBase : Nn.mem Acur (ρ.bound 4) :=
    (common.pred _ _ pointBase _).mpr ⟨_,lettersOld,ian⟩
  have equalLow := ZF.v_unique_l (kp_pair_l hN) native language.rank rankLow
  have memberCurrent := ZF.v_mono_l (kp_pair_l hN) native language.rank rank
    (fun x hx => limit.1.transitive _ exceeds.1 x hx) Acur memberBase
  have sourceCandidate := (tg_candidate_sat_l ground ψ).mp candidate |>.1
  have equalBase := ZF.v_unique_l (kp_pair_l hN) native
    ((candidateLinks 3) ▸ sourceCandidate.rank) rank
  have aUl := (v_transitive_l (kp_pair_l hN) rankUl)
    _ (ZF.v_mem_l (kp_pair_l hN) native rank rankUl hτ) Acur memberCurrent
  obtain ⟨ap,hap,iap⟩ := commonP.injection.1.2.2 an
    ((commonP.carrier _).mpr ⟨han,aUl⟩)
  have parentA := (lowSquare Acur (old.bound 50).val ap
    (equalLow ▸ memberBase) ((inverse _ _).mpr ian)).mp iap
  have ea : ap = (ζ.bound 50).val := embed.1.1.1.2 _ _ _ parentA (images 50).2
  have originalLow : M.mem Ar D₀ := by
    obtain ⟨a,ha,ax⟩ := (slice.image (ι.bound 6).val).mp lettersLow
    exact fromN.1.2 a Ar _ (slice.root a _ ax) lettersRoot ▸ ha
  have oldA : Rd_entry_d (old.bound 50).val (ι.bound 6).val g :=
    (roots Ar originalLow _ saved.letters_root _).mpr lettersRoot
  have equalA : Acur = ι.bound 6 :=
    Subtype.ext (common.injection.1.1.2 _ _ _ ian oldA)
  have pointA : Rd_entry_d (ι.bound 6).val (ζ.bound 50).val gp :=
    congrArg Subtype.val equalA ▸ ea ▸ iap
  have lettersCurrent : Pn.mem (ζ.bound 50) (ψp.bound 5) := by
    change Rd_entry_d (ζ.bound 50).val (ψp.bound 5).val S
    exact ea ▸ (commonP.pred _ _ (candidatePoints 5) ap).mpr
      ⟨an,equalBase.symm ▸ memberCurrent,iap⟩
  -- 恢复图、当前语言、dcp、程序以及历史界共同构成完整下一输入。
  have candidateData := (tg_candidate_sat_l ((certificate root).native_l I hZF hΩ) ψp).mp candidateP
  have langP := candidateData.1
  obtain ⟨vP,dropP,elasticP⟩ := candidateData.2
  have baseP := ZF.v_unique_l (kp_pair_l hP) nativeP ((candidateSame 3) ▸ langP.rank) rankBc
  have constantsP : ψp.bound 6 = Vc := nativeP.1.eq_of_same_members _ _ (fun x => by
    rw [langP.constants x,constantsVc x,baseP,show ψp.bound 3 = η.bound 3 from candidateSame 3])
  have languageP : Ee_language_d nativeP (ζ.bound 19) (η.bound 3) (η.bound 1) Bc Vc (ψp.bound 7)
      ⟨ψp.bound 8,ψp.bound 9,ψp.bound 10,ψp.bound 11⟩ :=
    (coupled 0) ▸ (candidateSame 2) ▸ (candidateSame 3) ▸ (candidateSame 4) ▸ baseP ▸ constantsP ▸ langP
  have dropP : Td_dcp_d (kp_pair_l hP) (η.bound 1) (η.bound 4) (ψp.bound 7) (η.bound 6) vP :=
    (candidateSame 4) ▸ (candidateSame 1) ▸ (candidateSame 0) ▸ dropP
  have inherited := oldSeed
  simp only [Formula.satisfies_isOmega_iff,Formula.satisfies_isEmpty_iff,
    woodin_sat_l (kp_pair_l hP) nativeP.1,tg_low_sat_l nativeP,tg_node_sat_l (kp_pair_l hP) nativeP.1,
    td_tree_sat_l (kp_pair_l hP) nativeP.1,td_alphabet_sat_l nativeP.1,
    td_separated_sat_l nativeP.1,Formula.satisfies_mem_iff] at inherited
  obtain ⟨hwP,heP,woodinP,lowP,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,treeP,_,alphabetP,chosenP,_,_,sepP⟩ := inherited
  have ordinalData := woodinP
  obtain ⟨_,_,_,_,regP,_⟩ := ordinalData
  have targetRound := (Formula.satisfies_conj_iff ..).mp transferred |>.2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at targetRound
  have ebκ : bκ = (old.bound 0).val := fv.1.1.2 _ _ _ iκv (back 2)
  have ecap : κcap = (ζ.bound 0).val := embed.1.1.1.2 _ _ _ (ebκ ▸ iκj) (images 0).2
  let χP : Pn.Domain := ⟨lp,commonP.right_rank.1⟩
  have rankVp := (rr_rank_native_l I mp.2.1 hP χP ⟨Vp,commonP.right_rank.2.1⟩).mp commonP.right_rank
  have χδ : Pn.mem χP (ζ.bound 21) := ordinal_down_l hP
    (v_ordinal_l (kp_pair_l hP) rankVp) regP.isLimitOrdinal.1
    (fun x hx => by
      change Rd_entry_d x.val (ζ.bound 0).val S
      exact ecap ▸ capP x.val hx) targetRound.2.2.1
  have κχ : Pn.mem (η.bound 3) χP := (pred _ _ endpointP _).mpr ⟨_,hτ,points 3⟩
  have κδ := regP.isLimitOrdinal.1.transitive χP χδ _ κχ
  obtain ⟨textP,progP⟩ := (ts_numeric0_sat_l nativeP _).mp program'
  have recoveryData := recovered
  obtain ⟨_,rank₁,model₁,real₁,_,_,height₁,root₁,last₁,_,node₁,groups₁,_⟩ := recoveryData
  have lastP : Rd_entry_d (η.bound 1) (ζ.bound 23) r₁ := by
    rw [show η.bound 1 = ζ.bound 9 from coupled 1]
    exact last₁
  have groupsP : Td_groups_d (kp_pair_l hP) (ζ.bound 19) (ζ.bound 20) (η.bound 1) r₁ a₁ b₁ := by
    rw [show η.bound 1 = ζ.bound 9 from coupled 1]
    exact groups₁
  have progSeed : Ts_program_d nativeP (ζ.bound 19) (η.bound 1) (η.bound 7)
      (fun i : Fin 7 => [η.bound 10,η.bound 11,η.bound 12,η.bound 13,η.bound 14,η.bound 15,η.bound 16].get i)
      textP (η.bound 8) := by
    rw [← show η.bound 0 = ζ.bound 19 from coupled 0]
    exact progP
  obtain ⟨dep,tab,depthStep,depth,tableGraph⟩ := saved.depth.step_l hZF hΩ embed.1.1
    (fun _ _ xy hx => (embed.relation_l I hZF hΩ ma mp xy (images 47).2).mp hx)
    saved.enumeration.function saved.enumeration.letters
  obtain ⟨chosen,hChosen,chosenLetter,scheduled⟩ :=
    depth.pick_l hZF hΩ (ζ.bound 49).property chosenP
  let zP : Pn.Domain := ⟨chosen,hChosen⟩
  let ξ : Env Pn 43 := ⟨fun i =>
    [ζ.bound 19,ζ.bound 20,ζ.bound 21,ζ.bound 22,ζ.bound 23,η.bound 3,θ.bound 9,dP,η.bound 1,η.bound 4,
      ν₁,X₁,c₁,R₁,r₁,Bc,Vc,ψp.bound 7,Dq,η.bound 6,vP,η.bound 7,textP,η.bound 8,χP,
      θ.bound 8,a₁,b₁,ζ.bound 47,ζ.bound 48,zP,ζ.bound 50,
      ψp.bound 8,ψp.bound 9,ψp.bound 10,ψp.bound 11,
      η.bound 10,η.bound 11,η.bound 12,η.bound 13,η.bound 14,η.bound 15,η.bound 16].get i,η.free⟩
  have seedP : Formula.satisfies ξ td_seed0_m := by
    simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
      Formula.satisfies_isEmpty_iff,woodin_sat_l (kp_pair_l hP) nativeP.1,tg_low_sat_l nativeP,
      Formula.satisfies_mem_iff,Formula.satisfies_isOrdinalAddition_iff (kp_pair_l hP) nativeP.1,
      Formula.satisfies_isSuccessor_iff,v_sat_l (kp_pair_l hP) nativeP.1,smem_sat_l (kp_pair_l hP),
      tt_realized_sat_l (kp_pair_l hP) hP,ee_language_sat_l ((certificate root).native_l I hZF hΩ),
      td_dcp_sat_l (kp_pair_l hP) nativeP.1,ee_elastic_sat_l,rd_entry0_sat_l nativeP.1,
      td_groups_sat_l (kp_pair_l hP) nativeP.1,tg_node_sat_l (kp_pair_l hP) nativeP.1,
      td_tree_sat_l (kp_pair_l hP) nativeP.1,td_alphabet_sat_l nativeP.1,ts_program_sat_l nativeP,
      td_separated_sat_l nativeP.1,tt_eval_cases_l]
    refine ⟨hwP,heP,woodinP,lowP,κδ,arityP.1,arityP.2.1,arityP.2.2.1,
      height₁,rank₁,model₁,real₁,languageP,dropP,elasticP,root₁,
      lastP,groupsP,node₁,treeP,
      (constantsVc _).mpr (Or.inl (baseP ▸ lettersCurrent)),alphabetP,chosenLetter,?_,χδ,sepP⟩
    have eq : (Fin.cases (η.bound 10) (Fin.cases (η.bound 11) (Fin.cases (η.bound 12)
        (Fin.cases (η.bound 13) (Fin.cases (η.bound 14) (Fin.cases (η.bound 15) (fun _ => η.bound 16))))))) =
        (fun i : Fin 7 => [η.bound 10,η.bound 11,η.bound 12,η.bound 13,η.bound 14,η.bound 15,η.bound 16].get i) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    exact eq.symm ▸ progSeed
  obtain ⟨resumed,resumedSame,resumedRound⟩ :=
    td_seed_native_l ((certificate root).native_l I hZF hΩ) ξ seedP
  have lowerP x (hx : Rd_entry_d x γP S) : Rd_entry_d x (ξ.bound 5).val S := by
    obtain ⟨a,ha,ax⟩ := (commonP.pred γN γP iγ x).mp hx
    have low : Nn.mem ⟨a,(mn.2.2.2 a γN ha).1⟩ (ρ.bound 8) :=
      limit.1.transitive (ρ.bound 1) exceeds.1 _ (lowerτ a ha)
    exact (pred _ _ (points 3) x).mpr ⟨a,low,((restrictP.2 a x).mp ax).2⟩
  obtain ⟨rankResumed,_⟩ := td_round_letters_l nativeP resumed resumedRound
  have renewed := td_round_native_l hP resumed resumedRound
  have subResumed : Pn.MemberSubset ⟨VP,sliceP.rank.2.1⟩ (resumed.bound 1) :=
    (KP.v_compare_l hP
      ((rr_rank_native_l I mp.2.1 hP ⟨γP,sliceP.rank.1⟩ ⟨VP,sliceP.rank.2.1⟩).mp sliceP.rank)
      rankResumed (fun x hx => renewed.2.2.1.1.transitive (resumed.bound 24)
        renewed.2.2.2.1 x ((resumedSame 5).symm ▸
          (show Pn.mem x (ξ.bound 5) from lowerP x.val hx)))).1
  have rootLow a x (ha : M.mem a D₀) (ax : Rd_entry_d a x qP) :
      Rd_entry_d x (resumed.bound 1).val S := by
    obtain ⟨y,hy,ay⟩ := sliceP.injection.1.2.2 a ha
    have eq := rootMap.1.1.1.2 a y x (sliceP.root a y ay) ax
    exact eq ▸ subResumed ⟨y,hy⟩ ((sliceP.image y).mpr ⟨a,ha,ay⟩)
  have cutPoint (x : Nn.Domain) (y : Pn.Domain) (hx : Nn.mem x Ul)
      (xy : Rd_entry_d x.val y.val t) : Rd_entry_d x.val y.val gp :=
    (restrictP.2 _ _).mpr ⟨(commonP.carrier _).mpr ⟨x.property,hx⟩,xy⟩
  have cutNatural (x : Nn.Domain) (y : Pn.Domain) (hx : Nn.mem x (ρ.bound 0))
      (xy : Rd_entry_d x.val y.val t) : Rd_entry_d x.val y.val gp :=
    cutPoint x y ((v_transitive_l (kp_pair_l hN) rankUl) _ hwUl x hx) xy
  have seedPoints : ∀ i : Fin 17, Rd_entry_d
      (ι.bound ([0,23,24,27,28,25,31,32,37,38,39,40,41,42,43,44,45].get i)).val
      (ξ.bound ([0,6,5,8,9,19,16,17,21,23,36,37,38,39,40,41,42].get i)).val gp := by
    have pw := cutPoint (ρ.bound 0) (η.bound 0) hwUl (points 0)
    have pk := cutNatural (ι.bound 23) (θ.bound 9) hkω (iq 9).2
    have pκ := (congrArg Subtype.val ((candidateLinks 3).trans (newCoords 2))) ▸
      (congrArg Subtype.val (candidateSame 3)) ▸ candidatePoints 3
    have pq := cutNatural (ρ.bound 3) (η.bound 1) type.finite (points 1)
    have pn := cutNatural (ρ.bound 9) (η.bound 4) realized.finite (points 4)
    have pu := (congrArg Subtype.val ((candidateLinks 0).trans (newCoords 4))) ▸
      (congrArg Subtype.val (candidateSame 0)) ▸ candidatePoints 0
    have pU := (congrArg Subtype.val candidateU) ▸ (congrArg Subtype.val constantsP) ▸ candidatePoints 6
    have pE := (congrArg Subtype.val candidateE) ▸ candidatePoints 7
    have programPoint (i : Fin 9) := cutNatural
      (ε.bound ([7,8,10,11,12,13,14,15,16].get i)) (η.bound ([7,8,10,11,12,13,14,15,16].get i))
      (codes i) (points _)
    have programPoint' : ∀ i : Fin 9, Rd_entry_d
        (ι.bound ([37,38,39,40,41,42,43,44,45].get i)).val
        (η.bound ([7,8,10,11,12,13,14,15,16].get i)).val gp := by
      intro i
      have eq : ε.bound ([7,8,10,11,12,13,14,15,16].get i) =
          ι.bound ([37,38,39,40,41,42,43,44,45].get i) :=
        Fin.cases (newCoords 5) (Fin.cases (newCoords 6) (Fin.cases (newCoords 7)
          (Fin.cases (newCoords 8) (Fin.cases (newCoords 9) (Fin.cases (newCoords 10)
            (Fin.cases (newCoords 11) (Fin.cases (newCoords 12) (Fin.cases (newCoords 13)
              (fun j => Fin.elim0 j))))))))) i
      exact congrArg Subtype.val eq ▸ programPoint i
    exact Fin.cases ((congrArg Subtype.val (newCoords 0)) ▸
      (congrArg Subtype.val (coupled 0)) ▸ pw)
      (Fin.cases pk (Fin.cases pκ (Fin.cases ((congrArg Subtype.val arityEq) ▸ pq)
        (Fin.cases ((congrArg Subtype.val (newCoords 3)) ▸ pn) (Fin.cases pu (Fin.cases pU
          (Fin.cases pE (Fin.cases (programPoint' 0) (Fin.cases (programPoint' 1)
            (Fin.cases (programPoint' 2) (Fin.cases (programPoint' 3) (Fin.cases (programPoint' 4)
              (Fin.cases (programPoint' 5) (Fin.cases (programPoint' 6)
                (Fin.cases (programPoint' 7) (Fin.cases (programPoint' 8) (fun j => Fin.elim0 j)))))))))))))))))
  have roundLetters : Rd_entry_d Ar (resumed.bound 50).val qP :=
    (congrArg Subtype.val (resumedSame 31)).symm ▸
      (rootComp.2 _ _).mpr ⟨_,saved.letters_root,(images 50).2⟩
  have roundTree : Rd_entry_d Sr (resumed.bound 22).val qP :=
    (congrArg Subtype.val (resumedSame 3)).symm ▸
      (rootComp.2 _ _).mpr ⟨_,saved.tree_root,(images 22).2⟩
  have pointA' : Rd_entry_d (ι.bound 6).val (resumed.bound 50).val gp :=
    (congrArg Subtype.val (resumedSame 31)).symm ▸ pointA
  have pointW : Rd_entry_d (ι.bound 0).val (resumed.bound 19).val gp :=
    (congrArg Subtype.val (resumedSame 0)).symm ▸ seedPoints 0
  have pointEmpty : Rd_entry_d (ι.bound 1).val (resumed.bound 20).val gp :=
    (congrArg Subtype.val (resumedSame 1)).symm ▸ congrArg Subtype.val ee ▸
      cutNatural (ι.bound 1) (θ.bound 1)
        (num_mem_l native.1 omega (show Num_d 0 (ι.bound 1) from rules.empty)) (iq 1).2
  have omegaP : Rd_entry_d (resumed.bound 19).val VP S :=
    (commonP.pred VN VP iV _).mpr ⟨_,omegaLow,pointW⟩
  have lettersP : Rd_entry_d (resumed.bound 50).val VP S :=
    (commonP.pred VN VP iV _).mpr ⟨_,lettersLow,pointA'⟩
  -- 第二施加直接读取已更新的同一回合，不在调用处重新换槽或重选回合。
  have roundPoints : ∀ i : Fin 17, Rd_entry_d
      (ι.bound ([0,23,24,27,28,25,31,32,37,38,39,40,41,42,43,44,45].get i)).val
      (resumed.bound ([19,25,24,27,28,38,35,36,40,42,55,56,57,58,59,60,61].get i)).val gp := by
    intro i
    have eq : resumed.bound ([19,25,24,27,28,38,35,36,40,42,55,56,57,58,59,60,61].get i) =
        ξ.bound ([0,6,5,8,9,19,16,17,21,23,36,37,38,39,40,41,42].get i) :=
      Fin.cases (resumedSame 0) (Fin.cases (resumedSame 6) (Fin.cases (resumedSame 5)
        (Fin.cases (resumedSame 8) (Fin.cases (resumedSame 9) (Fin.cases (resumedSame 19)
          (Fin.cases (resumedSame 16) (Fin.cases (resumedSame 17) (Fin.cases (resumedSame 21)
            (Fin.cases (resumedSame 23) (Fin.cases (resumedSame 36) (Fin.cases (resumedSame 37)
              (Fin.cases (resumedSame 38) (Fin.cases (resumedSame 39) (Fin.cases (resumedSame 40)
                (Fin.cases (resumedSame 41) (Fin.cases (resumedSame 42)
                  (fun j => Fin.elim0 j))))))))))))))))) i
    exact (congrArg Subtype.val eq).symm ▸ seedPoints i
  -- 原父边运输的旧图在同次恢复中延长，旧调度字母进入第一图。
  have growthData := recovered
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,sa,sb,hit,_⟩ := growthData
  have rk : resumed.bound 25 = θ.bound 9 := resumedSame 6
  have ra : resumed.bound 45 = a₁ := resumedSame 26
  have rb : resumed.bound 46 = b₁ := resumedSame 27
  have growth := td_aux_growth_save_l I mp.2.1 nativeP.1 s.v ζ resumed
    (fun i => (images ([25,45,46,49].get i)).2)
    (rk.symm ▸ steps.1) (ra.symm ▸ sa) (rb.symm ▸ sb) (ra.symm ▸ hit)
  -- 实数短图来自同一原请求；它属于实际常量域，故沿同一共同图运输。
  let realEnv : Env Nn 4 := ⟨fun i => [ι.bound 4,ι.bound 2,ι.bound 20,s₀].get i,ι.free⟩
  have realTrace := (td_play_native_l I mn.2.1 hN realEnv).mpr shortPlay
  have realPoint : Rd_entry_d s₀.val (resumed.bound 44).val gp :=
    (congrArg Subtype.val (show resumed.bound 44 = θ.bound 8 from resumedSame 25)).symm ▸
      cutPoint s₀ (θ.bound 8) ((v_transitive_l (kp_pair_l hN) rankUl) _ hUUl s₀ shortMem) (iq 8).2
  exact ⟨X,K,R',L,F,c,d,Y,T,j,κ',U',D',u',rankX,source,regular.isLimitOrdinal,hL,hκ,hτ,above,
    loc,card,strong,mx,my,ultra,critical,bound,limitκ,iU,iD,iu,pool,subtype,
    α,β,B,v,hα,limitα,rankβ,hκβ,carrier,fv,inverse,
    Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,cP,P,S,jP,qP,pP,cert,
    mp,Ul,lp,Vp,Δp,gp,commonP,CP,γP,VP,tP,sliceP,iγ,iV,comp,rootsP,
    Ac,Qc,Yc,ec,Dc,Γc,t,owned,domain,carrier',ft,
    restrictP,endpointP,layerP,present,pred,commute,η,points,valid,
    ζ,fun i => (images i).2,transferred,coupled,program',
    nativeP,Bc,Vc,Dq,rankBc,constantsVc,poolDc,realizedP,pn',pm',ipn,ipm,hpn,hpm,
    θ.bound 1,θ.bound 2,θ.bound 8,θ.bound 9,θ.bound 7,qmP,
    Fin.cases (iq 1).2 (Fin.cases (iq 2).2 (Fin.cases (iq 8).2
      (Fin.cases (iq 9).2 (fun i => Fin.elim0 i)))),nodeP,memberP,maxP,hmP,
    ν₁,X₁,c₁,R₁,r₁,a₁,b₁,z₁,π₁,recovered,dep,tab,depthStep,depth,tableGraph,ξ,seedP,scheduled,(by
      intro i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))) i),
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    resumed,resumedSame,resumedRound,congrArg Subtype.val (resumedSame 24),roundPoints,
    (congrArg Subtype.val (show resumed.bound 47 = ζ.bound 47 from resumedSame 28)).symm ▸ depth,
    (congrArg Subtype.val (show resumed.bound 49 = zP from resumedSame 30)).symm ▸ scheduled,
    lowerP,rootLow,roundLetters,roundTree,omegaP,lettersP,
    Fin.cases pointEmpty (Fin.cases pointA' (fun i => Fin.elim0 i)),
    nextCount (resumed.bound 21).val
      ((congrArg Subtype.val (show resumed.bound 21 = ζ.bound 21 from resumedSame 2)).symm ▸ (images 21).2),
    congrArg Subtype.val (newCoords 1) ▸ hL,
    (congrArg Subtype.val (show resumed.bound 22 = ζ.bound 22 from resumedSame 3)).symm ▸
      (congrArg Subtype.val (show resumed.bound 21 = ζ.bound 21 from resumedSame 2)).symm ▸
        saved.alphabet_code.map_l hZF hΩ ma mp embed (images 22).2 (images 21).2,growth,realTrace,realPoint,lowerτ⟩

end YesMetaZFC.SetTheory.LargeCardinal
