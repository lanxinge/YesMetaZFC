import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn

/-! # 可沿可数壳搬运的分支下降见证

每项是原结点与原元素的有序对；后项属于前项在同一真实树边下的像。
全部见证有一个传递集合界，因而证书为 Δ₀，不涉及壳的外部可数闭性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_ladder_d (ω B Q G H D f : M.Domain) : Prop := Fn0_d ω D f ∧
  (∀ u, M.mem u D → ∃ i, M.mem i B ∧ ∃ x, M.mem x H ∧ ∃ c, M.mem c H ∧
    ∃ X, M.mem X H ∧ ∃ R, M.mem R H ∧ KPair_d M u i x ∧ Rd_entry_d i c Q ∧ KPair_d M c X R ∧ M.mem x X) ∧
  ∀ n m u v, M.mem n ω → M.mem m ω → M.mem u D → M.mem v D →
    M.SuccessorOf m n → Rd_entry_d n u f → Rd_entry_d m v f →
    ∃ i, M.mem i H ∧ ∃ j, M.mem j H ∧ ∃ x, M.mem x H ∧ ∃ y, M.mem y H ∧
    ∃ a, M.mem a H ∧ ∃ g, M.mem g H ∧ ∃ z, M.mem z H ∧
      KPair_d M u i x ∧ KPair_d M v j y ∧ KPair_d M a i j ∧ Rd_entry_d a g G ∧ Rd_entry_d x z g ∧ M.mem y z

def it_ladder_m {d} (ω B Q G H D f : Term d) : Formula 1 d := set[d] ⟪⌜fn0_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, ⌜f⌝ₛ) ∧
  (∀ u ∈ ⌜D⌝ₛ, ∃ i ∈ ⌜B⌝ₛ, ∃ x ∈ ⌜H⌝ₛ, ∃ c ∈ ⌜H⌝ₛ, ∃ X ∈ ⌜H⌝ₛ, ∃ R ∈ ⌜H⌝ₛ,
    ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(c, X, R) ∧ x ∈ X) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∀ m ∈ ⌜ω⌝ₛ, ∀ u ∈ ⌜D⌝ₛ, ∀ v ∈ ⌜D⌝ₛ,
    ⌜KP.succ0_m⌝ₚ(m, n) → ⌜rd_entry0_m⌝ₚ(n, u, ⌜f⌝ₛ) → ⌜rd_entry0_m⌝ₚ(m, v, ⌜f⌝ₛ) →
    ∃ i ∈ ⌜H⌝ₛ, ∃ j ∈ ⌜H⌝ₛ, ∃ x ∈ ⌜H⌝ₛ, ∃ y ∈ ⌜H⌝ₛ, ∃ a ∈ ⌜H⌝ₛ, ∃ g ∈ ⌜H⌝ₛ, ∃ z ∈ ⌜H⌝ₛ,
      ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜kpair0_m⌝ₚ(v, j, y) ∧ ⌜kpair0_m⌝ₚ(a, i, j) ∧
      ⌜rd_entry0_m⌝ₚ(a, g, ⌜G⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, z, g) ∧ y ∈ z)⟫
derive_free_closed it_ladder_m

theorem it_ladder_delta_l {d} (ω B Q G H D f : Term d) : (it_ladder_m ω B Q G H D f).IsDelta0 :=
by
  unfold it_ladder_m
  repeat first
    | exact fn0_delta_l .. | exact kpair0_delta_l .. | exact rd_entry0_delta_l .. | exact KP.succ0_delta_l .. | exact .mem ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.imp

theorem it_ladder_sat_l (hKP : M.Models KP) {d} (η : Env M d) (ω B Q G H D f : Term d) :
    Formula.satisfies η (it_ladder_m ω B Q G H D f) ↔
      It_ladder_d (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (H.eval η) (D.eval η) (f.eval η) := by
  simp only [it_ladder_m, It_ladder_d, Formula.satisfies_conj_iff, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    KP.succ0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, nodes, steps⟩ => ⟨f, nodes, fun n m u v hn hm hu hv => steps n hn m hm u hu v hv⟩,
    fun ⟨f, nodes, steps⟩ => ⟨f, nodes, fun n hn m hm u hu v hv => steps n m u v hn hm hu hv⟩⟩

theorem It_ill_branch_d.ladder_l (hZF : M.Models ZF) {ω α T Q G B : M.Domain}
    (dc : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (members : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (bad : It_ill_branch_d hZF ω α T Q G B) : ∃ H D f, It_ladder_d ω B Q G H D f := by
  classical
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, L, D, p, A, R, q, c, N, V, _, system, _, limit, _, ill⟩ := bad
  have descent : ∃ f, Fn0_d ω D f ∧ ∀ n m u v, M.SuccessorOf m n →
      Rd_entry_d n u f → Rd_entry_d m v f → Di_step_d p A R u v := by
    apply Classical.byContradiction
    intro no
    exact ill (di_wf_of_no_step_l hZF dc system.system limit
      (fun f hf hs => no ⟨f, hf, hs⟩))
  obtain ⟨f, ff, steps⟩ := descent
  obtain ⟨U, us⟩ := KP.exists_pair (ZF.modelsKP hZF) Q G
  obtain ⟨W, ws⟩ := KP.exists_pair (ZF.modelsKP hZF) U D
  obtain ⟨H, trans, hWH, _⟩ := ZF.tc_exists_l I hZF W
  have hUH := trans W hWH U ((ws U).mpr (Or.inl rfl))
  have hD := trans W hWH D ((ws D).mpr (Or.inr rfl))
  have hQ := trans U hUH Q ((us Q).mpr (Or.inl rfl))
  have hG := trans U hUH G ((us G).mpr (Or.inr rfl))
  refine ⟨H, D, f, ff, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, x, hi, pair, c, X, R, hc, code, hx⟩ := (system.tags.nodes u).mp hu
    have hcode := (rd_entry_transitive_l trans hQ hc).2
    have own := code.mem_l M trans hcode
    exact ⟨i, hi, x, trans X own.1 x hx, c, hcode, X, own.1, R, own.2, pair, hc, code, hx⟩
  · intro n m u v _ _ hu hv succ hnu hmv
    obtain ⟨j, w, hvj, hwj, huw, hvw⟩ := steps n m u v succ hnu hmv
    obtain ⟨i, x, _, ux, _⟩ := (system.tags.nodes u).mp hu
    obtain ⟨y, vy, _⟩ := system.tags.label_l hvj
    obtain ⟨z, wz, _⟩ := system.tags.label_l hwj
    obtain ⟨_, _, g, hg, hxz⟩ := (system.arrows u w i j x z ux wz).mp huw
    obtain ⟨_, _, c, X, S, hc, code, hyz⟩ := (system.tags.relation_l vy wz).mp hvw
    obtain ⟨X₀, S₀, mx⟩ := members j c hc
    obtain ⟨eqX, eqS⟩ := kpair_injective_l M code mx.1.1
    subst X₀ S₀
    obtain ⟨a, pair, ha⟩ := hg
    have ag := rd_entry_transitive_l trans hG ha
    have ij := pair.mem_l M trans ag.1
    have xz := rd_entry_transitive_l trans ag.2 hxz
    have yH := (vy.mem_l M trans (trans D hD v hv)).2
    exact ⟨i, ij.1, j, ij.2, x, xz.1, y, yH, a, ag.1, g, ag.2, z, xz.2,
      ux, vy, pair, ha, hxz, ((mx.2 y z).mp hyz).2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 下降见证排除任何传递返回锥

将已有下降链的带标号元素送入实际锥。交换律把逐边下降变成同一传递
目标中的隶属下降，因此既不要求原模型可数闭，也不重新构造游戏递归。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ladder_d.no_cone_l {ω α T Q G B H D f d N W P : M.Domain}
    (hw : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (branch : It_branch_d α T B)
    (members : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d I c X R)
    (ladder : It_ladder_d ω B Q G H D f) (target : Smem_d I d N W) :
    ¬ It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P := by
  intro cone
  obtain ⟨e, _, heω⟩ := hw.1.1
  obtain ⟨u, hu, _⟩ := ladder.1.2.1 e heω
  obtain ⟨i, hi, _⟩ := ladder.2.1 u hu
  obtain ⟨L, A, p, K, R, q, c, C, V, _, system, _, _, _⟩ := it_branch_data_l hZF hw diagram branch ⟨i, hi⟩
  have sub : M.MemberSubset D A := by
    intro u hu
    obtain ⟨i, hi, x, _, c, _, X, _, S, _, pair, hc, code, hx⟩ := ladder.2.1 u hu
    exact (system.tags.nodes u).mpr ⟨i, x, hi, pair, c, X, S, hc, code, hx⟩
  obtain ⟨r, rf, rs, _⟩ := (cone.realizer_l hZF hw).map_l hZF diagram branch.subset system
  obtain ⟨v, vf, vs⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) (ladder.1.mono_target_l sub)) (fn0_function_l (ZF.modelsKP hZF) rf)
  have read {u i x g y} (pair : KPair_d M u i x) (hg : Rd_entry_d i g P) (hy : Rd_entry_d u y r) : Rd_entry_d x y g := by
    obtain ⟨_, j, z, g', pair', hg', hzy⟩ := (rs u y).mp hy
    obtain ⟨eqi, eqx⟩ := kpair_injective_l M pair' pair
    subst j z
    exact cone.function.2 i g' g hg' hg ▸ hzy
  obtain ⟨S, wf, ss⟩ := wf_membership_l hZF N
  apply wf_no_desc_l hZF hw wf (fn0_of_function_l (ZF.modelsKP hZF) vf)
  intro n m a b succ hna hmb
  obtain ⟨_, u, hnu, hua⟩ := (vs n a).mp hna
  obtain ⟨_, v, hmv, hvb⟩ := (vs m b).mp hmb
  obtain ⟨i, _, j, _, x, _, y, _, k, _, g, _, z, _, ux, vy, pair, hg, hxz, hyz⟩ :=
    ladder.2.2 n m u v (ladder.1.bound_l hnu).1 (ladder.1.bound_l hmv).1
      (ladder.1.bound_l hnu).2 (ladder.1.bound_l hmv).2 succ hnu hmv
  have node {u i x} (hu : M.mem u D) (pair : KPair_d M u i x) : M.mem i B ∧ Ep_at_d Q i x := by
    obtain ⟨j, hj, y, _, c, _, X, _, R, _, pair', hc, code, hy⟩ := ladder.2.1 u hu
    obtain ⟨eqi, eqx⟩ := kpair_injective_l M pair' pair
    subst j y
    exact ⟨hj, c, X, R, hc, code, hy⟩
  have ni := node (ladder.1.bound_l hnu).2 ux
  have nj := node (ladder.1.bound_l hmv).2 vy
  obtain ⟨gi, hgi⟩ := (cone.domain i).mp ni.1
  obtain ⟨gj, hgj⟩ := (cone.domain j).mp nj.1
  obtain ⟨ci, _, _, hci, _, _⟩ := ni.2
  obtain ⟨cj, _, _, hcj, _, _⟩ := nj.2
  obtain ⟨Xi, Ri, mi⟩ := members i ci hci
  obtain ⟨Xj, Rj, mj⟩ := members j cj hcj
  have ei := cone.elementary i gi ci Xi Ri hgi hci mi.1
  have ej := cone.elementary j gj cj Xj Rj hgj hcj mj.1
  have edge : It_map_d G i j g := ⟨k, pair, hg⟩
  have old := diagram.elementary i j g ci Xi Ri cj Xj Rj edge hci hcj mi.1 mj.1
  obtain ⟨t, _, hzt⟩ := ej.1.1.2.2 z (old.1.1.output_mem_of_pairMember hxz)
  have eq := ei.1.1.1.2 x t a (cone.commute i j g gi gj edge hgi hgj x z t hxz hzt) (read ux hgi hua)
  have less := ((target.2 b t).mp ((ej.relation_l I hZF hw mj.1 target.1 (read vy hgj hvb) hzt).mp
    ((mj.2 y z).mpr ⟨ej.1.1.input_mem_of_pairMember (read vy hgj hvb), old.1.1.output_mem_of_pairMember hxz, hyz⟩))).2.2
  exact (ss b a).mpr ⟨vf.output_mem_of_pairMember hmb, vf.output_mem_of_pairMember hna, eq ▸ less⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 避开指定不良基枝的实际可数返回

同一壳包含完整树、指定下降见证和全部额外参数。Δ₀ 下降证书沿壳回拉，
因此含 padding 的返回定理所得分支必不同于原指定分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_hull_return_d (hZF : M.Models ZF) (ω o c X T Q G E L B b : M.Domain)
    {n} (v : Fin n → M.Domain) : Prop :=
  ∃ A Rₐ a K U Rᵤ u J π c₀ X₀ R₀ π₀ Q₀ G₀ E₀ L₀,
    Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K A Rₐ ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J U Rᵤ ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) a A Rₐ ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) u U Rᵤ ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω a u A U π ∧ M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) A ω ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) c₀ X₀ R₀ ∧ M.TransitiveSet X₀ ∧ Rd_entry_d c₀ c π ∧ Rd_entry_d X₀ X π ∧
    M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) π₀ π X₀ ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c₀ c X₀ X π₀ ∧
    It_pnice_d hZF ω c₀ ω T Q₀ G₀ E₀ L₀ ∧
    (∀ i d, Rd_entry_d i d Q₀ → It_mem_d (kp_pair_l (ZF.modelsKP hZF)) d) ∧
    Rd_entry_d Q₀ Q π ∧ Rd_entry_d G₀ G π ∧ Rd_entry_d E₀ E π ∧ Rd_entry_d L₀ L π ∧
    It_return_at_d hZF ω o T Q₀ G₀ c X π₀ b ∧ b ≠ B ∧
    ∀ i, ∃ x, M.mem x A ∧ Rd_entry_d x (v i) π

theorem It_hull_return_d.branch_l (hZF : M.Models ZF) {ω o c X T Q G E L B b : M.Domain}
    {n} {v : Fin n → M.Domain} (h : It_hull_return_d hZF ω o c X T Q G E L B b v) :
    It_branch_d ω T b ∧ b ≠ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ret, ne, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, branch, _⟩ := ret
  exact ⟨branch, ne⟩

theorem it_hull_return_l (hZFC : M.Models ZFC) {ω o c X R θ T Q G E L B : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (models : ∀ i d, Rd_entry_d i d Q → It_mem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X)
    (ho : ∀ x, ¬ M.mem x o) (bad : It_ill_branch_d (ZFC.models_zf_l hZFC) ω ω T Q G B)
    {n} (v : Fin n → M.Domain) : ∃ b, It_hull_return_d (ZFC.models_zf_l hZFC) ω o c X T Q G E L B b v := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hw := nice.tree.omega
  have actual i d (hd : Rd_entry_d i d Q) := (nice.tree.sources i d hd).mem_l hZF
    (models i d hd)
  have members i d (hd : Rd_entry_d i d Q) : ∃ Y S, Smem_d I d Y S := by
    obtain ⟨Y, S, _, my, _⟩ := actual i d hd
    exact ⟨Y, S, my⟩
  obtain ⟨H, D, f, ladder⟩ := bad.ladder_l hZF (ZFC.dc_l I hZFC hw) members
  let w : Fin (n+7) → M.Domain := Fin.cases c (Fin.cases E (Fin.cases L (Fin.cases H
    (Fin.cases D (Fin.cases f (Fin.cases B v))))))
  obtain ⟨A, Rₐ, a, K, U, Rᵤ, u, J, C, V, π, Q₀, G₀, sa, su, ma, mu, hj, count, hC, fs, vt, hCV,
    _, hQ, hG, hTT, hQQ, hGG, diagram, _, reflect, params⟩ :=
    it_diagram_hull_l hZFC hw nice.tree.diagram nice.tree.sources w
  obtain ⟨c₀, _, hcc⟩ := params 0
  obtain ⟨E₀, he, hEE⟩ := params 1
  obtain ⟨L₀, hl, hLL⟩ := params 2
  obtain ⟨H₀, _, hHH⟩ := params 3
  obtain ⟨D₀, _, hDD⟩ := params 4
  obtain ⟨f₀, _, hff⟩ := params 5
  obtain ⟨B₀, _, hBB⟩ := params 6
  have omega := hj.omega_l I hZF hw sa.transitive su.transitive ma mu sa.omega_mem
  have natural := hj.natural_l hZF hw sa.transitive su.transitive ma mu sa.omega_mem
  have sub := (hj.subset_l hZF hw sa.transitive su.transitive ma mu hBB omega).mpr bad.1.subset
  have fixed := hj.fixed_subset_l hZF hw sa.transitive su.transitive ma mu omega natural
    (hj.1.1.input_mem_of_pairMember hBB) sub
  have eq := hj.1.1.1.2 B₀ B₀ B fixed hBB
  subst B₀
  have tr := smap_delta_l I hZF hw sa.transitive su.transitive ma mu hj
    (it_ladder_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (it_ladder_delta_l ..)
    ⟨Fin.cases f₀ (Fin.cases D₀ (Fin.cases H₀ (Fin.cases G₀ (Fin.cases Q₀ (Fin.cases B (fun _ => ω)))))), fun _ => ω⟩
    ⟨Fin.cases f (Fin.cases D (Fin.cases H (Fin.cases G (Fin.cases Q (Fin.cases B (fun _ => ω)))))), fun _ => ω⟩
    (Fin.cases hff (Fin.cases hDD (Fin.cases hHH (Fin.cases hGG (Fin.cases hQQ (Fin.cases hBB (fun _ => omega)))))))
  have ladder₀ : It_ladder_d ω B Q₀ G₀ H₀ D₀ f₀ := (it_ladder_sat_l (ZF.modelsKP hZF) _ ..).mp
    (tr.mpr ((it_ladder_sat_l (ZF.modelsKP hZF) _ ..).mpr ladder))
  obtain ⟨X', R', K', mx', source⟩ := actual o c (nice.tree.root o ho)
  obtain ⟨eqX, eqR⟩ := smdl_unique_l I mx'.1 mx.1
  subst X' R'
  -- 根源的配对闭性排除后继高度，无需在接口中另加高度假设。
  have limit : M.IsLimitOrdinal θ := by
    refine ⟨v_ordinal_l I rank, ⟨ω, ZF.v_ordinal_height_l hZF rank (hw.isOrdinal (ZF.modelsKP hZF)) source.omega_mem⟩, ?_⟩
    intro β hβ
    have hβX := ZF.v_ordinal_mem_l I hZF rank hβ
    obtain ⟨p, hp, pair⟩ := (source.algebra_l (ZF.modelsKP hZF)).pair β β hβX hβX
    obtain ⟨γ, W, hγ, vw, sub⟩ := (ZF.v_unfold_l I hZF rank p).mp hp
    exact ⟨γ, hγ, ZF.v_ordinal_height_l hZF vw ((v_ordinal_l I rank).mem hβ)
      (sub β ((pair β).mpr (Or.inl rfl)))⟩
  have powers i d Y S (hd : Rd_entry_d i d Q) (my : Smem_d I d Y S) : Sc_power_d Y := by
    obtain ⟨Y', S', _, my', sy⟩ := actual i d hd
    obtain ⟨eqY, eqS⟩ := smdl_unique_l I my'.1 my.1
    subst Y' S'
    obtain ⟨j, hj⟩ := nice.tree.diagram.map_l hZF (nice.tree.diagram.order.root_l hZF ho i
      ((nice.tree.diagram.model_domain i).mpr ⟨d, hd⟩))
    exact (sc_power_iff_l hZF hw source.transitive sy.transitive mx my
      (nice.tree.diagram.elementary o i j c X R d Y S hj (nice.tree.root o ho) hd mx.1 my.1)).mp
        (sc_v_power_l (ZF.modelsKP hZF) limit rank)
  have small := it_pnice_pull_l hZFC sa su ma mu hj hC fs vt hCV hQ hG he hl
    hcc hTT hQQ hGG hEE hLL diagram nice models powers reflect
  have smallModels i d (hd : Rd_entry_d i d Q₀) : It_mem_d I d := by
    have hi := (small.tree.diagram.model_domain i).mpr ⟨d,hd⟩
    have hdA := (rd_entry_transitive_l sa.transitive (hj.1.1.input_mem_of_pairMember hQQ) hd).2
    obtain ⟨d',_,hdd⟩ := hj.1.1.2.2 d hdA
    have hd' := (hj.entry_l hZF hw sa.transitive su.transitive ma mu (natural i hi) hdd hQQ).mp hd
    obtain ⟨Y,S,_,my,sy⟩ := actual i d' hd'
    obtain ⟨Y₀,S₀,_,_,my₀,sy₀,_⟩ := ep_set_source_pull_l hZF sa su ma mu hj hdd my sy
    exact ⟨Y₀,S₀,my₀,sy₀.transitive⟩
  obtain ⟨X₀, R₀, _, π₀, mx₀, sx, hXX, restrict, emb⟩ := ep_set_source_pull_l hZF sa su ma mu hj hcc mx source
  obtain ⟨e, injection⟩ := count
  obtain ⟨e₀, er⟩ := ZF.exists_restriction hZF I e X₀
  have cx : M.CardinalLessOrEqual I X₀ ω := ⟨e₀, er.isSetFunctionFromTo injection.1
    (sa.transitive X₀ (hj.1.1.input_mem_of_pairMember hXX)),
    fun x y z hx hy => injection.2 x y z ((er.2 x z).mp hx).2 ((er.2 y z).mp hy).2⟩
  obtain ⟨b, returned⟩ := it_copyable_return_l hZFC small.tree (small.copyable_l hZFC) mx₀ sx.transitive cx ho rank mx emb
  have ne : b ≠ B := by
    intro eq
    subst b
    obtain ⟨_, _, _, _, _, _, d, N, W, P, _, branch, _, _, target, cone, _, _⟩ := returned
    exact ladder₀.no_cone_l hZF hw diagram bad.1
      (fun i c hc => (smallModels i c hc).elim fun X h =>
          h.elim fun R h => ⟨X, R, h.1⟩)
      target cone.toIt_embedding_d
  exact ⟨b, A, Rₐ, a, K, U, Rᵤ, u, J, π, c₀, X₀, R₀, π₀, Q₀, G₀, E₀, L₀,
    sa, su, ma, mu, hj, ⟨e, injection⟩, mx₀, sx.transitive, hcc, hXX, restrict, emb, small, smallModels, hQQ, hGG, hEE, hLL, returned, ne,
    fun i => by
      obtain ⟨x, hx, image⟩ := params i.succ.succ.succ.succ.succ.succ.succ
      exact ⟨x, sa.transitive C hC x hx, image⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
