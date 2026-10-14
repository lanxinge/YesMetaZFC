import YesMetaZFC.SetTheory.LargeCardinal.IterationLadder
import YesMetaZFC.SetTheory.LargeCardinal.IterationRealizer

/-! # 下降见证排除任何传递返回锥

将已有下降链的带标号元素送入实际锥。交换律把逐边下降变成同一传递
目标中的隶属下降，因此既不要求原模型可数闭，也不重新构造游戏递归。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ladder_d.no_cone_l {ω α T Q G B H D f d N W P : M.Domain}
    (hw : M.IsOmega ω) (diagram : It_diagram_d hZF ω α T Q G) (branch : It_branch_d α T B)
    (members : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d I c X R)
    (ladder : It_ladder_d ω B Q G H D f) (target : Smem_d I d N W) :
    ¬ It_embedding_d hZF ω B Q G d N W P := by
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
