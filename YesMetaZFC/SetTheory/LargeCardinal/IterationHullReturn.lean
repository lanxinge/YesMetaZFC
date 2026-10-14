import YesMetaZFC.SetTheory.LargeCardinal.IterationNiceReturn
import YesMetaZFC.SetTheory.LargeCardinal.IterationLadderCone

/-! # 避开指定不良基枝的实际可数返回

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
    Ep_source_d hZF ω ω K A Rₐ ∧ Ep_source_d hZF ω ω J U Rᵤ ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) a A Rₐ ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) u U Rᵤ ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω a u A U π ∧ M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) A ω ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) c₀ X₀ R₀ ∧ Rd_entry_d c₀ c π ∧ Rd_entry_d X₀ X π ∧
    M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) π₀ π X₀ ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c₀ c X₀ X π₀ ∧
    It_pnice_d hZF ω c₀ ω T Q₀ G₀ E₀ L₀ ∧
    Rd_entry_d Q₀ Q π ∧ Rd_entry_d G₀ G π ∧ Rd_entry_d E₀ E π ∧ Rd_entry_d L₀ L π ∧
    It_return_at_d hZF ω o T Q₀ G₀ c X π₀ b ∧ b ≠ B ∧
    ∀ i, ∃ x, M.mem x A ∧ Rd_entry_d x (v i) π

theorem It_hull_return_d.branch_l (hZF : M.Models ZF) {ω o c X T Q G E L B b : M.Domain}
    {n} {v : Fin n → M.Domain} (h : It_hull_return_d hZF ω o c X T Q G E L B b v) :
    It_branch_d ω T b ∧ b ≠ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ret, ne, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, branch, _⟩ := ret
  exact ⟨branch, ne⟩

theorem it_hull_return_l (hZFC : M.Models ZFC) {ω o c X R θ T Q G E L B : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X)
    (ho : ∀ x, ¬ M.mem x o) (bad : It_ill_branch_d (ZFC.models_zf_l hZFC) ω ω T Q G B)
    {n} (v : Fin n → M.Domain) : ∃ b, It_hull_return_d (ZFC.models_zf_l hZFC) ω o c X T Q G E L B b v := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hw := nice.tree.omega
  have members i d (hd : Rd_entry_d i d Q) : ∃ Y S, Smem_d I d Y S := (nice.tree.sources i d hd).elim fun Y h =>
    h.elim fun S h => h.elim fun _ h => ⟨Y, S, h.1⟩
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
  obtain ⟨X', R', K', mx', source⟩ := nice.tree.sources o c (nice.tree.root o ho)
  obtain ⟨eqX, eqR⟩ := smdl_unique_l I mx'.1 mx.1
  subst X' R'
  -- 根源的配对闭性排除后继高度，无需在接口中另加高度假设。
  have limit : M.IsLimitOrdinal θ := by
    refine ⟨v_ordinal_l I rank, ⟨ω, ZF.v_ordinal_height_l hZF rank (hw.isOrdinal hZF) source.omega_mem⟩, ?_⟩
    intro β hβ
    have hβX := ZF.v_ordinal_mem_l I hZF rank hβ
    obtain ⟨p, hp, pair⟩ := source.theory.algebra.pair β β hβX hβX
    obtain ⟨γ, W, hγ, vw, sub⟩ := (ZF.v_unfold_l I hZF rank p).mp hp
    exact ⟨γ, hγ, ZF.v_ordinal_height_l hZF vw ((v_ordinal_l I rank).mem hβ)
      (sub β ((pair β).mpr (Or.inl rfl)))⟩
  have powers i d Y S (hd : Rd_entry_d i d Q) (my : Smem_d I d Y S) : Sc_power_d Y := by
    obtain ⟨Y', S', _, my', sy⟩ := nice.tree.sources i d hd
    obtain ⟨eqY, eqS⟩ := smdl_unique_l I my'.1 my.1
    subst Y' S'
    obtain ⟨j, hj⟩ := nice.tree.diagram.map_l hZF (nice.tree.diagram.order.root_l hZF ho i
      ((nice.tree.diagram.model_domain i).mpr ⟨d, hd⟩))
    exact (sc_power_iff_l hZF hw source.transitive sy.transitive mx my
      (nice.tree.diagram.elementary o i j c X R d Y S hj (nice.tree.root o ho) hd mx.1 my.1)).mp
        (sc_v_power_l hZF limit rank)
  have small := it_pnice_pull_l hZFC sa su ma mu hj hC fs vt hCV hQ hG he hl
    hcc hTT hQQ hGG hEE hLL diagram nice powers reflect
  obtain ⟨X₀, R₀, _, π₀, mx₀, _, hXX, restrict, emb⟩ := ep_set_source_pull_l hZF sa su ma mu hj hcc mx source
  obtain ⟨e, injection⟩ := count
  obtain ⟨e₀, er⟩ := ZF.exists_restriction hZF I e X₀
  have cx : M.CardinalLessOrEqual I X₀ ω := ⟨e₀, er.isSetFunctionFromTo injection.1
    (sa.transitive X₀ (hj.1.1.input_mem_of_pairMember hXX)),
    fun x y z hx hy => injection.2 x y z ((er.2 x z).mp hx).2 ((er.2 y z).mp hy).2⟩
  obtain ⟨b, returned⟩ := it_pnice_return_l hZFC small mx₀ cx ho rank mx emb
  have ne : b ≠ B := by
    intro eq
    subst b
    obtain ⟨_, _, _, _, _, _, d, N, W, P, _, branch, _, _, target, cone, _⟩ := returned
    exact ladder₀.no_cone_l hZF hw diagram bad.1
      (fun i c hc => (small.tree.sources i c hc).elim fun X h => h.elim fun R h => h.elim fun _ h => ⟨X, R, h.1⟩)
      target cone.toIt_embedding_d
  exact ⟨b, A, Rₐ, a, K, U, Rᵤ, u, J, π, c₀, X₀, R₀, π₀, Q₀, G₀, E₀, L₀,
    sa, su, ma, mu, hj, ⟨e, injection⟩, mx₀, hcc, hXX, restrict, emb, small, hQQ, hGG, hEE, hLL, returned, ne,
    fun i => by
      obtain ⟨x, hx, image⟩ := params i.succ.succ.succ.succ.succ.succ.succ
      exact ⟨x, sa.transitive C hC x hx, image⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
