import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptImage
import YesMetaZFC.Model.SetTheory.Internal.SourceFinitePartial

/-! # 联合有限尝试的实际拥有性

每行是内部有限列；前驱定义域是有限序数内的源内分离集。原行图由有限
部分图闭性回收，因此像中的节点判定可用于背景实际构造的全部联合尝试。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_node_d.member_l {ω κ K Z S T Q G E Y W z π k P : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hT : M.mem T Z) (hY : M.MemberSubset Y Z)
    (diagram : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (node : Ja_node_d I ω T Q G E Y W z π k P) : M.mem P Z := by
  have hk := source.transitive ω source.omega_mem k node.length
  obtain ⟨m, hs, hm⟩ := source.omega.1.2 k node.length
  let ρ : Env M 2 := ⟨Fin.cases k (fun _ => T), fun _ => k⟩
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨c, code⟩ := source.code
  obtain ⟨D, hD, ds⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (rd_entry0_delta_l ..) ρ (Fin.cases hk (fun _ => hT)) (source.transitive ω source.omega_mem m hm)
  have dom i : M.mem i D ↔ Rd_entry_d i k T := by
    have spec : M.mem i D ↔ M.mem i m ∧ Rd_entry_d i k T :=
      (ds i).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
    exact spec.trans ⟨And.right, fun hi => ⟨(hs i).mpr ((diagram.order.forward i k hi).elim
      (fun e => Or.inr (e ▸ fun _ => Iff.rfl)) Or.inl), hi⟩⟩
  have fn : M.IsSetFunctionFromTo I P D Z := ⟨node.function,
    fun i => (dom i).trans (node.domain i).symm, fun i hi => by
      obtain ⟨p, hp⟩ := (node.domain i).mpr ((dom i).mp hi)
      obtain ⟨a, A, R, ha, ma⟩ := diagram.model_l hZF (diagram.order.bound i k ((dom i).mp hi)).1
      obtain ⟨e, he⟩ := (en.domain i).mp (diagram.order.bound i k ((dom i).mp hi)).1
      exact ⟨p, sc_finite_function_l hZF source.omega source.transitive source.theory.algebra.pair source.theory.algebra.union source.omega_mem
        hY node.length (node.rows i p a A R e hp ha ma.1 he).1, hp⟩⟩
  exact sc_finite_partial_l hZF source.omega source.transitive code source.theory source.omega_mem hD hm
    (fun i hi => ((ds i).mp hi).1) (fn0_of_function_l (ZF.modelsKP hZF) fn)

theorem Ja_cell_d.member_l {ω κ K Z S T Q G E Y W z π s : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hT : M.mem T Z) (hY : M.MemberSubset Y Z)
    (diagram : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (cell : Ja_cell_d I ω T Q G E Y W z π s) : M.mem s Z := by
  obtain ⟨k, P, pair, node⟩ := cell
  obtain ⟨t, ht, hp⟩ := source.kpair_l hZF (source.transitive ω source.omega_mem k node.length)
    (node.member_l hZF source hT hY diagram en)
  exact kpair_unique_l M hZF.1 hp pair ▸ ht

/-- 像参数仍给出同一类枚举树时，像集合就是全部背景联合节点及其原扩展关系。 -/
theorem Ja_space_d.full_image_l {ω κ K X R μ K' Y S c d j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ρ η : Env M 11) (hw : ρ.bound 0 = ω) (images : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j)
    (space : Ja_space_d I ω (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)
      (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10))
    (diagram : It_diagram_d hZF ω ω (η.bound 1) (η.bound 2) (η.bound 3))
    (en : Ja_enum_d I ω ω (η.bound 2) (η.bound 4)) :
    Ja_space_d I ω (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4)
      (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) (η.bound 9) (η.bound 10) := by
  obtain ⟨nodes, edges⟩ := space.image_l hZF source target hm hn hj ρ η hw images
  have owned i := hj.1.1.output_mem_of_pairMember (images i)
  have nodes s : M.mem s (η.bound 9) ↔ Ja_cell_d I ω (η.bound 1) (η.bound 2) (η.bound 3)
      (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) s :=
    ⟨fun hs => (nodes s (target.transitive _ (owned 9) s hs)).mp hs,
      fun hs => (nodes s (hs.member_l hZF target (owned 1) (target.transitive _ (owned 5)) diagram en)).mpr hs⟩
  let φ : Formula 1 2 := Formula.forallMem (.bound 1) (Formula.existsMem (.bound 1)
    (Formula.existsMem (.bound 2) (kpair0_m (.bound 2) .newest (.bound 1))))
  have read (θ : Env M 2) : Formula.satisfies θ φ ↔ ∀ p, M.mem p (θ.bound 1) →
      ∃ s, M.mem s (θ.bound 0) ∧ ∃ t, M.mem t (θ.bound 0) ∧ KPair_d M p t s := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  let a (θ : Env M 11) : Env M 2 := ⟨Fin.cases (θ.bound 9) (fun _ => θ.bound 10), fun _ => ω⟩
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj φ
    (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) (a ρ) (a η)
    (Fin.cases (images 9) (fun _ => images 10))
  have pairs := (read (a η)).mp (tr.mp ((read (a ρ)).mpr (fun p hp => by
    obtain ⟨t, s, pair⟩ := space.relation p hp
    have edge := (space.edges s t).mp ⟨p, pair, hp⟩
    exact ⟨s, edge.1, t, edge.2.1, pair⟩)))
  refine ⟨nodes, fun p hp => ?_, fun s t => ⟨?_, ?_⟩⟩
  · obtain ⟨s, _, t, _, pair⟩ := pairs p hp
    exact ⟨t, s, pair⟩
  · intro h
    have ts := rd_entry_transitive_l target.transitive (owned 10) h
    exact (edges s t ts.2 ts.1).mp h
  · intro h
    exact (edges s t (target.transitive _ (owned 9) s h.1) (target.transitive _ (owned 9) t h.2.1)).mpr h

end YesMetaZFC.SetTheory.LargeCardinal
