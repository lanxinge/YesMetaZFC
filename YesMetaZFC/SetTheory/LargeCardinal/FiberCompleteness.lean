import YesMetaZFC.SetTheory.LargeCardinal.MeasureFamily

/-! # 派生扩展器所需的共同纤维可数完备性

第 n 层只含长度 n 的内部有限列。各层之并保留共同纤维；回拉并集上的分支后，
函数定义域的唯一性把每个前缀精确归还到原第 n 层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ef_levels_d (ω D H : M.Domain) : Prop := (∃ P, Fn0_d ω P H) ∧
  ∀ n A, Rd_entry_d n A H → ∀ s, M.mem s A → Fn0_d n D s

def Ef_fiber_d (ω D H f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ A s, Rd_entry_d n A H ∧ M.mem s A ∧ Fn0_d n D s ∧ M.MemberSubset s f

def Ef_image_fiber_d (j ω D H f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ A A' s, Rd_entry_d n A H ∧ M.PairMember I A A' j ∧ M.mem s A' ∧ Fn0_d n D s ∧ M.MemberSubset s f

def ef_levels_m {d} (ω D H : Term d) : Formula 1 d :=
  .conj (.existsE (fn0_m ω.weaken .newest H.weaken)) (.forallE (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest H.weaken.weaken)
      (Formula.forallMem .newest (fn0_m (.bound 2) D.weaken.weaken.weaken .newest)))))
derive_free_closed ef_levels_m

def ef_fiber_m {d} (ω D H f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
      (.conj (fn0_m (.bound 2) D.weaken.weaken.weaken .newest) (Formula.subset .newest f.weaken.weaken.weaken)))))))
derive_free_closed ef_fiber_m

def ef_image_fiber_m {d} (j ω D H f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (.existsE (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) j.weaken.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
        (.conj (fn0_m (.bound 3) D.weaken.weaken.weaken.weaken .newest)
          (Formula.subset .newest f.weaken.weaken.weaken.weaken)))))))))
derive_free_closed ef_image_fiber_m

theorem ef_levels_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D H : Term d) :
    Formula.satisfies ρ (ef_levels_m ω D H) ↔ Ef_levels_d (ω.eval ρ) (D.eval ρ) (H.eval ρ) := by
  simp only [ef_levels_m, Ef_levels_d, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    fn0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hE,
    Formula.satisfies_forallMem_iff, Definitional.Term.eval_weaken]
  rfl

theorem ef_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D H f : Term d) :
    Formula.satisfies ρ (ef_fiber_m ω D H f) ↔ Ef_fiber_d (ω.eval ρ) (D.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ef_fiber_m, Ef_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem ef_image_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j ω D H f : Term d) :
    Formula.satisfies ρ (ef_image_fiber_m (𝒞 := 𝒞) j ω D H f) ↔
      Ef_image_fiber_d I (j.eval ρ) (ω.eval ρ) (D.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ef_image_fiber_m, Ef_image_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

/-- 共同纤维回拉给出整个层族的可数完备性，强于逐个测度的可数完备性。 -/
theorem ef_common_fiber_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L G H f}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hLk : M.MemberSubset L k) (hG : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G ω L)
    (hGY : M.mem G Y) (hH : Ef_levels_d ω κ H) (hf : Ef_image_fiber_d I j ω L H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  have ht := ZF.v_transitive_l I hZF hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨P, hHP⟩ := hH.1
  have hFn := fn0_function_l (ZF.modelsKP hZF) hHP
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF (kp_pair_l (ZF.modelsKP hZF)) hFn.1 hFn.2.1
  obtain ⟨T, hT⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have spec s : M.mem s T ↔ ∃ n A, Rd_entry_d n A H ∧ M.mem s A := by
    rw [hT s]
    exact ⟨fun ⟨A, hA, hs⟩ => ((hR A).mp hA).elim fun n hn => ⟨n, A, hn, hs⟩,
      fun ⟨n, A, hn, hs⟩ => ⟨A, (hR A).mpr ⟨n, hn⟩, hs⟩⟩
  have hTX : M.mem T X := ZF.v_relations_mem_l I hZF hX hδ hc.source (fun s hs p hp => by
    obtain ⟨n, A, hn, hsA⟩ := (spec s).mp hs
    obtain ⟨i, hi, a, ha, hp⟩ := (hH.2 n A hn s hsA).1 p hp
    exact ⟨i, hc.ordinal.transitive ω hωκ i (hω.transitive hZF n (hHP.bound_l hn).1 i hi), a, ha, hp⟩)
  obtain ⟨T', _, hjT⟩ := hj.2.2 T hTX
  have branch : Eb_d ω L T' f := by
    refine ⟨hf.1, fun n hn => ?_⟩
    obtain ⟨A, A', s, hA, hjA, hs, hsFn, hsf⟩ := hf.2 n hn
    have sub : M.MemberSubset A T := fun t ht => (spec t).mpr ⟨n, A, hA, ht⟩
    exact ⟨s, (ed_subset_l I hZF hω h ht hY hjA hjT).mp sub s hs, hsFn, hsf⟩
  obtain ⟨g, hgX, hg⟩ := ed_branch_pull_l I hZF hω h ht hY (hc.fixed ω hωκ) hc.image hjT
    (hY G hGY f ((hG f).mpr (fn0_function_l (ZF.modelsKP hZF) hf.1))) (eb_mono_l hLk branch)
  refine ⟨g, hgX, hg.1, fun n hn => ?_⟩
  obtain ⟨s, hs, hsFn, hsg⟩ := hg.2 n hn
  obtain ⟨m, A, hmA, hsA⟩ := (spec s).mp hs
  have eq := hsFn.domain_eq_l hZF.1 (hH.2 m A hmA s hsA)
  exact ⟨A, s, eq.symm ▸ hmA, hsA, hsFn, hsg⟩

end YesMetaZFC.SetTheory.LargeCardinal
