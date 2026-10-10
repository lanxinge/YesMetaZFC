import YesMetaZFC.SetTheory.Descriptive.RealArray

/-! # 实数行列的内部编码与常行对角映射 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem array_encode_l (hZF : M.Models ZF) {ω B J D H} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hD : M.MemberSubset D ω) (hH : M.IsSetFunctionFromTo I H D B) :
    ∃ w, M.mem w B ∧ ∀ i x, M.PairMember I i x H → Row_d I J i w x := by
  classical
  obtain ⟨z, _, hz⟩ := hB.1.1.1
  let ρ : Env M 4 := (((⟨fun _ => J, fun _ => J⟩ : Env M 1).push D).push H).push z
  let φ : BinarySchema 4 := { body := .existsE (.existsE (.conj
    (np_m (𝒞 := 𝒞) (.bound 7) (.bound 1) .newest (.bound 3)) (.disj
    (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 6))
      (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) .newest)))
    (.conj (.neg (.mem (.bound 1) (.bound 6))) (Formula.extensionalEq (.bound 2) (.bound 4)))))) }
  have hp k v : φ.denote ρ k v ↔ ∃ i j, Np_d I J i j k ∧
      ((∃ x, M.PairMember I i x H ∧ M.PairMember I j v x) ∨ (¬ M.mem i D ∧ v = z)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, np_sat_l I, Formula.satisfies_disj_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨w, hw, ew⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (by
      intro k hk
      obtain ⟨i, j, _, hj, hij⟩ := np_surj_l I hJ hk
      by_cases hi : M.mem i D
      · obtain ⟨x, hx, hix⟩ := hH.2.2 i hi
        obtain ⟨v, _, hjv⟩ := ((hB.2 x).mp hx).2.2 j hj
        exact ⟨v, (hp k v).mpr ⟨i, j, hij, Or.inl ⟨x, hix, hjv⟩⟩⟩
      · exact ⟨z, (hp k z).mpr ⟨i, j, hij, Or.inr ⟨hi, rfl⟩⟩⟩)
    (by
      intro k _ v u hv hu
      obtain ⟨i, j, hij, hv⟩ := (hp k v).mp hv
      obtain ⟨i', j', hij', hu⟩ := (hp k u).mp hu
      obtain ⟨ei, ej⟩ := np_injective_l I hJ hij' hij
      subst i' j'
      rcases hv with ⟨x, hx, hjv⟩ | ⟨hi, rfl⟩ <;> rcases hu with ⟨y, hy, hju⟩ | ⟨hi', rfl⟩
      · exact ((hB.2 x).mp (hH.output_mem_of_pairMember hx)).1.2 j v u hjv (hH.1.2 i y x hy hx ▸ hju)
      · exact (hi' (hH.input_mem_of_pairMember hx)).elim
      · exact (hi (hH.input_mem_of_pairMember hy)).elim
      · rfl)
    (by
      intro k v _ hv
      obtain ⟨i, j, _, hv⟩ := (hp k v).mp hv
      exact hv.elim (fun ⟨x, hx, hjv⟩ => ((hB.2 x).mp (hH.output_mem_of_pairMember hx)).output_mem_of_pairMember hjv)
        (fun h => h.2.symm ▸ hz))
  refine ⟨w, (hB.2 w).mpr hw, fun i x hix => ⟨((hB.2 x).mp (hH.output_mem_of_pairMember hix)).1.1, fun j v => ⟨?_, ?_⟩⟩⟩
  · intro hjv
    obtain ⟨k, hk, hik⟩ := np_total_l I hJ (hD i (hH.input_mem_of_pairMember hix))
      (((hB.2 x).mp (hH.output_mem_of_pairMember hix)).input_mem_of_pairMember hjv)
    exact ⟨k, hik, (ew k v).mpr ⟨hk, (hp k v).mpr ⟨i, j, hik, Or.inl ⟨x, hix, hjv⟩⟩⟩⟩
  · rintro ⟨k, hik, hkv⟩
    obtain ⟨i', j', hij', hv⟩ := (hp k v).mp ((ew k v).mp hkv).2
    obtain ⟨ei, ej⟩ := np_injective_l I hJ hij' hik
    subst i' j'
    exact hv.elim (fun ⟨y, hiy, hjv⟩ => hH.1.2 i y x hiy hix ▸ hjv)
      (fun h => (h.1 (hH.input_mem_of_pairMember hix)).elim)

/-- 常行对角 x↦(x,x,…) 是实际连续函数，无需选择公理。 -/
theorem array_diag_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ x w, M.PairMember I x w f → ∀ i, M.mem i ω → Row_d I J i w x := by
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := { body := .existsE (np_m (𝒞 := 𝒞) (.bound 3) .newest (.bound 1) (.bound 2)) }
  have hp k j : φ.denote ρ k j ↔ ∃ i, Np_d I J i j k := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, np_sat_l I]; rfl
  obtain ⟨E, he, ee⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun k hk => (np_surj_l I hJ hk).elim fun i h => h.elim fun j h => ⟨j, (hp k j).mpr ⟨i, h.2.2⟩⟩)
    (fun _ _ _ _ h k => ((hp _ _).mp h).elim fun _ h => ((hp _ _).mp k).elim fun _ k => (np_injective_l I hJ h k).2)
    (fun _ _ _ h => ((hp _ _).mp h).elim fun _ h => (np_type_l I hJ h).2.1)
  obtain ⟨f, hf⟩ := rg_exists_l I hZF hB he
  refine ⟨f, rg_cont_l I hZF hB hA he hf, fun x w hxw i hi => ?_⟩
  have hx := (hB.2 x).mp (hf.1.input_mem_of_pairMember hxw)
  have hr := ((hf.2 x w).mp hxw).2
  refine ⟨hx.1.1, fun j v => ⟨?_, ?_⟩⟩
  · intro hjv
    obtain ⟨k, hk, hik⟩ := np_total_l I hJ hi (hx.input_mem_of_pairMember hjv)
    exact ⟨k, hik, (hr.2 k v).mpr ⟨j, (ee k j).mpr ⟨hk, (hp k j).mpr ⟨i, hik⟩⟩, hjv⟩⟩
  · rintro ⟨k, hik, hkv⟩
    obtain ⟨j', hkj, hjv⟩ := (hr.2 k v).mp hkv
    obtain ⟨i', hij'⟩ := (hp k j').mp ((ee k j').mp hkj).2
    exact (np_injective_l I hJ hij' hik).2 ▸ hjv

theorem row_mem_l (hZF : M.Models ZF) {ω B J i w x} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hi : M.mem i ω) (hw : M.mem w B) (h : Row_d I J i w x) : M.mem x B := by
  obtain ⟨y, hy, hr⟩ := row_exists_l I hZF hJ hi ((hB.2 w).mp hw)
  exact row_unique_l I hZF.1 hr h ▸ (hB.2 y).mpr hy

theorem row_surj_l (hZF : M.Models ZF) {ω B J x} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hx : M.mem x B) : ∃ w, M.mem w B ∧ ∀ i, M.mem i ω → Row_d I J i w x := by
  obtain ⟨H, hH, eh⟩ := ZF.exists_constantFunction hZF I (source := ω) hx
  obtain ⟨w, hw, hr⟩ := array_encode_l I hZF hB hJ (fun _ => id) hH
  exact ⟨w, hw, fun i hi => hr i x ((eh i x).mpr ⟨hi, rfl⟩)⟩

end YesMetaZFC.SetTheory.Descriptive
