import YesMetaZFC.SetTheory.FinitaryHullStep

/-! # 模型内部的最小有限元闭包

在 P(X) 上迭代一步闭包，再取内部 ω 链之并。有限参数截取给出闭性，另一轮
实际公式归纳给出最小性。本层只需 ZF，供实际司寇伦选择图的闭包装配调用。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ZF.fc_hull_chain_l (hZF : M.Models ZF) {ω X T D K A} (hω : M.IsOmega ω)
    (hK : M.IsSetFunctionFromTo I K D X) (hA : M.MemberSubset A X) : ∃ P Q N,
    M.IsPowerSetOf P X ∧ M.IsSetFunctionFromTo I Q ω P ∧
      (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e A Q) ∧
      (∀ i j B C, M.SuccessorOf j i → M.PairMember I i B Q → M.PairMember I j C Q → Fc_step_d I ω T K B C) ∧
      Cc_union_d I Q N ∧ Fc_hull_d I ω X T K A N := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push T).push K
  let φ : BinarySchema 3 := { body := fc_step_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ B C : φ.denote ρ B C ↔ Fc_step_d I ω T K B C := fc_step_sat_l I hZF.1 _ _ _ _ _ _
  obtain ⟨G, hG, hg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := P)
    (fun B hB => (ZF.fc_step_exists_l I hZF hK ((hP B).mp hB)).elim fun C hC => ⟨C, (hφ B C).mpr hC.1⟩)
    (fun B _ C E hC hE => hZF.1.eq_of_same_members C E (fun x => ((hφ B C).mp hC x).trans ((hφ B E).mp hE x).symm))
    (fun B C hB hC => (hP C).mpr (fun x hx => (((hφ B C).mp hC x).mp hx).elim
      ((hP B).mp hB x) (fun ⟨_, _, _, _, _, _, _, _, hx⟩ => hK.output_mem_of_pairMember hx)))
  obtain ⟨Q, hQ, hz, hs⟩ := ZFC.iterate_l I hZF hω hG ((hP A).mpr hA)
  have step i j B C (hij : M.SuccessorOf j i) (hi : M.PairMember I i B Q) (hj : M.PairMember I j C Q) :
      Fc_step_d I ω T K B C := (hφ B C).mp ((hg B C).mp (hs i j B C hij hi hj)).2
  have mono := ZF.cc_increasing_of_successor_l I hZF hω hQ
    (fun i j B C hij hi hj x hx => (step i j B C hij hi hj x).mpr (Or.inl hx))
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  obtain ⟨N, hN⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have hu : Cc_union_d I Q N := fun x => (hN x).trans
    ⟨fun ⟨B, hB, hx⟩ => (hR B).mp hB |>.elim fun i hi => ⟨i, B, hi, hx⟩,
      fun ⟨i, B, hi, hx⟩ => ⟨B, (hR B).mpr ⟨i, hi⟩, hx⟩⟩
  obtain ⟨e, he, _⟩ := hω.1.1
  refine ⟨P, Q, N, hP, hQ, hz, step, hu,
    (fun x hx => (hu x).mpr ⟨e, A, hz e he, hx⟩), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, B, hi, hx⟩ := (hu x).mp hx
    exact (hP B).mp (hQ.output_mem_of_pairMember hi) x hx
  · rintro x ⟨n, s, t, p, hn, hs, ht, hp, hx⟩
    obtain ⟨i, B, hi, hb⟩ := ZF.cc_fseq_bound_l I hZF hω hQ mono hu hn hs
    obtain ⟨j, hji, hjω⟩ := hω.1.2 i (hQ.input_mem_of_pairMember hi)
    obtain ⟨C, _, hj⟩ := hQ.2.2 j hjω
    exact (hu x).mpr ⟨j, C, hj, (step i j B C hji hi hj x).mpr (Or.inr ⟨n, s, t, p, hn, hb, ht, hp, hx⟩)⟩
  · intro B hAB hB
    let η : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push B
    let ψ : UnarySchema 2 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
      (Formula.subset .newest (.bound 2))) }
    have hψ i : ψ.denote η i ↔ ∀ C, M.PairMember I i C Q → M.MemberSubset C B := by
      simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff]
      rfl
    have bound : ∀ i, M.mem i ω → ∀ C, M.PairMember I i C Q → M.MemberSubset C B := by
      apply hω.induction (fun i => ∀ C, M.PairMember I i C Q → M.MemberSubset C B)
      · obtain ⟨U, hU⟩ := ZF.separation_exists_d hZF ψ η ω
        exact ⟨U, fun i => (hU i).trans (and_congr_right fun _ => hψ i)⟩
      · intro z hz0 C hC
        exact hQ.1.2 z A C (hz z hz0) hC ▸ hAB
      · intro i hi ih j hji C hj
        obtain ⟨E, _, hE⟩ := hQ.2.2 i hi
        exact fun x hx => ((step i j E C hji hE hj x).mp hx).elim (ih E hE x)
          (fun hx => hB x (fc_value_mono_l I (ih E hE) hx))
    intro x hx
    obtain ⟨i, C, hi, hx⟩ := (hu x).mp hx
    exact bound i (hQ.input_mem_of_pairMember hi) C hi x hx

end YesMetaZFC.SetTheory
