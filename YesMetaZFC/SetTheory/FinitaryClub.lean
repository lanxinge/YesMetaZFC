import YesMetaZFC.SetTheory.FinitaryHullStep
import YesMetaZFC.SetTheory.CountableChain

/-! # 在指定内部 club 中构造有限元闭集

每步先作一次有限元闭包，再在 club 内取包含它的可数集合。选择函数沿内部 ω
迭代，链并仍在 club 中；有限参数截取保证它对全部给定运算闭合。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 任意内部 club 都包含承接指定可数种子、对指定可数运算族闭合的实际集合。 -/
theorem ZFC.fc_club_hull_l (hZFC : M.Models ZFC) {ω X S T D K C A} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hT : M.CardinalLessOrEqual I T ω)
    (hC : Cc_club_d I ω X C) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ N, M.mem N C ∧ M.MemberSubset A N ∧ Fc_closed_d I ω T K N := by
  have hZF := models_zf_l hZFC
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push T).push K
  let φ : BinarySchema 3 := { body := .existsE (.conj
    (fc_step_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
    (Formula.subset .newest (.bound 1))) }
  have hφ B E : φ.denote ρ B E ↔ ∃ V, Fc_step_d I ω T K B V ∧ M.MemberSubset V E := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      fc_step_sat_l I hZF.1, Formula.satisfies_subset_iff]
    rfl
  obtain ⟨F, hF, hf⟩ := uniformize_formula_l I hZFC φ ρ (X := C) (Y := C) (by
    intro B hB
    obtain ⟨V, hv, hV⟩ := ZF.fc_step_exists_l I hZF hK (hC.members B hB).1
    have hc := ZF.fc_step_countable_l I hZF hω hS hD hK hT
      (hC.members B hB).1 (hC.members B hB).2 hv
    obtain ⟨E, hE, he⟩ := hC.unbounded V hV hc
    exact ⟨E, hE, (hφ B E).mpr ⟨V, hv, he⟩⟩)
  obtain ⟨Z, hZ, hAZ⟩ := hC.unbounded A hA ha
  obtain ⟨Q, hQ, hz, hs⟩ := iterate_l I hZF hω hF hZ
  have step {i j B E} (hj : M.SuccessorOf j i) (hi : M.PairMember I i B Q) (he : M.PairMember I j E Q) :
      ∃ V, Fc_step_d I ω T K B V ∧ M.MemberSubset V E := (hφ B E).mp (hf B E (hs i j B E hj hi he))
  have inc := ZF.cc_increasing_of_successor_l I hZF hω hQ (fun i j B E hj hi he => by
    obtain ⟨V, hv, hV⟩ := step hj hi he
    exact fun x hx => hV x ((hv x).mpr (Or.inl hx)))
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  obtain ⟨N, hN⟩ := KP.exists_union (ZF.modelsKP hZF) Y
  have hu : Cc_union_d I Q N := fun x => (hN x).trans
    ⟨fun ⟨B, hB, hx⟩ => (hY B).mp hB |>.elim fun i hi => ⟨i, B, hi, hx⟩,
      fun ⟨i, B, hi, hx⟩ => ⟨B, (hY B).mpr ⟨i, hi⟩, hx⟩⟩
  obtain ⟨e, he, _⟩ := hω.1.1
  refine ⟨N, hC.closed Q N hQ inc hu, fun x hx => (hu x).mpr ⟨e, Z, hz e he, hAZ x hx⟩, ?_⟩
  rintro x ⟨n, s, t, p, hn, hsN, ht, hp, hx⟩
  obtain ⟨i, B, hi, hsB⟩ := ZF.cc_fseq_bound_l I hZF hω hQ inc hu hn hsN
  obtain ⟨j, hji, hjω⟩ := hω.1.2 i (hQ.input_mem_of_pairMember hi)
  obtain ⟨E, _, hj⟩ := hQ.2.2 j hjω
  obtain ⟨V, hv, hVE⟩ := step hji hi hj
  exact (hu x).mpr ⟨j, E, hj, hVE x ((hv x).mpr (Or.inr ⟨n, s, t, p, hn, hsB, ht, hp, hx⟩))⟩

/-- 在任意内部 club 中截取对一个实际有限元运算族闭合的成员，所得仍是 club。 -/
theorem ZFC.fc_club_refine_l (hZFC : M.Models ZFC) {ω X S T D K C} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hT : M.CardinalLessOrEqual I T ω)
    (hC : Cc_club_d I ω X C) : ∃ V, Cc_club_d I ω X V ∧
      ∀ N, M.mem N V ↔ M.mem N C ∧ Fc_closed_d I ω T K N := by
  have hZF := models_zf_l hZFC
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push T).push K
  let φ : UnarySchema 3 := { body := fc_closed_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨V, hV⟩ := ZF.separation_exists_d hZF φ ρ C
  have hv N : M.mem N V ↔ M.mem N C ∧ Fc_closed_d I ω T K N :=
    (hV N).trans (and_congr_right fun _ => fc_closed_sat_l I hZF.1 _ _ _ _ _)
  refine ⟨V, ⟨fun N hN => hC.members N ((hv N).mp hN).1, ?_, ?_⟩, hv⟩
  · intro A hA ha
    obtain ⟨N, hN, hAN, hn⟩ := fc_club_hull_l I hZFC hω hS hD hK hT hC hA ha
    exact ⟨N, (hv N).mpr ⟨hN, hn⟩, hAN⟩
  · intro f N hf hm hu
    have hfC := hf.mono_target_l I (fun A hA => ((hv A).mp hA).1)
    refine (hv N).mpr ⟨hC.closed f N hfC hm hu, ?_⟩
    rintro x ⟨n, s, t, p, hn, hsN, ht, hp, hx⟩
    obtain ⟨j, A, hj, hsA⟩ := ZF.cc_fseq_bound_l I hZF hω hf hm hu hn hsN
    have hxA := ((hv A).mp (hf.output_mem_of_pairMember hj)).2 x ⟨n, s, t, p, hn, hsA, ht, hp, hx⟩
    exact (hu x).mpr ⟨j, A, hj, hxA⟩

end YesMetaZFC.SetTheory
