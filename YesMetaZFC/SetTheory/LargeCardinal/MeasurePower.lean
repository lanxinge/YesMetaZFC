import YesMetaZFC.SetTheory.LargeCardinal.Measurable

/-! # 完备非主超滤排除小幂集中的长单射

逐坐标选取测度一的真假纤维，再取少于 κ 个纤维的交。
交内任意两点的子集像完全相同；若原图为单射，交就是单点集，矛盾。
真假选择由超滤的唯一决定及原替代构造，不使用选择公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_power_injection_l (hZF : M.Models ZF) {κ U μ P : M.Domain}
    (hU : FilterZF.Maximal_d (ℳ := M) κ U) (hn : Ed_nonprincipal_d U) (hc : Ed_complete_d κ κ U)
    (hμ : M.mem μ κ) (power : M.IsPowerSetOf P μ) : ¬ M.CardinalLessOrEqual I κ P := by
  classical
  rintro ⟨f, hf⟩
  let hit i x := ∃ A, M.PairMember I x A f ∧ M.mem i A
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases κ (fun _ => U)), fun _ => κ⟩
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 4)) (.disj
      (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
        (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem (.bound 3) .newest))))))
      (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
        (.neg (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem (.bound 3) .newest)))))))) }
  have read i s : φ.denote ρ i s ↔ M.mem s U ∧
      ((∀ x, M.mem x s ↔ M.mem x κ ∧ hit i x) ∨ (∀ x, M.mem x s ↔ M.mem x κ ∧ ¬ hit i x)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff]; rfl
  have total i (_ : M.mem i μ) : ∃ s, φ.denote ρ i s := by
    let θ : UnarySchema 2 := {
      body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3)) (.mem (.bound 2) .newest)) }
    obtain ⟨s, ss⟩ := ZF.separation_exists_d hZF θ ⟨Fin.cases i (fun _ => f), fun _ => κ⟩ κ
    have row x : M.mem x s ↔ M.mem x κ ∧ hit i x := by
      simpa only [θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff] using! ss x
    by_cases hs : M.mem s U
    · exact ⟨s, (read i s).mpr ⟨hs, Or.inl row⟩⟩
    obtain ⟨t, ts⟩ := KP.difference_exists_d (ZF.modelsKP hZF) s κ
    have ht := (FilterZF.maximal_decides_d hZF hU (fun x hx => ((row x).mp hx).1) ts).resolve_left hs
    exact ⟨t, (read i t).mpr ⟨ht, Or.inr (fun x => (ts x).trans
      ⟨fun ⟨hx, no⟩ => ⟨hx, fun hi => no ((row x).mpr ⟨hx, hi⟩)⟩,
        fun ⟨hx, no⟩ => ⟨hx, fun hs => no ((row x).mp hs).2⟩⟩)⟩⟩
  have apart i s t (hs : M.mem s U) (ht : M.mem t U)
      (left : ∀ x, M.mem x s ↔ M.mem x κ ∧ hit i x)
      (right : ∀ x, M.mem x t ↔ M.mem x κ ∧ ¬ hit i x) : False := by
    obtain ⟨r, hr, rs, rt⟩ := hU.1.2.2.2 s t hs ht
    obtain ⟨x, hx⟩ := hU.2.1 r hr
    exact ((right x).mp (rt x hx)).2 ((left x).mp (rs x hx)).2
  have unique i s t (hs : φ.denote ρ i s) (ht : φ.denote ρ i t) : s = t := by
    obtain ⟨hs, left⟩ := (read i s).mp hs
    obtain ⟨ht, right⟩ := (read i t).mp ht
    rcases left with left | left <;> rcases right with right | right
    · exact hZF.1.eq_of_same_members s t (fun x => (left x).trans (right x).symm)
    · exact (apart i s t hs ht left right).elim
    · exact (apart i t s ht hs right left).elim
    · exact hZF.1.eq_of_same_members s t (fun x => (left x).trans (right x).symm)
  obtain ⟨g, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    total (fun i _ => unique i) (fun i s _ hs => ((read i s).mp hs).1)
  obtain ⟨r, hr, rs⟩ := hc μ hμ g (fn0_of_function_l (ZF.modelsKP hZF) gf)
  have decode i x A (hx : M.PairMember I x A f) : hit i x ↔ M.mem i A :=
    ⟨fun ⟨B, hb, hi⟩ => hf.1.1.2 x B A hb hx ▸ hi, fun hi => ⟨A, hx, hi⟩⟩
  have same x y (hx : M.mem x r) (hy : M.mem y r) : x = y := by
    obtain ⟨hxκ, allx⟩ := (rs x).mp hx
    obtain ⟨hyκ, ally⟩ := (rs y).mp hy
    obtain ⟨A, hA, hxA⟩ := hf.1.2.2 x hxκ
    obtain ⟨B, hB, hyB⟩ := hf.1.2.2 y hyκ
    have eq : A = B := hZF.1.eq_of_same_members A B (fun i => by
      by_cases hi : M.mem i μ
      · obtain ⟨s, hs, his⟩ := gf.2.2 i hi
        have xx := allx i hi s hs his
        have yy := ally i hi s hs his
        rcases ((read i s).mp ((gs i s).mp his).2).2 with row | row
        · exact iff_of_true ((decode i x A hxA).mp ((row x).mp xx).2) ((decode i y B hyB).mp ((row y).mp yy).2)
        · exact iff_of_false (fun h => ((row x).mp xx).2 ((decode i x A hxA).mpr h))
            (fun h => ((row y).mp yy).2 ((decode i y B hyB).mpr h))
      · exact iff_of_false (fun h => hi ((power A).mp hA i h)) (fun h => hi ((power B).mp hB i h)))
    exact hf.2 x y A hxA (eq.symm ▸ hyB)
  obtain ⟨x, hx⟩ := hU.2.1 r hr
  exact hn x r (fun y => ⟨fun hy => same y x hy hx, fun eq => eq.symm ▸ hx⟩) hr

end YesMetaZFC.SetTheory.LargeCardinal
