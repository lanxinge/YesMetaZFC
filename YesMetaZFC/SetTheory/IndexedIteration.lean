import YesMetaZFC.SetTheory.DependentChoice

/-! # 原 ZF 中实际函数图的带指标 ω 递归

状态为 (指标,当前值)，下一状态由后继指标与给定函数图唯一决定。
原公式的内部 ω 归纳核验第一坐标，再投影出所需序列；不使用对象选择公理。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem indexed_iteration_l (hZF : M.Models ZF) {ω X D F a} (hω : M.IsOmega ω)
    (hD : M.IsCartesianProduct I D ω X) (hF : M.IsSetFunctionFromTo I F D X) (ha : M.mem a X) :
    ∃ Q, M.IsSetFunctionFromTo I Q ω X ∧
      (∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o a Q) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x Q → M.PairMember I j y Q →
        ∃ p, I.Codes p i x ∧ M.PairMember I p y F := by
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let ψ : BinarySchema 1 := {
    body := .existsE (.existsE (.existsE (.existsE
      (.conj (𝒞.code (.bound 5) (.bound 3) (.bound 2))
        (.conj (𝒞.code (.bound 4) (.bound 1) .newest)
          (.conj (Formula.isSuccessor (.bound 1) (.bound 3))
            (Formula.orderedPairMem 𝒞 (.bound 5) .newest (.bound 6)))))))) }
  have hψ s t : ψ.denote ρ s t ↔ ∃ i x j y,
      I.Codes s i x ∧ I.Codes t j y ∧ M.SuccessorOf j i ∧ M.PairMember I s y F := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨R, hR, hr⟩ := exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := D) (target := D) (by
    intro s hsD
    obtain ⟨i, hi, x, _, hs⟩ := (hD s).mp hsD
    obtain ⟨y, _, hsy⟩ := hF.2.2 s hsD
    obtain ⟨j, hj, _⟩ := hω.1.2 i hi
    obtain ⟨t, ht⟩ := I.total j y
    exact ⟨t, (hψ s t).mpr ⟨i, x, j, y, hs, ht, hj, hsy⟩⟩) (by
    intro s _ t u ht hu
    obtain ⟨i, x, j, y, hs, ht, hj, hy⟩ := (hψ s t).mp ht
    obtain ⟨i', x', j', y', hs', hu, hj', hy'⟩ := (hψ s u).mp hu
    obtain ⟨rfl, rfl⟩ := I.injective hs hs'
    have hej := Structure.SuccessorOf.eq hZF.1 hj hj'
    have hey := hF.1.2 s y y' hy hy'
    subst j' y'
    exact I.unique ht hu) (by
    intro s t hsD ht
    obtain ⟨i, x, j, y, hs, ht, hj, hy⟩ := (hψ s t).mp ht
    obtain ⟨i', hi, x', _, hs'⟩ := (hD s).mp hsD
    obtain ⟨rfl, rfl⟩ := I.injective hs hs'
    obtain ⟨j', hj', hjω⟩ := hω.1.2 i hi
    have hej := Structure.SuccessorOf.eq hZF.1 hj' hj
    exact (hD t).mpr ⟨j, hej ▸ hjω, y, hF.output_mem_of_pairMember hy, ht⟩)
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  obtain ⟨s, hs⟩ := I.total o a
  obtain ⟨G, hG, hz, hg⟩ := ZFC.iterate_l I hZF hω hR ((hD s).mpr ⟨o, hoω, a, ha, hs⟩)
  have coords : ∀ i, M.mem i ω → ∀ s, M.PairMember I i s G → ∃ x, I.Codes s i x := by
    apply hω.induction (fun i => ∀ s, M.PairMember I i s G → ∃ x, I.Codes s i x)
    · let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
      let θ : UnarySchema 1 := {
        body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
          (.existsE (𝒞.code (.bound 1) (.bound 2) .newest))) }
      obtain ⟨C, hC⟩ := separation_exists_d hZF θ δ ω
      exact ⟨C, fun i => by simpa only [θ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, I.realizes] using! hC i⟩
    · intro e he t het
      have heo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (ho x))
      have hts := hG.1.2 e t s het (hz e he)
      exact ⟨a, hts.symm ▸ heo.symm ▸ hs⟩
    · intro i hi ih j hij t hjt
      obtain ⟨r, _, hir⟩ := hG.2.2 i hi
      obtain ⟨x, hri⟩ := ih r hir
      obtain ⟨i', x', j', y, hr', ht', hji, _⟩ := (hψ r t).mp ((hr r t).mp (hg i j r t hij hir hjt)).2
      obtain ⟨hei, _⟩ := I.injective hri hr'
      subst i'
      have hej := Structure.SuccessorOf.eq hZF.1 hji hij
      exact ⟨y, hej ▸ ht'⟩
  let δ : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let θ : BinarySchema 1 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (𝒞.code .newest (.bound 2) (.bound 1))) }
  have hθ i x : θ.denote δ i x ↔ ∃ s, M.PairMember I i s G ∧ I.Codes s i x := by
    simp only [BinarySchema.denote, θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, I.realizes]
    rfl
  obtain ⟨Q, hQ, hq⟩ := exists_setFunctionFromTo_of_denote hZF I θ δ (source := ω) (target := X) (by
    intro i hi
    obtain ⟨s, _, his⟩ := hG.2.2 i hi
    obtain ⟨x, hs⟩ := coords i hi s his
    exact ⟨x, (hθ i x).mpr ⟨s, his, hs⟩⟩) (by
    intro i _ x y hx hy
    obtain ⟨s, his, hs⟩ := (hθ i x).mp hx
    obtain ⟨t, hit, ht⟩ := (hθ i y).mp hy
    have he := hG.1.2 i s t his hit
    exact (I.injective hs (he.symm ▸ ht)).2) (by
    intro i x _ hx
    obtain ⟨s, his, hs⟩ := (hθ i x).mp hx
    obtain ⟨j, _, y, hy, hs'⟩ := (hD s).mp (hG.output_mem_of_pairMember his)
    exact (I.injective hs' hs).2 ▸ hy)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro e he
    have heo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (ho x))
    exact (hq e a).mpr ⟨heo.symm ▸ hoω, (hθ e a).mpr ⟨s, hz e he, heo.symm ▸ hs⟩⟩
  · intro i j x y hij hix hjy
    obtain ⟨s, his, hs⟩ := (hθ i x).mp ((hq i x).mp hix).2
    obtain ⟨t, hjt, ht⟩ := (hθ j y).mp ((hq j y).mp hjy).2
    obtain ⟨i', x', j', y', hs', ht', _, hsy⟩ := (hψ s t).mp ((hr s t).mp (hg i j s t hij his hjt)).2
    obtain ⟨_, hey⟩ := I.injective ht' ht
    exact ⟨s, hs, hey ▸ hsy⟩

end YesMetaZFC.SetTheory.ZF
