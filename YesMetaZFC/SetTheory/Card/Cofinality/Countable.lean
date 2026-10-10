import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Card.Omega

/-! # ZF 中的可数共尾集与严格 ω 共尾列

反向延拓可数单射得到实际枚举。每步取同时高于前项和枚举项的最小成员，
由带指标的确定递归构造严格共尾列；不调用对象选择或外部标准自然数递归。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 内部可数共尾集给出实际严格 ω 共尾列，序列的所有值仍在原集合中。 -/
theorem cc_strict_cofinal_l (hZF : M.Models ZF) {ω A α} (hω : M.IsOmega ω)
    (hA : M.IsCofinalSubset A α) (hc : M.CardinalLessOrEqual I A ω) :
    ∃ Q, M.IsSetFunctionFromTo I Q ω A ∧ M.IsCofinalOrdinalSequence I Q ω α := by
  obtain ⟨t, ht⟩ := hA.1.2.1
  obtain ⟨a, ha, _⟩ := (hA.2.2 t).mp ht
  obtain ⟨G, hG⟩ := hc
  obtain ⟨g, hg, hgr⟩ := injection_retract_l I hZF hG (fun _ h => h) ha
  have next x (hx : M.mem x A) : ∃ y, M.mem y A ∧ M.mem x y := (hA.2.2 x).mp (hA.2.1 x hx)
  have upper x z (hx : M.mem x A) (hz : M.mem z A) :
      ∃ y, M.mem y A ∧ M.mem x y ∧ M.mem z y := by
    rcases hA.1.1.wellOrder.linear.compare x (hA.2.1 x hx) z (hA.2.1 z hz) with he | hxz | hzx
    · obtain ⟨y, hy, hzy⟩ := next z hz
      exact ⟨y, hy, (hZF.1.eq_of_same_members x z he).symm ▸ hzy, hzy⟩
    · obtain ⟨y, hy, hzy⟩ := next z hz
      exact ⟨y, hy, (hA.1.1.mem (hA.2.1 y hy)).transitive z hzy x hxz, hzy⟩
    · obtain ⟨y, hy, hxy⟩ := next x hx
      exact ⟨y, hy, hxy, (hA.1.1.mem (hA.2.1 y hy)).transitive x hxy z hzx⟩
  have least x z (hx : M.mem x A) (hz : M.mem z A) :
      ∃ y, (M.mem y A ∧ M.mem x y ∧ M.mem z y) ∧
        ∀ w, M.mem w A ∧ M.mem x w ∧ M.mem z w → M.MemberSubset y w := by
    let ρ : Env M 3 := ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push x).push z
    let θ : UnarySchema 3 := {
      body := .conj (.mem .newest (.bound 3)) (.conj (.mem (.bound 2) .newest) (.mem (.bound 1) .newest)) }
    obtain ⟨C, hC⟩ := separation_exists_d hZF θ ρ A
    have hc w : M.mem w C ↔ M.mem w A ∧ (M.mem w A ∧ M.mem x w ∧ M.mem z w) := by
      simpa only [θ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] using! hC w
    obtain ⟨y, hy⟩ := upper x z hx hz
    obtain ⟨v, hv, hm⟩ := hA.1.1.wellOrder.least C
      (fun w hw => hA.2.1 w ((hc w).mp hw).1) ⟨y, (hc y).mpr ⟨hy.1, hy⟩⟩
    refine ⟨v, ((hc v).mp hv).2, fun w hw => ?_⟩
    rcases hm w ((hc w).mpr ⟨hw.1, hw⟩) with he | hvw
    · exact fun t ht => (he t).mp ht
    · exact (hA.1.1.mem (hA.2.1 w hw.1)).transitive.memberSubset hvw
  -- 最小上界唯一，故用替代取得实际转移函数，随后直接作 ZF 递归。
  obtain ⟨D, hD⟩ := exists_cartesianProduct hZF I ω A
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push g
  let ψ : BinarySchema 2 := {
    body := .existsE (.existsE (.existsE (.conj (𝒞.code (.bound 4) (.bound 2) (.bound 1))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5))
        (.conj (.conj (.mem (.bound 3) (.bound 6))
          (.conj (.mem (.bound 1) (.bound 3)) (.mem .newest (.bound 3))))
          (.forallE (.imp (.conj (.mem .newest (.bound 7))
            (.conj (.mem (.bound 2) .newest) (.mem (.bound 1) .newest)))
            (Formula.subset (.bound 4) .newest)))))))) }
  have hψ p y : ψ.denote ρ p y ↔ ∃ i x z, I.Codes p i x ∧ M.PairMember I i z g ∧
      (M.mem y A ∧ M.mem x y ∧ M.mem z y) ∧
        ∀ w, M.mem w A ∧ M.mem x w ∧ M.mem z w → M.MemberSubset y w := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff]
    rfl
  obtain ⟨F, hF, hf⟩ := exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := D) (target := A) (by
    intro p hp
    obtain ⟨i, hi, x, hx, hp⟩ := (hD p).mp hp
    obtain ⟨z, hz, hiz⟩ := hg.2.2 i hi
    obtain ⟨y, hy, hm⟩ := least x z hx hz
    exact ⟨y, (hψ p y).mpr ⟨i, x, z, hp, hiz, hy, hm⟩⟩) (by
    intro p _ y v hy hv
    obtain ⟨i, x, z, hp, hiz, hy, hm⟩ := (hψ p y).mp hy
    obtain ⟨i', x', z', hp', hiz', hv, hm'⟩ := (hψ p v).mp hv
    obtain ⟨rfl, rfl⟩ := I.injective hp hp'
    have he := hg.1.2 i z z' hiz hiz'
    subst z'
    exact hZF.1.eq_of_same_members y v (fun t => ⟨hm v hv t, hm' y hy t⟩)) (by
    intro p y _ hy
    obtain ⟨_, _, _, _, _, hy, _⟩ := (hψ p y).mp hy
    exact hy.1)
  obtain ⟨Q, hQ, _, hs⟩ := indexed_iteration_l I hZF hω hD hF ha
  have step i j x y (hij : M.SuccessorOf j i) (hix : M.PairMember I i x Q) (hjy : M.PairMember I j y Q) :
      M.mem x y ∧ ∀ z, M.PairMember I i z g → M.mem z y := by
    obtain ⟨p, hp, hpy⟩ := hs i j x y hij hix hjy
    obtain ⟨i', x', z, hp', hiz, hy, _⟩ := (hψ p y).mp ((hf p y).mp hpy).2
    obtain ⟨rfl, rfl⟩ := I.injective hp hp'
    exact ⟨hy.2.1, fun z' hz' => hg.1.2 i z z' hiz hz' ▸ hy.2.2⟩
  let θ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  let δ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
  have hθ x y : θ.denote δ x y ↔ M.mem x y := Formula.satisfies_mem_iff _ _ _
  have inc := rel_chain_l I hZF θ δ hω hQ
    (fun x y z _ _ hz hxy hyz => (hθ x z).mpr ((hA.1.1.mem (hA.2.1 z hz)).transitive y
      ((hθ y z).mp hyz) x ((hθ x y).mp hxy)))
    (fun i j x y hij hix hjy => (hθ x y).mpr (step i j x y hij hix hjy).1)
  have ord : M.IsOrdinalValuedSequence I Q ω := ⟨⟨hω.isOrdinal hZF, hQ.1, hQ.2.1⟩,
    fun _ _ x hx => hA.1.1.mem (hA.2.1 x (hQ.output_mem_of_pairMember hx))⟩
  obtain ⟨T, hT⟩ := exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  refine ⟨Q, hQ, hA.1, ⟨ord, fun i _ j _ hij x y hx hy => (hθ x y).mp (inc i j x y hij hx hy)⟩,
    ⟨hA.1.1, ord, T, hT, ?_⟩, fun _ _ x hx => hA.2.1 x (hQ.output_mem_of_pairMember hx)⟩
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz, hxz⟩ := (hA.2.2 x).mp hx
    obtain ⟨i, hi, hzi⟩ := hG.1.2.2 z hz
    obtain ⟨j, hij, hj⟩ := hω.1.2 i hi
    obtain ⟨v, _, hiv⟩ := hQ.2.2 i hi
    obtain ⟨y, hy, hjy⟩ := hQ.2.2 j hj
    exact ⟨y, (hT y).mpr ⟨j, hjy⟩, (hA.1.1.mem (hA.2.1 y hy)).transitive z
      ((step i j v y hij hiv hjy).2 z (hgr z i hzi)) x hxz⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨i, hiy⟩ := (hT y).mp hy
    exact hA.1.1.transitive y (hA.2.1 y (hQ.output_mem_of_pairMember hiy)) x hxy

/-- ω 是非零极限序数中的最小者，所以严格 ω 共尾列已经给出精确共尾度。 -/
theorem cf_omega_iff_l (hZF : M.Models ZF) {ω α} (hω : M.IsOmega ω) :
    M.IsCofinality I ω α ↔ M.HasCofinalOrdinalSequence I ω α := by
  refine ⟨fun h => h.hasCofinalSequence, fun h => ⟨omega_cardinal_l I hZF hω, h, ?_⟩⟩
  rintro l ⟨F, hF⟩
  have hl := hF.length_isLimitOrdinal hZF
  have hwl := hω.subset_limitOrdinal hZF hl
  rcases (hω.isOrdinal hZF).trichotomy hZF.1 hl.1 (KP.difference_exists_d (modelsKP hZF))
      (KP.intersection_exists_d (modelsKP hZF) ω l) with he | hwl' | hlw
  · exact Or.inl (hZF.1.eq_of_same_members ω l he)
  · exact Or.inr hwl'
  · exact (hl.1.wellOrder.linear.irrefl l (hwl l hlw) (hwl l hlw)).elim

/-- 精确共尾度为 ω，当且仅当存在模型内部可数的实际共尾子集。 -/
theorem cf_omega_countable_l (hZF : M.Models ZF) {ω α} (hω : M.IsOmega ω) :
    M.IsCofinality I ω α ↔ ∃ A, M.IsCofinalSubset A α ∧ M.CardinalLessOrEqual I A ω := by
  constructor
  · intro h
    obtain ⟨F, hF⟩ := h.hasCofinalSequence
    have hf := hF.isSetInjectionFromTo hZF I
    obtain ⟨A, hA⟩ := exists_range_of_setFunction hZF I hf.1.1 hf.1.2.1
    have hFA : M.IsSetBijectionFromTo I F ω A := by
      refine ⟨⟨⟨hf.1.1, hf.1.2.1, ?_⟩, hf.2⟩, ?_⟩
      · intro i hi
        obtain ⟨y, _, hiy⟩ := hf.1.2.2 i hi
        exact ⟨y, (hA y).mpr ⟨i, hiy⟩, hiy⟩
      · intro y hy
        obtain ⟨i, hiy⟩ := (hA y).mp hy
        exact ⟨i, hf.1.input_mem_of_pairMember hiy, hiy⟩
    obtain ⟨G, hG⟩ := exists_inverseBijection hZF I hFA
    exact ⟨A, hF.range_isCofinalSubset hZF.1 hA, G, hG.1⟩
  · rintro ⟨A, hA, hc⟩
    obtain ⟨Q, _, hQ⟩ := cc_strict_cofinal_l I hZF hω hA hc
    exact (cf_omega_iff_l I hZF hω).mpr ⟨Q, hQ⟩

end YesMetaZFC.SetTheory.ZF
