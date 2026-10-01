import YesMetaZFC.SetTheory.Choice
import YesMetaZFC.SetTheory.Ord.Natural

/-! # 集合关系的内部选择与依赖递归

原选择集公理把全定义集合关系单值化；原序数递归随后构造模型自己的 ω 序列。
这里的函数图均属于模型，不把外部选择所得的序列当作内部集合。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 每个全定义集合关系包含一个同定义域的集合编码函数。 -/
theorem uniformize_l (hZFC : M.Models ZFC) {X Y R : M.Domain}
    (ht : ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ M.PairMember I x y R) :
    ∃ F, M.IsSetFunctionFromTo I F X Y ∧
      ∀ x y, M.PairMember I x y F → M.PairMember I x y R := by
  let hZF := models_zf_l hZFC
  obtain ⟨C, hC⟩ := selector_l hZFC I Y
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push Y).push C
  let φ : BinarySchema 3 := {
    body := .existsE (.conj (.forallE (.iff (.mem .newest (.bound 1))
      (.conj (.mem .newest (.bound 5)) (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 6)))))
      (.conj (.mem (.bound 1) .newest) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3)))) }
  have hφ x y : φ.denote ρ x y ↔ ∃ T,
      (∀ z, M.mem z T ↔ M.mem z Y ∧ M.PairMember I x z R) ∧
        M.mem y T ∧ M.PairMember I T y C := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have htotal x (hx : M.mem x X) : ∃ y, φ.denote ρ x y := by
    let ψ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2) }
    obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF ψ
      ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push x) Y
    have hT z : M.mem z T ↔ M.mem z Y ∧ M.PairMember I x z R := by
      rw [hT z]
      simp only [ψ, Formula.satisfies_orderedPairMem_iff I]
      rfl
    obtain ⟨y, hy, hc, _⟩ := hC T (fun z hz => ((hT z).mp hz).1)
      ((ht x hx).elim fun y hy => ⟨y, (hT y).mpr hy⟩)
    exact ⟨y, (hφ x y).mpr ⟨T, hT, hy, hc⟩⟩
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ htotal (by
    intro x hx y z hy hz
    obtain ⟨T, hT, hy, hcy⟩ := (hφ x y).mp hy
    obtain ⟨V, hV, hz, hcz⟩ := (hφ x z).mp hz
    have he := hZFC.1.eq_of_same_members V T (fun w => (hV w).trans (hT w).symm)
    subst V
    obtain ⟨a, _, _, hu⟩ := hC T (fun w hw => ((hT w).mp hw).1) ⟨y, hy⟩
    exact (hu y hy hcy).trans (hu z hz hcz).symm) (by
    intro x y _ hy
    obtain ⟨T, hT, hy, _⟩ := (hφ x y).mp hy
    exact ((hT y).mp hy).1)
  refine ⟨F, hF, fun x y hxy => ?_⟩
  obtain ⟨T, hT, hy, _⟩ := (hφ x y).mp ((he x y).mp hxy).2
  exact ((hT y).mp hy).2

/-- 对实际二元公式直接构造内部选择函数，目标界由调用处给出的集合承载。 -/
theorem uniformize_formula_l (hZFC : M.Models ZFC) {n} (φ : BinarySchema n) (ρ : Env M n)
    {X Y : M.Domain} (ht : ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ φ.denote ρ x y) :
    ∃ F, M.IsSetFunctionFromTo I F X Y ∧ ∀ x y, M.PairMember I x y F → φ.denote ρ x y := by
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) X Y
  obtain ⟨W, hW⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have hx x (hx : M.mem x X) : M.mem x W := (hW x).mpr ⟨X, (hP X).mpr (Or.inl rfl), hx⟩
  have hy y (hy : M.mem y Y) : M.mem y W := (hW y).mpr ⟨Y, (hP Y).mpr (Or.inr rfl), hy⟩
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  obtain ⟨F, hF, hf⟩ := uniformize_l I hZFC (fun x hxX => by
    obtain ⟨y, hyY, hφ⟩ := ht x hxX
    exact ⟨y, hyY, (hr x y).mpr ⟨hx x hxX, hy y hyY, hφ⟩⟩)
  exact ⟨F, hF, fun x y hxy => ((hr x y).mp (hf x y hxy)).2.2⟩

def Next_d (F a x y : M.Domain) : Prop := M.PairMember I x y F ∨
  ((¬ ∃ z, M.PairMember I x z F) ∧ y = a)

def next_m (𝒞 : OrderedPairConvention) {n} (F a x y : Term n) : Formula 1 n :=
  .disj (Formula.orderedPairMem 𝒞 x y F) (.conj
    (.neg (.existsE (Formula.orderedPairMem 𝒞 x.weaken .newest F.weaken))) (Formula.extensionalEq y a))
derive_free_closed next_m

def iter_m (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .disj (.conj (Formula.isZeroLengthSequence 𝒞 (.bound 1))
    (Formula.extensionalEq .newest (.bound 2))) (.disj (.existsE
      (.conj (Formula.isSuccessorLengthSequenceWithLast 𝒞 (.bound 2) .newest)
        (next_m 𝒞 (.bound 4) (.bound 3) .newest (.bound 1))))
      (Formula.isLimitLengthSequenceWithUnion 𝒞 (.bound 1) .newest))

theorem iter_sat_l (hE : Extensional M) (ρ : Env M 2) (s x : M.Domain) :
    (iter_m 𝒞).denote ρ s x ↔ M.IsZeroSuccessorLimitStep I
      (fun x => x = ρ.bound 0) (Next_d I (ρ.bound 1) (ρ.bound 0)) s x := by
  simp only [iter_m, BinarySchema.denote, Structure.IsZeroSuccessorLimitStep, next_m, Next_d,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_isZeroLengthSequence_iff I hE,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff I hE,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff I hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE]
  rfl

/-- 内部自映射从任意初值出发，产生沿模型自身 ω 迭代的函数图。 -/
theorem iterate_l (hZF : M.Models ZF) {ω X F a : M.Domain} (hω : M.IsOmega ω)
    (hF : M.IsSetFunctionFromTo I F X X) (ha : M.mem a X) :
    ∃ g, M.IsSetFunctionFromTo I g ω X ∧
      (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e a g) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x g → M.PairMember I j y g →
        M.PairMember I x y F := by
  classical
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push a
  have hop : M.IsClassFunctionOnTransfiniteSequences I ((iter_m 𝒞).denote ρ) := by
    have ht := ZF.zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences hZF I
      (fun x => x = a) (Next_d I F a) ⟨a, rfl, fun _ h => h⟩ (by
        intro x
        by_cases hn : ∃ y, M.PairMember I x y F
        · obtain ⟨y, hy⟩ := hn
          exact ⟨y, Or.inl hy, fun z hz => hz.elim
            (fun hz => hF.1.2 x z y hz hy) (fun hz => False.elim (hz.1 ⟨y, hy⟩))⟩
        · exact ⟨a, Or.inr ⟨hn, rfl⟩, fun y hy => hy.elim
            (fun hy => False.elim (hn ⟨y, hy⟩)) And.right⟩)
    intro s hs
    obtain ⟨x, hx, hu⟩ := ht s hs
    exact ⟨x, (iter_sat_l I hZF.1 ρ s x).mpr hx,
      fun y hy => hu y ((iter_sat_l I hZF.1 ρ s y).mp hy)⟩
  obtain ⟨g, hg⟩ := ZF.recursiveSequence_exists hZF I ρ (iter_m 𝒞) hop (hω.isOrdinal hZF)
  have hz e (he : ∀ x, ¬ M.mem x e) x (hx : M.PairMember I e x g) : x = a := by
    have heω := (hg.1.2.2 e).mpr ⟨x, hx⟩
    obtain ⟨s, hs, hop⟩ := hg.2 e heω x hx
    have hs0 : M.IsZeroLengthSequence I s := ⟨e, hg.1.restriction heω hs, he⟩
    rcases (iter_sat_l I hZF.1 ρ s x).mp hop with hx | ⟨y, hy, _⟩ | hx
    · exact hx.2
    · exact False.elim (hs0.not_successorLength hZF.1 hy)
    · exact False.elim (hs0.not_limitLength hZF.1 hx)
  have hs i j x y (hij : M.SuccessorOf j i) (hx : M.PairMember I i x g)
      (hy : M.PairMember I j y g) (hxX : M.mem x X) : M.PairMember I x y F := by
    have hi := (hg.1.2.2 i).mpr ⟨x, hx⟩
    have hj := (hg.1.2.2 j).mpr ⟨y, hy⟩
    obtain ⟨s, hs, hop⟩ := hg.2 j hj y hy
    have hsl : M.IsSuccessorLengthSequenceWithLast I s x :=
      ⟨i, hg.1.1.mem hi, j, hij, hg.1.restriction hj hs,
        (hs.2 i x).mpr ⟨hij.predecessor_mem, hx⟩⟩
    rcases (iter_sat_l I hZF.1 ρ s y).mp hop with hy | ⟨z, hz, hy⟩ | hy
    · exact False.elim (hy.1.not_successorLength hZF.1 hsl)
    · have he := hz.last_eq hZF.1 hsl
      subst z
      exact hy.elim id (fun hy => False.elim (hy.1 ((hF.2.2 x hxX).elim fun z hz => ⟨z, hz.2⟩)))
    · exact False.elim (hsl.not_limitLength hZF.1 hy)
  have htarget : ∀ i, M.mem i ω → ∀ x, M.PairMember I i x g → M.mem x X := by
    apply hω.induction (fun i => ∀ x, M.PairMember I i x g → M.mem x X)
    · let φ : UnarySchema 2 := {
        body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
          (.mem .newest (.bound 3))) }
      obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ
        ((⟨fun _ => X, fun _ => X⟩ : Env M 1).push g) ω
      refine ⟨T, fun i => ?_⟩
      rw [hT i]
      simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
      rfl
    · intro e he x hx
      exact hz e he x hx ▸ ha
    · intro i hi ih j hij y hy
      obtain ⟨x, hx⟩ := (hg.1.2.2 i).mp hi
      exact hF.output_mem_of_pairMember (hs i j x y hij hx hy (ih x hx))
  refine ⟨g, ⟨hg.1.2.1, hg.1.2.2, fun i hi => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hg.1.2.2 i).mp hi
    exact ⟨x, htarget i hi x hx, hx⟩
  · intro e he
    obtain ⟨e', he', heω⟩ := hω.1.1
    have heq : e' = e := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he x))
    subst e'
    obtain ⟨x, hx⟩ := (hg.1.2.2 e).mp heω
    exact hz e he x hx ▸ hx
  · intro i j x y hij hx hy
    exact hs i j x y hij hx hy (htarget i ((hg.1.2.2 i).mpr ⟨x, hx⟩) x hx)

/-- 原 ZFC 对任意内部全定义关系证明依赖选择，不需要额外 DC 合同。 -/
theorem dependent_choice_l (hZFC : M.Models ZFC) {ω X R a : M.Domain}
    (hω : M.IsOmega ω) (ha : M.mem a X)
    (ht : ∀ x, M.mem x X → ∃ y, M.mem y X ∧ M.PairMember I x y R) :
    ∃ g, M.IsSetFunctionFromTo I g ω X ∧
      (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e a g) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x g → M.PairMember I j y g →
        M.PairMember I x y R := by
  obtain ⟨F, hF, hFR⟩ := uniformize_l I hZFC ht
  obtain ⟨g, hg, hz, hs⟩ := iterate_l I (models_zf_l hZFC) hω hF ha
  exact ⟨g, hg, hz, fun i j x y hij hx hy => hFR x y (hs i j x y hij hx hy)⟩

/-- 内部满射的纤维选择给出反向基数不等式。 -/
theorem surjection_bound_l (hZFC : M.Models ZFC) {F X Y}
    (hf : M.IsSetFunctionFromTo I F X Y) (hs : M.IsSetSurjectiveOnto I F X Y) : M.CardinalLessOrEqual I Y X := by
  let φ : BinarySchema 1 := { body := Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  have hφ y x : φ.denote ρ y x ↔ M.PairMember I x y F :=
    Formula.satisfies_orderedPairMem_iff I ((ρ.push y).push x) .newest (.bound 1) (.bound 2)
  obtain ⟨G, hG, hg⟩ := uniformize_formula_l I hZFC φ ρ (X := Y) (Y := X) (by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hs y hy
    exact ⟨x, hx, (hφ y x).mpr hxy⟩)
  exact ⟨G, hG, fun y z x hy hz => hf.1.2 x y z ((hφ y x).mp (hg y x hy)) ((hφ z x).mp (hg z x hz))⟩

end YesMetaZFC.SetTheory.ZFC
