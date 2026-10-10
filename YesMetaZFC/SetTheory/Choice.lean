import YesMetaZFC.SetTheory.Card.Aleph.Hartogs
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # 模型内部选择与序数枚举

先对互不相交的带标签行应用原选择集公理，得到任意非空子集的统一选择关系。
随后递归选取尚未出现的元素；Hartogs 定理迫使序列覆盖源集。
所有选择关系和序列都是模型内集合，不使用外部良序或不可计算数据实例。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} (h : M.Models ZFC)
include h

theorem models_zf_l : M.Models ZF := ⟨h.1, fun s hs => h.2 s (.zf hs)⟩

theorem choice_set_l (A : M.Domain)
    (hn : ∀ a, M.mem a A → ∃ x, M.mem x a)
    (hd : ∀ a, M.mem a A → ∀ b, M.mem b A → a ≠ b → ¬ ∃ x, M.mem x a ∧ M.mem x b) :
    ∃ C, ∀ a, M.mem a A → ∃ x, (M.mem x C ∧ M.mem x a) ∧
      ∀ y, (M.mem y C ∧ M.mem y a) → y = x := by
  have hc := (Structure.satisfiesSentence_iff M Axioms.choice).mp (h.2 _ .choice) (fun _ => A)
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq h.1, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken] at hc
  exact hc A ⟨hn, hd⟩

/-- 原选择集公理给出一个模型内关系，为源集的每个非空内部子集唯一选值。 -/
theorem selector_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ C, ∀ T, M.MemberSubset T S → (∃ x, M.mem x T) →
      ∃ x, M.mem x T ∧ M.PairMember I T x C ∧
        ∀ y, M.mem y T → M.PairMember I T y C → y = x := by
  let hZF := models_zf_l h
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF S
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I P S
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF X
  let φ : UnarySchema 1 := {
    body := .existsE (.conj (.mem .newest (.bound 2))
      (.conj (.existsE (.mem .newest (.bound 1)))
        (Formula.isCartesianRow 𝒞 (.bound 1) .newest .newest))) }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ Q
  have ha a : M.mem a A ↔ M.mem a Q ∧ ∃ T, M.mem T P ∧
      (∃ x, M.mem x T) ∧ ∀ p, M.mem p a ↔ ∃ x, M.mem x T ∧ I.Codes p T x := by
    rw [hA a]
    simp only [φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_isCartesianRow_iff I]
    rfl
  obtain ⟨C, hC⟩ := choice_set_l h A (by
    intro a haA
    obtain ⟨_, T, _, ⟨x, hx⟩, ht⟩ := (ha a).mp haA
    obtain ⟨p, hp⟩ := I.total T x
    exact ⟨p, (ht p).mpr ⟨x, hx, hp⟩⟩) (by
    intro a haA b hbA hn ⟨p, hpa, hpb⟩
    obtain ⟨_, T, _, _, ht⟩ := (ha a).mp haA
    obtain ⟨_, V, _, _, hv⟩ := (ha b).mp hbA
    obtain ⟨x, _, hx⟩ := (ht p).mp hpa
    obtain ⟨y, _, hy⟩ := (hv p).mp hpb
    obtain ⟨rfl, _⟩ := I.injective hx hy
    exact hn (h.1.eq_of_same_members a b (fun q => (ht q).trans (hv q).symm)))
  refine ⟨C, fun T hT hn => ?_⟩
  obtain ⟨a, ht⟩ := ZF.exists_cartesianRow hZF I T T
  have htP := (hP T).mpr hT
  have haA : M.mem a A := (ha a).mpr ⟨(hQ a).mpr (by
    intro p hp
    obtain ⟨x, hx, hc⟩ := (ht p).mp hp
    exact (hX p).mpr ⟨T, htP, x, hT x hx, hc⟩), T, htP, hn, ht⟩
  obtain ⟨p, ⟨hpC, hpa⟩, hp⟩ := hC a haA
  obtain ⟨x, hx, hc⟩ := (ht p).mp hpa
  refine ⟨x, hx, ⟨p, hc, hpC⟩, fun y hy ⟨q, hq, hqC⟩ => ?_⟩
  have he := hp q ⟨hqC, (ht q).mpr ⟨y, hy, hq⟩⟩
  exact (I.injective (he ▸ hq) hc).2

section Syntax
omit h

def Rem_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S F T : M.Domain) : Prop :=
  ∀ x, M.mem x T ↔ M.mem x S ∧ ¬ ∃ i, M.PairMember I i x F

def rem_m (𝒞 : OrderedPairConvention) {n} (S F T : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest T.weaken) (.conj (.mem .newest S.weaken)
    (.neg (.existsE (Formula.orderedPairMem 𝒞 .newest (.bound 1) F.weaken.weaken)))))
derive_free_closed rem_m

theorem rem_sat_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    {n} (ρ : Env M n) (S F T : Term n) :
    Formula.satisfies ρ (rem_m 𝒞 S F T) ↔ Rem_d I (S.eval ρ) (F.eval ρ) (T.eval ρ) := by
  simp only [rem_m, Rem_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

def Enum_step_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S C a F x : M.Domain) : Prop :=
  ∃ T, Rem_d I S F T ∧ ((M.mem x T ∧ M.PairMember I T x C) ∨ ((∀ y, ¬ M.mem y T) ∧ x = a))

def enum_step_m (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE (.conj (rem_m 𝒞 (.bound 5) (.bound 2) .newest)
    (.disj (.conj (.mem (.bound 1) .newest) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4)))
      (.conj (.forallE (.neg (.mem .newest (.bound 1)))) (Formula.extensionalEq (.bound 1) (.bound 3)))))

theorem enum_step_sat_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) (ρ : Env M 3) (F x : M.Domain) :
    (enum_step_m 𝒞).denote ρ F x ↔ Enum_step_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) F x := by
  simp only [enum_step_m, BinarySchema.denote, Enum_step_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, rem_sat_l I,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE]
  rfl

end Syntax

/-- 每个集合是某个内部序数的集合编码满射像；空集也由零长度枚举统一处理。 -/
theorem ordinal_enum_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ κ F, M.IsOrdinal κ ∧ M.IsSetFunctionFromTo I F κ S ∧ M.IsSetSurjectiveOnto I F κ S := by
  classical
  let hZF := models_zf_l h
  by_cases hn : ∃ a, M.mem a S
  · obtain ⟨a, ha⟩ := hn
    obtain ⟨C, hC⟩ := selector_l h I S
    let ρ : Env M 3 := ((⟨fun _ => S, fun _ => S⟩ : Env M 1).push C).push a
    have hs F x : (enum_step_m 𝒞).denote ρ F x ↔ Enum_step_d I S C a F x :=
      enum_step_sat_l I h.1 ρ F x
    have hop : M.IsClassFunctionOnTransfiniteSequences I ((enum_step_m 𝒞).denote ρ) := by
      intro F _
      let φ : UnarySchema 1 := {
        body := .neg (.existsE (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 2))) }
      obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ (⟨fun _ => F, fun _ => F⟩ : Env M 1) S
      have ht : Rem_d I S F T := by
        intro x
        rw [hT x]
        simp only [φ, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
          Formula.satisfies_orderedPairMem_iff I]
        rfl
      have hu {V} (hv : Rem_d I S F V) : V = T :=
        h.1.eq_of_same_members V T (fun x => (hv x).trans (ht x).symm)
      by_cases hn : ∃ x, M.mem x T
      · obtain ⟨x, hx, hc, he⟩ := hC T (fun x hx => ((ht x).mp hx).1) hn
        refine ⟨x, (hs F x).mpr ⟨T, ht, Or.inl ⟨hx, hc⟩⟩, fun y hy => ?_⟩
        obtain ⟨V, hv, hy⟩ := (hs F y).mp hy
        have := hu hv; subst V
        exact hy.elim (fun hy => he y hy.1 hy.2) (fun hy => False.elim (hy.1 x hx))
      · refine ⟨a, (hs F a).mpr ⟨T, ht, Or.inr ⟨fun x hx => hn ⟨x, hx⟩, rfl⟩⟩,
          fun y hy => ?_⟩
        obtain ⟨V, hv, hy⟩ := (hs F y).mp hy
        have := hu hv; subst V
        exact hy.elim (fun hy => False.elim (hn ⟨y, hy.1⟩)) And.right
    obtain ⟨κ, hκ⟩ := ZF.exists_hartogsNumber hZF I S
    obtain ⟨F, hF⟩ := ZF.recursiveSequence_exists hZF I ρ (enum_step_m 𝒞) hop hκ.1
    have step i x (hi : M.PairMember I i x F) :
        ∃ f, M.IsRestrictionOf I f F i ∧ Enum_step_d I S C a f x := by
      obtain ⟨f, hf, hx⟩ := hF.2 i ((hF.1.2.2 i).mpr ⟨x, hi⟩) x hi
      exact ⟨f, hf, (hs f x).mp hx⟩
    have hf : M.IsSetFunctionFromTo I F κ S := by
      refine ⟨hF.1.2.1, hF.1.2.2, fun i hi => ?_⟩
      obtain ⟨x, hx⟩ := (hF.1.2.2 i).mp hi
      obtain ⟨f, _, T, ht, hx'⟩ := step i x hx
      refine ⟨x, ?_, hx⟩
      exact hx'.elim (fun k => ((ht x).mp k.1).1) (fun k => k.2 ▸ ha)
    refine ⟨κ, F, hκ.1, hf, ?_⟩
    apply Classical.byContradiction
    intro hn
    apply hκ.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    refine ⟨F, hf, fun i j x hi hj => ?_⟩
    have impossible {i j x} (hi : M.PairMember I i x F) (hj : M.PairMember I j x F)
        (hij : M.mem i j) : False := by
      obtain ⟨f, hf', T, ht, hx⟩ := step j x hj
      rcases hx with hx | hx
      · exact ((ht x).mp hx.1).2 ⟨i, (hf'.2 i x).mpr ⟨hij, hi⟩⟩
      · apply hn
        intro y hy
        by_cases hmem : ∃ i, M.PairMember I i y F
        · obtain ⟨i, hi⟩ := hmem
          exact ⟨i, hf.input_mem_of_pairMember hi, hi⟩
        · exact False.elim (hx.1 y ((ht y).mpr ⟨hy, fun ⟨i, hi⟩ => hmem ⟨i, ((hf'.2 i y).mp hi).2⟩⟩))
    rcases hκ.1.wellOrder.linear.compare i (hf.input_mem_of_pairMember hi)
        j (hf.input_mem_of_pairMember hj) with he | hij | hji
    · exact h.1.eq_of_same_members i j he
    · exact False.elim (impossible hi hj hij)
    · exact False.elim (impossible hj hi hji)
  · obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have ht := Structure.IsSequenceOfLength.empty I he
    exact ⟨e, e, ht.1, ⟨ht.2.1, ht.2.2, fun i hi => False.elim (he i hi)⟩,
      fun x hx => False.elim (hn ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.ZFC
