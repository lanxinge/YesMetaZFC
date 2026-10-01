import YesMetaZFC.Model.Forcing.Closed.Basic
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.PartialFunction

/-! # 地模型内部的可数部分函数塌缩

条件是源集 X 到目标集 Y 的可数部分函数，增强关系为函数图的反向包含。
可数性、函数图、条件集以及序关系都在地模型内部定义。递降 ω 链的并给出
实际下界；此闭性仅量化模型内的序列，不能用于任意外部可数链。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Coll_d (ω X Y p : M.Domain) : Prop := M.IsSetFunction I p ∧
  (∀ x y, M.PairMember I x y p → M.mem x X ∧ M.mem y Y) ∧ M.CardinalLessOrEqual I p ω

def coll_m (𝒞 : OrderedPairConvention) {n} (ω X Y p : Term n) : Formula 1 n :=
  .conj (Formula.isFunction 𝒞 p) (.conj (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.mem .newest Y.weaken.weaken)))))
    (Formula.cardinalLessOrEqual 𝒞 p ω))
derive_free_closed coll_m

theorem coll_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X Y p : Term n) :
    Formula.satisfies ρ (coll_m 𝒞 ω X Y p) ↔ Coll_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (p.eval ρ) := by
  simp only [coll_m, Coll_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem coll_set_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ B, ∀ p, M.mem p B ↔ Coll_d I ω X Y p := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I X Y
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := { body := coll_m 𝒞 (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ K
  have hφ p : φ.denote ρ p ↔ Coll_d I ω X Y p :=
    coll_sat_l I hZF.1 (ρ.push p) (.bound 3) (.bound 2) (.bound 1) .newest
  refine ⟨B, fun p => (hB p).trans ?_⟩
  change (M.mem p K ∧ φ.denote ρ p) ↔ _
  rw [hφ]
  refine ⟨And.right, fun hp => ⟨(hK p).mpr ?_, hp⟩⟩
  intro q hq
  obtain ⟨x, y, hcode⟩ := hp.1.1 q hq
  have hxy := hp.2.1 x y ⟨q, hcode, hq⟩
  exact (hP q).mpr ⟨x, hxy.1, y, hxy.2, hcode⟩

theorem coll_empty_l {ω X Y e} (he : ∀ x, ¬ M.mem x e) : Coll_d I ω X Y e := by
  have hseq := SetTheory.Structure.IsSequenceOfLength.empty I he
  refine ⟨hseq.2.1, fun x y ⟨p, _, hp⟩ => False.elim (he p hp), e,
    ⟨hseq.2.1, hseq.2.2, fun x hx => False.elim (he x hx)⟩, ?_⟩
  exact fun x y z ⟨p, _, hp⟩ _ => False.elim (he p hp)

/-- 模型内 ω 链的并仍是可数部分函数。 -/
theorem coll_union_l (hZFC : M.Models ZFC) {ω X Y B f} (hω : M.IsOmega ω)
    (hB : ∀ p, M.mem p B ↔ Coll_d I ω X Y p)
    (hf : M.IsSetFunctionFromTo I f ω B)
    (hd : ∀ i j p q, M.mem i j → M.PairMember I i p f → M.PairMember I j q f → M.MemberSubset p q) :
    ∃ q, M.mem q B ∧ ∀ i p, M.PairMember I i p f → M.MemberSubset p q := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  obtain ⟨q, hq⟩ := KP.exists_union (ZF.modelsKP hZF) A
  have ha {p} (hp : M.mem p A) : Coll_d I ω X Y p := by
    obtain ⟨i, hi⟩ := (hA p).mp hp
    exact (hB p).mp (hf.output_mem_of_pairMember hi)
  have hs {i p} (hp : M.PairMember I i p f) : M.MemberSubset p q :=
    fun x hx => (hq x).mpr ⟨p, (hA p).mpr ⟨i, hp⟩, hx⟩
  have hcA : M.CardinalLessOrEqual I A ω := ZFC.surjection_bound_l I hZFC
    ⟨hf.1, hf.2.1, fun i hi => by
      obtain ⟨p, _, hp⟩ := hf.2.2 i hi
      exact ⟨p, (hA p).mpr ⟨i, hp⟩, hp⟩⟩
    (fun p hp => by
      obtain ⟨i, hi⟩ := (hA p).mp hp
      exact ⟨i, hf.input_mem_of_pairMember hi, hi⟩)
  have hc := ZFC.countable_union_l I hZFC hω hcA hq (fun _ hp => (ha hp).2.2)
  refine ⟨q, (hB q).mpr ⟨⟨?_, ?_⟩, ?_, hc⟩, fun _ _ hp => hs hp⟩
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := (hq x).mp hx
    exact (ha hp).1.1 x hxp
  · rintro x y z ⟨v, hv, hvq⟩ ⟨w, hw, hwq⟩
    obtain ⟨p, hp, hvp⟩ := (hq v).mp hvq
    obtain ⟨r, hr, hwr⟩ := (hq w).mp hwq
    obtain ⟨i, hi⟩ := (hA p).mp hp
    obtain ⟨j, hj⟩ := (hA r).mp hr
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare i (hf.input_mem_of_pairMember hi)
        j (hf.input_mem_of_pairMember hj) with he | hij | hji
    · have he := hZF.1.eq_of_same_members i j he
      subst j
      have he := hf.1.2 i p r hi hj
      subst r
      exact (ha hp).1.2 x y z ⟨v, hv, hvp⟩ ⟨w, hw, hwr⟩
    · exact (ha hr).1.2 x y z ⟨v, hv, hd i j p r hij hi hj v hvp⟩ ⟨w, hw, hwr⟩
    · exact (ha hp).1.2 x y z ⟨v, hv, hvp⟩ ⟨w, hw, hd j i r p hji hj hi w hwr⟩
  · rintro x y ⟨v, hv, hvq⟩
    obtain ⟨p, hp, hvp⟩ := (hq v).mp hvq
    exact (ha hp).2.1 x y ⟨v, hv, hvp⟩

/-- 给定尚未使用的坐标，可以指定任意目标值并保持条件性。 -/
theorem coll_extend_l (hZF : M.Models ZF) {ω X Y p x y} (hω : M.IsOmega ω)
    (hp : Coll_d I ω X Y p) (hx : M.mem x X) (hy : M.mem y Y)
    (hn : ¬ ∃ z, M.PairMember I x z p) :
    ∃ q, Coll_d I ω X Y q ∧ M.MemberSubset p q ∧ M.PairMember I x y q := by
  obtain ⟨q, v, _, hq, hqf, hxy⟩ := ZF.pfn_insert_l I hZF ⟨hp.1, hp.2.1⟩ hx hy hn
  exact ⟨q, ⟨hqf.1, hqf.2, ZF.countable_insert_l I hZF hω hp.2.2 hq⟩,
    fun w hw => (hq w).mpr (Or.inl hw), hxy⟩

/-- 不可数源集中总有一个尚未使用的坐标。 -/
theorem coll_fresh_l (hZF : M.Models ZF) {ω X Y p} (hp : Coll_d I ω X Y p)
    (hX : ¬ M.CardinalLessOrEqual I X ω) : ∃ x, M.mem x X ∧ ¬ ∃ y, M.PairMember I x y p := by
  classical
  apply Classical.byContradiction
  intro hn
  have ht x (hx : M.mem x X) : ∃ y, M.PairMember I x y p := by
    apply Classical.byContradiction
    exact fun h => hn ⟨x, hx, h⟩
  let ρ : Env M 1 := ⟨fun _ => p, fun _ => p⟩
  let φ : BinarySchema 1 := {
    body := .conj (.mem .newest (.bound 2)) (.existsE (𝒞.code (.bound 1) (.bound 2) .newest)) }
  have hφ x q : φ.denote ρ x q ↔ M.mem q p ∧ ∃ y, I.Codes q x y := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, I.satisfies_code_iff]
    rfl
  obtain ⟨F, hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ (source := X) (target := p) (by
    intro x hx
    obtain ⟨y, q, hq, hqp⟩ := ht x hx
    exact ⟨q, (hφ x q).mpr ⟨hqp, y, hq⟩⟩) (by
    intro x _ q r hq hr
    obtain ⟨hqp, y, hq⟩ := (hφ x q).mp hq
    obtain ⟨hrp, z, hr⟩ := (hφ x r).mp hr
    have he := hp.1.2 x y z ⟨q, hq, hqp⟩ ⟨r, hr, hrp⟩
    subst z
    exact I.unique hq hr) (fun x q _ hq => ((hφ x q).mp hq).1) (by
    intro x y q _ _ hx hy
    obtain ⟨_, a, hx⟩ := (hφ x q).mp hx
    obtain ⟨_, b, hy⟩ := (hφ y q).mp hy
    exact (I.injective hx hy).1)
  obtain ⟨G, hG⟩ := hp.2.2
  exact hX (ZF.exists_compositionInjection hZF I hF hG)

variable (M : SetTheory.Structure.{u})

/-- 实际条件集和反向包含序；B 本身由基础公理保证不在 B 中，作为排除值。 -/
theorem collapse_order_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X Y p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧
    Cond_order_d M B R B := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, hB⟩ := coll_set_l I hZF ω X Y
  obtain ⟨R, hR, hO, _⟩ := subset_order_l M hZF B
  exact ⟨B, R, hB, hR, hO⟩

/-- 可数部分函数塌缩具有已实现的模型内部可数闭性。 -/
theorem collapse_closed_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω) (X Y : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω X Y p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧
    Cond_order_d M B R B ∧ Closed_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R B ω := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, R, hB, hR, O⟩ := collapse_order_l M hZF ω X Y
  refine ⟨B, R, hB, hR, O, fun f hf => ?_⟩
  obtain ⟨q, hq, hqs⟩ := coll_union_l J hZFC hω hB hf.1 (fun i j p q hij hip hjq =>
    ((hR q p).mp (chain_lower_l O hZF hω hf i j p q hij hip hjq)).2.2)
  refine ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hq), fun i p hip => ?_⟩
  exact (hR q p).mpr ⟨hq, hf.1.output_mem_of_pairMember hip, hqs i p hip⟩

end YesMetaZFC.Model.Forcing.Internal
