import YesMetaZFC.SetTheory.Card.Finite
import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 内部有限部分函数

源集、值集与有限性均为地模型对象。相容性是公共定义域上的一致；并图、添值与
删除图都实际构造为模型中的集合，供任意坐标集的 Cohen 力迫复用。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pfn_d (X Y p : M.Domain) : Prop := M.IsSetFunction I p ∧
  ∀ x y, M.PairMember I x y p → M.mem x X ∧ M.mem y Y

def Fn_d (ω X Y p : M.Domain) : Prop := Pfn_d I X Y p ∧ Finite_d I ω p

def Agree_d (p q : M.Domain) : Prop :=
  ∀ x y z, M.PairMember I x y p → M.PairMember I x z q → y = z

def pfn_m (𝒞 : OrderedPairConvention) {n} (X Y p : Term n) : Formula 1 n :=
  .conj (Formula.isFunction 𝒞 p) (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.mem .newest Y.weaken.weaken)))))
derive_free_closed pfn_m

def fn_m (𝒞 : OrderedPairConvention) {n} (ω X Y p : Term n) : Formula 1 n :=
  .conj (pfn_m 𝒞 X Y p) (finite_m 𝒞 ω p)
derive_free_closed fn_m

def agree_m (𝒞 : OrderedPairConvention) {n} (p q : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) p.weaken.weaken.weaken)
    (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest q.weaken.weaken.weaken)
      (Formula.extensionalEq (.bound 1) .newest)))))
derive_free_closed agree_m

theorem pfn_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X Y p : Term n) :
    Formula.satisfies ρ (pfn_m 𝒞 X Y p) ↔ Pfn_d I (X.eval ρ) (Y.eval ρ) (p.eval ρ) := by
  simp only [pfn_m, Pfn_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

theorem fn_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X Y p : Term n) :
    Formula.satisfies ρ (fn_m 𝒞 ω X Y p) ↔ Fn_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (p.eval ρ) := by
  simp only [fn_m, Fn_d, Formula.satisfies_conj_iff, pfn_sat_l I hE, finite_sat_l I hE]

theorem agree_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p q : Term n) :
    Formula.satisfies ρ (agree_m 𝒞 p q) ↔ Agree_d I (p.eval ρ) (q.eval ρ) := by
  simp only [agree_m, Agree_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_two_push, Term.eval_bound_one_push, Term.eval_bound_zero_push]

theorem pfn_subset_l {X Y p q} (hp : Pfn_d I X Y p) (hq : M.MemberSubset q p) : Pfn_d I X Y q := by
  have he {x y} (h : M.PairMember I x y q) : M.PairMember I x y p := h.elim fun a ha => ⟨a, ha.1, hq a ha.2⟩
  exact ⟨⟨fun a ha => hp.1.1 a (hq a ha), fun x y z hy hz => hp.1.2 x y z (he hy) (he hz)⟩,
    fun x y h => hp.2 x y (he h)⟩

/-- 两张函数图具有同一条目，删去该条目后的一致性可还原。 -/
theorem agree_restore_l {p q r s a x y} (ha : I.Codes a x y)
    (hp : M.IsSetFunction I p) (hq : M.IsSetFunction I q) (hap : M.mem a p) (haq : M.mem a q)
    (hr : ∀ v, M.mem v r ↔ M.mem v p ∧ v ≠ a)
    (hs : ∀ v, M.mem v s ↔ M.mem v q ∧ v ≠ a) (h : Agree_d I r s) : Agree_d I p q := by
  intro i j k hij hik
  classical
  by_cases he : i = x
  · subst i
    exact (hp.2 x j y hij ⟨a, ha, hap⟩).trans (hq.2 x k y hik ⟨a, ha, haq⟩).symm
  · obtain ⟨b, hb, hbp⟩ := hij
    obtain ⟨c, hc, hcq⟩ := hik
    exact h i j k ⟨b, hb, (hr b).mpr ⟨hbp, fun e => he (I.injective (e ▸ hb) ha).1⟩⟩
      ⟨c, hc, (hs c).mpr ⟨hcq, fun e => he (I.injective (e ▸ hc) ha).1⟩⟩

namespace ZF
variable (hZF : M.Models ZF)
include hZF

theorem fn_set_l (ω X Y : M.Domain) : ∃ B, ∀ p, M.mem p B ↔ Fn_d I ω X Y p := by
  obtain ⟨P, hP⟩ := exists_cartesianProduct hZF I X Y
  obtain ⟨K, hK⟩ := exists_powerSet hZF P
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := { body := fn_m 𝒞 (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := separation_exists_d hZF φ ρ K
  refine ⟨B, fun p => (hB p).trans ?_⟩
  rw [fn_sat_l I hZF.1]
  refine ⟨And.right, fun h => ⟨(hK p).mpr ?_, h⟩⟩
  intro a ha
  obtain ⟨x, y, hxy⟩ := h.1.1.1 a ha
  have hb := h.1.2 x y ⟨a, hxy, ha⟩
  exact (hP a).mpr ⟨x, hb.1, y, hb.2, hxy⟩

theorem fn_empty_l {ω X Y e} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) : Fn_d I ω X Y e :=
  ⟨⟨⟨fun x hx => False.elim (he x hx), fun _ _ _ h => False.elim (h.elim fun p hp => he p hp.2)⟩,
    fun _ _ h => False.elim (h.elim fun p hp => he p hp.2)⟩, finite_empty_l I hZF hω he⟩

theorem pfn_insert_l {X Y p x y} (hp : Pfn_d I X Y p) (hx : M.mem x X) (hy : M.mem y Y)
    (hn : ¬ ∃ z, M.PairMember I x z p) : ∃ q a, I.Codes a x y ∧
      (∀ v, M.mem v q ↔ M.mem v p ∨ v = a) ∧ Pfn_d I X Y q ∧ M.PairMember I x y q := by
  obtain ⟨a, ha⟩ := I.total x y
  obtain ⟨q, hq⟩ := KP.exists_insert (ZF.modelsKP hZF) p a
  have he i j : M.PairMember I i j q ↔ M.PairMember I i j p ∨ (i = x ∧ j = y) := by
    constructor
    · rintro ⟨v, hv, hvq⟩
      rcases (hq v).mp hvq with hvp | rfl
      · exact Or.inl ⟨v, hv, hvp⟩
      · exact Or.inr (I.injective hv ha)
    · rintro (⟨v, hv, hvp⟩ | ⟨rfl, rfl⟩)
      · exact ⟨v, hv, (hq v).mpr (Or.inl hvp)⟩
      · exact ⟨a, ha, (hq a).mpr (Or.inr rfl)⟩
  refine ⟨q, a, ha, hq, ⟨⟨?_, ?_⟩, ?_⟩, (he x y).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro v hv
    rcases (hq v).mp hv with hv | rfl
    · exact hp.1.1 v hv
    · exact ⟨x, y, ha⟩
  · intro i j k hj hk
    rcases (he i j).mp hj with hj | ⟨hix, hjy⟩ <;> rcases (he i k).mp hk with hk | ⟨hix', hky⟩
    · exact hp.1.2 i j k hj hk
    · exact False.elim (hn ⟨j, hix' ▸ hj⟩)
    · exact False.elim (hn ⟨k, hix ▸ hk⟩)
    · exact hjy.trans hky.symm
  · intro i j hij
    rcases (he i j).mp hij with hij | ⟨rfl, rfl⟩
    · exact hp.2 i j hij
    · exact ⟨hx, hy⟩

theorem fn_insert_l {ω X Y p x y} (hω : M.IsOmega ω) (hp : Fn_d I ω X Y p)
    (hx : M.mem x X) (hy : M.mem y Y) (hn : ¬ ∃ z, M.PairMember I x z p) :
    ∃ q, Fn_d I ω X Y q ∧ M.MemberSubset p q ∧ M.PairMember I x y q := by
  obtain ⟨q, a, _, hq, hpq, hxy⟩ := pfn_insert_l I hZF hp.1 hx hy hn
  exact ⟨q, ⟨hpq, finite_insert_l I hZF hω hp.2 hq⟩, fun v hv => (hq v).mpr (Or.inl hv), hxy⟩

theorem fn_union_l {ω X Y p q} (hω : M.IsOmega ω) (hp : Fn_d I ω X Y p) (hq : Fn_d I ω X Y q)
    (ha : Agree_d I p q) : ∃ r, Fn_d I ω X Y r ∧ M.MemberSubset p r ∧ M.MemberSubset q r := by
  obtain ⟨r, hr⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) p q
  have he x y : M.PairMember I x y r ↔ M.PairMember I x y p ∨ M.PairMember I x y q := by
    constructor
    · rintro ⟨v, hv, hvr⟩
      exact ((hr v).mp hvr).elim (fun h => Or.inl ⟨v, hv, h⟩) (fun h => Or.inr ⟨v, hv, h⟩)
    · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact ⟨v, hv, (hr v).mpr (Or.inl h)⟩
      · exact ⟨v, hv, (hr v).mpr (Or.inr h)⟩
  refine ⟨r, ⟨⟨⟨?_, ?_⟩, ?_⟩, finite_union_l I hZF hω hp.2 hq.2 hr⟩,
    fun v hv => (hr v).mpr (Or.inl hv), fun v hv => (hr v).mpr (Or.inr hv)⟩
  · intro v hv
    exact ((hr v).mp hv).elim (hp.1.1.1 v) (hq.1.1.1 v)
  · intro x y z hy hz
    rcases (he x y).mp hy with hy | hy <;> rcases (he x z).mp hz with hz | hz
    · exact hp.1.1.2 x y z hy hz
    · exact ha x y z hy hz
    · exact (ha x z y hz hy).symm
    · exact hq.1.1.2 x y z hy hz
  · intro x y hxy
    exact ((he x y).mp hxy).elim (hp.1.2 x y) (hq.1.2 x y)

end ZF

namespace ZFC

/-- 有限集不能命中每个自然数的互异纤维；一次返回未被有限支撑占用的指标。 -/
theorem finite_avoid_l (hZFC : M.Models ZFC) {ω S} (hω : M.IsOmega ω) (hS : Finite_d I ω S)
    {n} (φ : BinarySchema n) (ρ : Env M n)
    (hu : ∀ i j s, M.mem i ω → M.mem j ω → M.mem s S →
      φ.denote ρ i s → φ.denote ρ j s → i = j) :
    ∃ i, M.mem i ω ∧ ∀ s, M.mem s S → ¬ φ.denote ρ i s := by
  classical
  apply Classical.byContradiction
  intro hn
  have ht i (hi : M.mem i ω) : ∃ s, M.mem s S ∧ φ.denote ρ i s := by
    apply Classical.byContradiction
    intro h
    exact hn ⟨i, hi, fun s hs hφ => h ⟨s, hs, hφ⟩⟩
  obtain ⟨f, hf, he⟩ := uniformize_formula_l I hZFC φ ρ ht
  have hi : M.IsSetInjectionFromTo I f ω S := ⟨hf, fun i j s his hjs =>
    hu i j s (hf.input_mem_of_pairMember his) (hf.input_mem_of_pairMember hjs)
      (hf.output_mem_of_pairMember his) (he i s his) (he j s hjs)⟩
  obtain ⟨k, hk, g, hg⟩ := hS
  exact ZF.omega_not_le_finite_l I (models_zf_l hZFC) hω k hk
    (ZF.exists_compositionInjection (models_zf_l hZFC) I hi hg)

end ZFC
end YesMetaZFC.SetTheory
