import YesMetaZFC.Model.Forcing.CCC.Basic
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 参数化 Cohen 偏序的原公式规格

偏序的有限函数条件、反向包含关系及二元值集均由实际原公式定义。
同一规格用于模型内构造及后继名称装配，不依赖预先选取的泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def fn_order_m {n} (ω X Y Q D : Term n) : Formula 1 n :=
  .conj (.forallE (.iff (.mem .newest Q.weaken)
    (fn_m kpair_convention_l ω.weaken X.weaken Y.weaken .newest)))
    (.conj (Formula.isRelation kpair_convention_l D) (.forallE (.forallE (.iff (entry_m (.bound 1) .newest D.weaken.weaken)
      (.conj (.mem (.bound 1) Q.weaken.weaken)
        (.conj (.mem .newest Q.weaken.weaken) (Formula.subset .newest (.bound 1))))))))
derive_free_closed fn_order_m

def Cohen_spec_d {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (κ Q D : M.Domain) : Prop :=
  ∃ ω o l Y X, M.IsOmega ω ∧ (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf l o ∧ Pair_d M Y o l ∧
    M.IsCartesianProduct I X κ ω ∧ (∀ p, M.mem p Q ↔ Fn_d I ω X Y p) ∧
    (∀ v, M.mem v D → ∃ p q, KPair_d M v p q) ∧
    ∀ p q, Entry_d M p q D ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p

def cohen_m {n} (κ Q D : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (Formula.isOmega (.bound 4))
      (.conj (Formula.isEmpty (.bound 3))
        (.conj (Formula.isSuccessor (.bound 2) (.bound 3))
          (.conj (Formula.isUnorderedPair (.bound 1) (.bound 3) (.bound 2))
            (.conj (Formula.isCartesianProduct kpair_convention_l .newest
              κ.weaken.weaken.weaken.weaken.weaken (.bound 4))
              (fn_order_m (.bound 4) .newest (.bound 1)
                Q.weaken.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed cohen_m

variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem fn_order_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X Y Q D : Term n) :
    Formula.satisfies ρ (fn_order_m ω X Y Q D) ↔
      (∀ p, M.mem p (Q.eval ρ) ↔ Fn_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) p) ∧
      (∀ v, M.mem v (D.eval ρ) → ∃ p q, KPair_d M v p q) ∧
      ∀ p q, Entry_d M p q (D.eval ρ) ↔
        M.mem p (Q.eval ρ) ∧ M.mem q (Q.eval ρ) ∧ M.MemberSubset q p := by
  have graph {k} (η : Env M k) (D : Term k) :
      Formula.satisfies η (Formula.isRelation kpair_convention_l D) ↔
        ∀ v, M.mem v (D.eval η) → ∃ p q, KPair_d M v p q := by
    simp only [Formula.isRelation, kpair_convention_l, Formula.satisfies_forallMem_iff,
      Formula.satisfies_exists_iff, kpair_sat_l M hE]
    rfl
  simp only [fn_order_m, graph, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn_sat_l I hE,
    entry_sat_l M hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  rfl

theorem cohen_sat_l (hE : Extensional M) {n} (ρ : Env M n) (κ Q D : Term n) :
    Formula.satisfies ρ (cohen_m κ Q D) ↔ Cohen_spec_d I (κ.eval ρ) (Q.eval ρ) (D.eval ρ) := by
  have pair {k} (η : Env M k) (Y o l : Term k) :
      Formula.satisfies η (Formula.isUnorderedPair Y o l) ↔ Pair_d M (Y.eval η) (o.eval η) (l.eval η) := by
    simp only [Formula.isUnorderedPair, Pair_d, Formula.satisfies_forall_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest,
      Definitional.Term.eval_weaken]
  simp only [cohen_m, Cohen_spec_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_isSuccessor_iff,
    pair, Formula.satisfies_isCartesianProduct_iff I, fn_order_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 原 ZF 已足以构造全部 Cohen 条件与序关系，选择公理仅用于其 CCC 结论。 -/
theorem cohen_spec_exists_l (hZF : M.Models ZF) (κ : M.Domain) :
    ∃ Q D, Cohen_spec_d I κ Q D := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨o, ho, _⟩ := hω.1.1
  obtain ⟨l, hl⟩ := KP.exists_successor (ZF.modelsKP hZF) o
  obtain ⟨Y, hY⟩ := KP.exists_pair (ZF.modelsKP hZF) o l
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I κ ω
  obtain ⟨Q, hQ⟩ := ZF.fn_set_l I hZF ω X Y
  obtain ⟨D, hD, _, hGraph⟩ := subset_order_l M hZF Q
  exact ⟨Q, D, ω, o, l, Y, X, hω, ho, hl, hY, hX, hQ, hGraph, hD⟩

/-- 规格直接给出非空预序；空函数是最大条件。 -/
theorem cohen_spec_top_l (hZF : M.Models ZF) {κ Q D} (h : Cohen_spec_d I κ Q D) :
    Preord_d M Q D ∧ ∃ o, M.mem o Q ∧ ∀ p, M.mem p Q → Entry_d M p o D := by
  obtain ⟨ω, o, l, Y, X, hω, ho, _, _, _, hQ, _, hD⟩ := h
  have hoQ := (hQ o).mpr (ZF.fn_empty_l I hZF hω ho)
  refine ⟨⟨fun p hp => (hD p p).mpr ⟨hp, hp, fun _ h => h⟩, ?_⟩,
    o, hoQ, fun p hp => (hD p o).mpr ⟨hp, hoQ, fun a ha => False.elim (ho a ha)⟩⟩
  intro p q r hp hq hr hpq hqr
  exact (hD p r).mpr ⟨hp, hr, fun a ha => ((hD p q).mp hpq).2.2 a (((hD q r).mp hqr).2.2 a ha)⟩

/-- 固定添加量后，Cohen 条件集和完整关系图唯一；只需外延性。 -/
theorem cohen_spec_unique_l (hE : Extensional M) {κ Q D Q' D'}
    (h : Cohen_spec_d I κ Q D) (h' : Cohen_spec_d I κ Q' D') : Q = Q' ∧ D = D' := by
  obtain ⟨ω, o, l, Y, X, hω, ho, hl, hY, hX, hQ, hG, hD⟩ := h
  obtain ⟨ω', o', l', Y', X', hω', ho', hl', hY', hX', hQ', hG', hD'⟩ := h'
  have he := hE.eq_of_same_members ω ω' (fun x => ⟨hω.2 ω' hω'.1 x, hω'.2 ω hω.1 x⟩)
  subst ω'
  have he := hE.eq_of_same_members o o' (fun x => iff_of_false (ho x) (ho' x))
  subst o'
  have he := hE.eq_of_same_members l l' (fun x => (hl x).trans (hl' x).symm)
  subst l'
  have he := hE.eq_of_same_members Y Y' (fun x => (hY x).trans (hY' x).symm)
  subst Y'
  have he := hE.eq_of_same_members X X' (fun x => (hX x).trans (hX' x).symm)
  subst X'
  have he := hE.eq_of_same_members Q Q' (fun x => (hQ x).trans (hQ' x).symm)
  subst Q'
  exact ⟨rfl, entry_ext_l M hE hG hG' (fun p q => (hD p q).trans (hD' p q).symm)⟩

theorem cohen_spec_top_unique_l (hE : Extensional M) {κ Q D s t} (h : Cohen_spec_d I κ Q D)
    (hs : M.mem s Q ∧ ∀ p, M.mem p Q → Entry_d M p s D)
    (ht : M.mem t Q ∧ ∀ p, M.mem p Q → Entry_d M p t D) : s = t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hD⟩ := h
  exact hE.eq_of_same_members s t (fun x =>
    ⟨((hD t s).mp (hs.2 t ht.1)).2.2 x, ((hD s t).mp (ht.2 s hs.1)).2.2 x⟩)

end YesMetaZFC.Model.Forcing.Internal
