import YesMetaZFC.Model.Forcing.Iteration.Condition.Operations

/-! # 有限支撑与可数支撑的共同封闭接口

false 表示有限支撑，true 表示可数支撑；大小判断施加于实际定义域集合。
两类支撑的限制和单坐标追加都只需要原 ZF，毋须可数选择。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Supp_size_d (k : Bool) (ω D : M.Domain) : Prop := if k then M.CardinalLessOrEqual I D ω else Finite_d I ω D

def Row_supp_d (k : Bool) (ω p : M.Domain) : Prop := ∃ D, Coord_d M p D ∧ Supp_size_d I k ω D

def supp_size_m (𝒞 : OrderedPairConvention) (k : Bool) {n} (ω D : Term n) : Formula 1 n :=
  if k then Formula.cardinalLessOrEqual 𝒞 D ω else finite_m 𝒞 ω D
@[simp] theorem supp_size_m_freeClosed (𝒞 : OrderedPairConvention) (k : Bool) {n} (ω D : Term n)
    (hω : ω.freeSupport = []) (hD : D.freeSupport = []) : (supp_size_m 𝒞 k ω D).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [supp_size_m, hω, hD]

def row_supp_m (𝒞 : OrderedPairConvention) (k : Bool) {n} (ω p : Term n) : Formula 1 n :=
  .existsE (.conj (coord_m p.weaken .newest) (supp_size_m 𝒞 k ω.weaken .newest))
derive_free_closed row_supp_m

theorem supp_size_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (ω D : Term n) :
    Formula.satisfies ρ (supp_size_m 𝒞 k ω D) ↔ Supp_size_d I k (ω.eval ρ) (D.eval ρ) := by
  cases k <;> simp only [supp_size_m, Supp_size_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, finite_sat_l I hE]

theorem row_supp_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (ω p : Term n) :
    Formula.satisfies ρ (row_supp_m 𝒞 k ω p) ↔ Row_supp_d I k (ω.eval ρ) (p.eval ρ) := by
  simp only [row_supp_m, Row_supp_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    coord_sat_l M hE, supp_size_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem supp_size_subset_l (hZF : M.Models ZF) {k ω D E} (hD : Supp_size_d I k ω D)
    (hED : M.MemberSubset E D) : Supp_size_d I k ω E := by
  cases k with
  | false => exact ZF.finite_subset_l I hZF hD hED
  | true =>
    obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I hED
    obtain ⟨g, hg⟩ := hD
    exact ZF.exists_compositionInjection hZF I hf hg

theorem row_supp_empty_l (hZF : M.Models ZF) {ω e} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (k : Bool) :
    Row_supp_d I k ω e := by
  have hd : Coord_d M e e := fun i => ⟨fun hi => False.elim (he i hi),
    fun ⟨s, v, _, hv⟩ => False.elim (he v hv)⟩
  refine ⟨e, hd, ?_⟩
  cases k with
  | false => exact ZF.finite_empty_l I hZF hω he
  | true => exact ZF.finite_countable_l I hZF hω (ZF.finite_empty_l I hZF hω he)

/-- 追加后的支撑是原支撑，或原支撑添加当前索引。 -/
theorem row_append_supp_l (hZF : M.Models ZF) {k ω α t p s q} (hω : M.IsOmega ω)
    (hp : Row_supp_d I k ω p) (h : Row_append_d M α t p s q) : Row_supp_d I k ω q := by
  rcases h with ⟨_, rfl⟩ | ⟨hs, v, hv, hq⟩
  · exact hp
  · obtain ⟨D, hD, hd⟩ := hp
    obtain ⟨E, hE⟩ := KP.exists_insert (ZF.modelsKP hZF) D α
    have hh : Row_append_d M α t p s q := Or.inr ⟨hs, v, hv, hq⟩
    have he : Coord_d M q E := by
      intro i
      rw [hE i]
      constructor
      · rintro (hi | hi)
        · obtain ⟨a, ha⟩ := (hD i).mp hi
          exact ⟨a, (row_append_entry_l M hh i a).mpr (Or.inl ha)⟩
        · subst i
          exact ⟨s, (row_append_entry_l M hh α s).mpr (Or.inr ⟨hs, rfl, rfl⟩)⟩
      · rintro ⟨a, ha⟩
        exact ((row_append_entry_l M hh i a).mp ha).elim (fun hi => Or.inl ((hD i).mpr ⟨a, hi⟩)) (fun hi => Or.inr hi.2.1)
    refine ⟨E, he, ?_⟩
    cases k with
    | false => exact ZF.finite_insert_l I hZF hω hd hE
    | true => exact ZF.countable_insert_l I hZF hω hd hE

theorem row_restrict_supp_l (hZF : M.Models ZF) {k ω p q β}
    (hp : Row_supp_d I k ω p) (hq : M.IsRestrictionOf
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) q p β) : Row_supp_d I k ω q := by
  obtain ⟨D, hD, hd⟩ := hp
  obtain ⟨E, hE⟩ := coord_exists_l M hZF q
  refine ⟨E, hE, supp_size_subset_l I hZF hd (fun i hi => ?_)⟩
  obtain ⟨s, his⟩ := (hE i).mp hi
  exact (hD i).mpr ⟨s, ((hq.2 i s).mp his).2⟩

end YesMetaZFC.Model.Forcing.Internal
