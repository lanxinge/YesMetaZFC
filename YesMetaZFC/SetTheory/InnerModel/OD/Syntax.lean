import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Internal.CanonicalCode
import YesMetaZFC.SetTheory.Cumulative

/-! # 内部序数可定义性的公式

定义码为 (层高度，公式自然数码，有限序数参数列的规范码)。量化的公式、长度、
序列和满足表全部属于原模型；候选值占零号变量，列外赋值固定为空集。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Od_local_d (ω X e a s x : M.Domain) : Prop :=
  Ssk_mem_d I ω X e a e s x ∧ ∀ y, Ssk_mem_d I ω X e a e s y → y = x

def od_local_m {d} (ω X e a s x : Term d) : Formula 1 d :=
  .conj (ssk_mem_m (𝒞 := 𝒞) ω X e a e s x) (.forallE (.imp
    (ssk_mem_m (𝒞 := 𝒞) ω.weaken X.weaken e.weaken a.weaken e.weaken s.weaken .newest)
    (Formula.extensionalEq .newest x.weaken)))
derive_free_closed od_local_m

theorem od_local_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X e a s x : Term d) :
    Formula.satisfies ρ (od_local_m (𝒞 := 𝒞) ω X e a s x) ↔
      Od_local_d I (ω.eval ρ) (X.eval ρ) (e.eval ρ) (a.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [od_local_m, Od_local_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, ssk_mem_sat_l I hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Od_code_d (θ z p x : M.Domain) : Prop := ∃ ω X e a s,
  M.IsOmega ω ∧ V_d I θ X ∧ (∀ y, ¬ M.mem y e) ∧ M.mem e X ∧
    Sc_num_d I ω a z ∧ Oc_seq_d I ω s p ∧ Od_local_d I ω X e a s x

def od_code_m {d} (θ z p x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (Formula.isOmega (.bound 4)) (.conj (v_m 𝒞 θ.weaken.weaken.weaken.weaken.weaken (.bound 3))
    (.conj (Formula.isEmpty (.bound 2)) (.conj (.mem (.bound 2) (.bound 3))
    (.conj (sc_num_m (𝒞 := 𝒞) (.bound 4) (.bound 1) z.weaken.weaken.weaken.weaken.weaken)
    (.conj (oc_seq_m (𝒞 := 𝒞) (.bound 4) .newest p.weaken.weaken.weaken.weaken.weaken)
      (od_local_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
        x.weaken.weaken.weaken.weaken.weaken)))))))))))
derive_free_closed od_code_m

theorem od_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (θ z p x : Term d) :
    Formula.satisfies ρ (od_code_m (𝒞 := 𝒞) θ z p x) ↔
      Od_code_d I (θ.eval ρ) (z.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [od_code_m, Od_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, v_sat_l I hE, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, sc_num_sat_l I hE, oc_seq_sat_l I hE, od_local_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

def Od_in_d (x : M.Domain) : Prop := ∃ θ z p, Od_code_d I θ z p x

def od_in_m {d} (x : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (od_code_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest x.weaken.weaken.weaken)))
derive_free_closed od_in_m

theorem od_in_sat_l (hE : Extensional M) {d} (ρ : Env M d) (x : Term d) :
    Formula.satisfies ρ (od_in_m (𝒞 := 𝒞) x) ↔ Od_in_d I (x.eval ρ) := by
  simp only [od_in_m, Od_in_d, Formula.satisfies_exists_iff, od_code_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

/-- 同一合法定义码只定义一个对象；辅助结构、赋值和满足表不能改变输出。 -/
theorem od_code_unique_l (hZF : M.Models ZF) {θ z p x y}
    (hx : Od_code_d I θ z p x) (hy : Od_code_d I θ z p y) : x = y := by
  obtain ⟨ω, X, e, a, s, hω, hX, he, _, ha, hs, hx⟩ := hx
  obtain ⟨ω', Y, f, b, t, hω', hY, hf, _, hb, ht, hy⟩ := hy
  have eq := hZF.1.eq_of_same_members ω' ω (fun i =>
    ⟨hω'.2 ω hω.1 i, hω.2 ω' hω'.1 i⟩)
  subst ω'
  have eq := ZF.v_unique_l I hZF hY hX; subst Y
  have eq := hZF.1.eq_of_same_members f e (fun i => iff_of_false (hf i) (he i)); subst f
  have eq := sc_num_injective_l I hZF hω hb ha; subst b
  have eq := oc_seq_injective_l I hZF hω ht hs; subst t
  exact hy.2 x hx.1

theorem od_code_types_l (hZF : M.Models ZF) {θ z p x} (h : Od_code_d I θ z p x) :
    M.IsOrdinal θ ∧ M.IsOrdinal z ∧ M.IsOrdinal p := by
  obtain ⟨ω, _, _, _, _, hω, hX, _, _, ha, hs, _⟩ := h
  exact ⟨v_ordinal_l I hX, hω.members_areOrdinals hZF z (sc_num_natural_l I hZF hω ha),
    oc_seq_ordinal_l I hZF hs⟩

end YesMetaZFC.SetTheory.InnerModel
