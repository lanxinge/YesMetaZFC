import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 自然数博弈、策略与获胜

双方交替落子，先手占偶数坐标。策略是全部内部有限局面上的 ω 值函数；
另一方回合的值不参与服从条件。局面、策略及对局都是对象模型中的集合图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Gm_even_d (ω n : M.Domain) : Prop := ∃ k, M.mem k ω ∧ M.IsOrdinalAddition I n k k

def gm_even_m {d} (ω n : Term d) : Formula 1 d :=
  Formula.existsMem ω (Formula.isOrdinalAddition 𝒞 n.weaken .newest .newest)
derive_free_closed gm_even_m

theorem gm_even_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n : Term d) :
    Formula.satisfies ρ (gm_even_m (𝒞 := 𝒞) ω n) ↔ Gm_even_d I (ω.eval ρ) (n.eval ρ) := by
  simp only [gm_even_m, Gm_even_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_isOrdinalAddition_iff I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Gm_turn_d (p : Bool) (ω n : M.Domain) : Prop :=
  if p then Gm_even_d I ω n else ¬ Gm_even_d I ω n

def gm_turn_m (p : Bool) {d} (ω n : Term d) : Formula 1 d :=
  if p then gm_even_m (𝒞 := 𝒞) ω n else .neg (gm_even_m (𝒞 := 𝒞) ω n)

@[simp] theorem gm_turn_closed_l (p : Bool) {d} (ω n : Term d)
    (hω : ω.freeSupport = []) (hn : n.freeSupport = []) : (gm_turn_m (𝒞 := 𝒞) p ω n).FreeClosed := by
  cases p <;> simp [gm_turn_m, Definitional.Formula.FreeClosed, gm_even_m_freeClosed ω n hω hn]

theorem gm_turn_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω n : Term d) :
    Formula.satisfies ρ (gm_turn_m (𝒞 := 𝒞) p ω n) ↔ Gm_turn_d I p (ω.eval ρ) (n.eval ρ) := by
  cases p <;> simp only [gm_turn_m, Gm_turn_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_neg_iff, gm_even_sat_l I hE]

def Gm_follows_d (p : Bool) (ω σ x : M.Domain) : Prop :=
  ∀ n, M.mem n ω → Gm_turn_d I p ω n → ∀ s, M.IsRestrictionOf I s x n →
    ∀ a, M.PairMember I n a x → M.PairMember I s a σ

def gm_follows_m (p : Bool) {d} (ω σ x : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (gm_turn_m (𝒞 := 𝒞) p ω.weaken .newest)
    (.forallE (.imp (Formula.isRestriction 𝒞 .newest x.weaken.weaken (.bound 1))
      (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest x.weaken.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest σ.weaken.weaken.weaken))))))
derive_free_closed gm_follows_m

theorem gm_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω σ x : Term d) :
    Formula.satisfies ρ (gm_follows_m (𝒞 := 𝒞) p ω σ x) ↔
      Gm_follows_d I p (ω.eval ρ) (σ.eval ρ) (x.eval ρ) := by
  simp only [gm_follows_m, Gm_follows_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    gm_turn_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Gm_win_d (p : Bool) (ω B T A σ : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I σ T ω ∧ ∀ x, M.mem x B → Gm_follows_d I p ω σ x →
    if p then M.mem x A else ¬ M.mem x A

def gm_win_m (p : Bool) {d} (ω B T A σ : Term d) : Formula 1 d :=
  .conj (Formula.isFunctionFromTo 𝒞 σ T ω) (Formula.forallMem B
    (.imp (gm_follows_m (𝒞 := 𝒞) p ω.weaken σ.weaken .newest)
      (if p then .mem .newest A.weaken else .neg (.mem .newest A.weaken))))

@[simp] theorem gm_win_closed_l (p : Bool) {d} (ω B T A σ : Term d)
    (hω : ω.freeSupport = []) (hB : B.freeSupport = []) (hT : T.freeSupport = [])
    (hA : A.freeSupport = []) (hσ : σ.freeSupport = []) : (gm_win_m (𝒞 := 𝒞) p ω B T A σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [gm_win_m, Definitional.Formula.FreeClosed,
    Formula.isFunctionFromTo, hω, hB, hT, hA, hσ]

theorem gm_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω B T A σ : Term d) :
    Formula.satisfies ρ (gm_win_m (𝒞 := 𝒞) p ω B T A σ) ↔
      Gm_win_d I p (ω.eval ρ) (B.eval ρ) (T.eval ρ) (A.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [gm_win_m, Gm_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, gm_follows_sat_l I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

def Det_d (ω B T A : M.Domain) : Prop :=
  (∃ σ, Gm_win_d I true ω B T A σ) ∨ ∃ σ, Gm_win_d I false ω B T A σ

def det_m {d} (ω B T A : Term d) : Formula 1 d :=
  .disj (.existsE (gm_win_m (𝒞 := 𝒞) true ω.weaken B.weaken T.weaken A.weaken .newest))
    (.existsE (gm_win_m (𝒞 := 𝒞) false ω.weaken B.weaken T.weaken A.weaken .newest))
derive_free_closed det_m

theorem det_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T A : Term d) :
    Formula.satisfies ρ (det_m (𝒞 := 𝒞) ω B T A) ↔ Det_d I (ω.eval ρ) (B.eval ρ) (T.eval ρ) (A.eval ρ) := by
  simp only [det_m, Det_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    gm_win_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 两个常值收益集合具有实际内部获胜策略；策略空间并非额外存在性前提。 -/
theorem gm_trivial_l (hZF : M.Models ZF) {ω B T e} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) :
    (∃ σ, Gm_win_d I true ω B T B σ) ∧ ∃ τ, Gm_win_d I false ω B T e τ := by
  obtain ⟨z, _, hz⟩ := hω.1.1
  obtain ⟨σ, hσ, _⟩ := ZF.exists_constantFunction hZF I (source := T) hz
  exact ⟨⟨σ, hσ, fun _ hx _ => hx⟩, ⟨σ, hσ, fun x _ _ => he x⟩⟩

end YesMetaZFC.SetTheory.Descriptive
