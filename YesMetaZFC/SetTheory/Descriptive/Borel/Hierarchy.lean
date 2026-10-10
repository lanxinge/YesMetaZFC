import YesMetaZFC.SetTheory.Descriptive.Closed

/-! # 标准 Borel 层级的内部超限递归

Σ⁰₁ 为开集，Π⁰α 为相对补集；正层 Σ⁰α 由开集及较低 Π 层的内部可数并组成。
第零层为空。递归值是 P(B) 的实际子集，索引是模型的序数，允许外部非良基。
可数族是模型中的函数；在 ZF 中不把一族集合的存在偷换为一族码的存在。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 允许部分 ω 索引，因而空并不需另添人为索引。 -/
def Bu_d (ω H K : M.Domain) : Prop := M.IsSetFunction I H ∧
  (∀ i C, M.PairMember I i C H → M.mem i ω) ∧
  ∀ x, M.mem x K ↔ ∃ i C, M.PairMember I i C H ∧ M.mem x C
def bu_m {d} (ω H K : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H) (.conj
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken) (.mem (.bound 1) ω.weaken.weaken))))
  (.forallE (.iff (.mem .newest K.weaken) (.existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))))
derive_free_closed bu_m
theorem bu_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H K : Term d) :
    Formula.satisfies ρ (bu_m (𝒞 := 𝒞) ω H K) ↔ Bu_d I (ω.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [bu_m, Bu_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Definitional.Term.eval_weaken]; rfl

def Bh_prev_d (B F C : M.Domain) : Prop := ∃ β V L,
  M.PairMember I β V F ∧ M.mem L V ∧ Cm_d B L C
def bh_prev_m {d} (B F C : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj
  (.mem .newest (.bound 1)) (cm_m B.weaken.weaken.weaken .newest C.weaken.weaken.weaken)))))
derive_free_closed bh_prev_m
theorem bh_prev_sat_l {d} (ρ : Env M d) (B F C : Term d) :
    Formula.satisfies ρ (bh_prev_m (𝒞 := 𝒞) B F C) ↔ Bh_prev_d I (B.eval ρ) (F.eval ρ) (C.eval ρ) := by
  simp only [bh_prev_m, Bh_prev_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, cm_sat_l, Definitional.Term.eval_weaken]; rfl

def Bh_build_d (ω A B F K : M.Domain) : Prop := M.MemberSubset K B ∧
  (∃ β V, M.PairMember I β V F) ∧ (Open_d A B K ∨ ∃ H,
    Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Bh_prev_d I B F C)
def bh_build_m {d} (ω A B F K : Term d) : Formula 1 d := .conj (Formula.subset K B) (.conj
  (.existsE (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)))
  (.disj (open_m A B K) (.existsE (.conj (bu_m (𝒞 := 𝒞) ω.weaken .newest K.weaken)
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (bh_prev_m (𝒞 := 𝒞) B.weaken.weaken.weaken F.weaken.weaken.weaken .newest))))))))
derive_free_closed bh_build_m
theorem bh_build_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B F K : Term d) :
    Formula.satisfies ρ (bh_build_m (𝒞 := 𝒞) ω A B F K) ↔
      Bh_build_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (F.eval ρ) (K.eval ρ) := by
  simp only [bh_build_m, Bh_build_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_disj_iff,
    open_sat_l, bu_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    bh_prev_sat_l I, Definitional.Term.eval_weaken]; rfl

def Bh_step_d (ω A B F S : M.Domain) : Prop := ∀ K, M.mem K S ↔ Bh_build_d I ω A B F K
def bh_op_s : BinarySchema 3 := { body := .forallE (.iff (.mem .newest (.bound 1))
  (bh_build_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)) }
def bh_env_l (ω A B : M.Domain) : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B
theorem bh_op_l (hE : Extensional M) (ρ : Env M 3) :
    (bh_op_s (𝒞 := 𝒞)).denote ρ = Bh_step_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext F S
  apply propext
  simp only [bh_op_s, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, bh_build_sat_l I hE]; rfl

def Bh_d (ω A B α S : M.Domain) : Prop := M.IsRecursionValue I (Bh_step_d I ω A B) α S
def bh_m {d} (ω A B α S : Term d) : Formula 1 d := Formula.isRecursionValue 𝒞 (bh_op_s (𝒞 := 𝒞))
  (Definitional.TermVector.ofFn (Fin.cases B (Fin.cases A (fun _ => ω)))) α S
@[simp] theorem bh_closed_l {d} (ω A B α S : Term d) (hω : ω.freeSupport = []) (hA : A.freeSupport = [])
    (hB : B.freeSupport = []) (hα : α.freeSupport = []) (hS : S.freeSupport = []) : (bh_m (𝒞 := 𝒞) ω A B α S).FreeClosed := by
  have he : (Definitional.TermVector.ofFn (Fin.cases B (Fin.cases A (fun _ : Fin 1 => ω)))).FreeClosed := by
    intro i
    cases i using Fin.cases with
    | zero => exact hB
    | succ i => cases i using Fin.cases with
      | zero => exact hA
      | succ i => simpa only [Definitional.TermVector.get_ofFn, Fin.cases_succ] using hω
  exact Formula.isRecursionValue_freeClosed _ _ _ _ _ he hα hS
theorem bh_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α S : Term d) :
    Formula.satisfies ρ (bh_m (𝒞 := 𝒞) ω A B α S) ↔
      Bh_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (S.eval ρ) := by
  rw [bh_m, Formula.satisfies_isRecursionValue_iff I hE, bh_op_l I hE]; rfl

theorem bh_class_l (hZF : M.Models ZF) (ω A B : M.Domain) : M.IsClassFunctionOnTransfiniteSequences I (Bh_step_d I ω A B) := by
  intro F _
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  let φ : UnarySchema 4 := { body := bh_build_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, hs⟩ := ZF.separation_exists_d hZF φ ((bh_env_l ω A B).push F) P
  have step : Bh_step_d I ω A B F S := by
    intro K
    have hv : φ.denote ((bh_env_l ω A B).push F) K ↔ Bh_build_d I ω A B F K := bh_build_sat_l I hZF.1 _ _ _ _ _ _
    exact (hs K).trans ((and_congr (hp K) hv).trans ⟨And.right, fun h => ⟨h.1, h⟩⟩)
  exact ⟨S, step, fun U hu => hZF.1.eq_of_same_members U S (fun K => (hu K).trans (step K).symm)⟩
theorem bh_exists_l (hZF : M.Models ZF) {ω A B α} (hα : M.IsOrdinal α) : ∃ S, Bh_d I ω A B α S := by
  have hc := bh_class_l I hZF ω A B
  have op : (bh_op_s (𝒞 := 𝒞)).denote (bh_env_l ω A B) = Bh_step_d I ω A B := bh_op_l I hZF.1 _
  rw [← op] at hc
  obtain ⟨S, hs⟩ := ZF.recursionValue_exists hZF I (bh_env_l ω A B) bh_op_s hc hα
  exact ⟨S, by simpa only [Bh_d, op] using hs⟩
theorem bh_unique_l (hZF : M.Models ZF) {ω A B α S T} (h : Bh_d I ω A B α S) (k : Bh_d I ω A B α T) : S = T := by
  have hc := bh_class_l I hZF ω A B
  have op : (bh_op_s (𝒞 := 𝒞)).denote (bh_env_l ω A B) = Bh_step_d I ω A B := bh_op_l I hZF.1 _
  rw [← op] at hc
  exact ZF.recursionValue_unique hZF I (bh_env_l ω A B) bh_op_s hc
    (by simpa only [Bh_d, op] using h) (by simpa only [Bh_d, op] using k)

def Bsig_d (ω A B α K : M.Domain) : Prop := ∃ S, Bh_d I ω A B α S ∧ M.mem K S
def Bpi_d (ω A B α K : M.Domain) : Prop := ∃ L, Bsig_d I ω A B α L ∧ Cm_d B L K
def bsig_m {d} (ω A B α K : Term d) : Formula 1 d := .existsE (.conj
  (bh_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken α.weaken .newest) (.mem K.weaken .newest))
def bpi_m {d} (ω A B α K : Term d) : Formula 1 d := .existsE (.conj
  (bsig_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken α.weaken .newest) (cm_m B.weaken .newest K.weaken))
derive_free_closed bsig_m
derive_free_closed bpi_m
theorem bsig_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α K : Term d) :
    Formula.satisfies ρ (bsig_m (𝒞 := 𝒞) ω A B α K) ↔ Bsig_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [bsig_m, Bsig_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bh_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl
theorem bpi_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α K : Term d) :
    Formula.satisfies ρ (bpi_m (𝒞 := 𝒞) ω A B α K) ↔ Bpi_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [bpi_m, Bpi_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsig_sat_l I hE, cm_sat_l, Definitional.Term.eval_weaken]; rfl

theorem bsig_ordinal_l {ω A B α K} (h : Bsig_d I ω A B α K) : M.IsOrdinal α :=
  h.elim fun _ h => h.1.elim fun _ h => h.1.1.1
theorem bsig_subset_l {ω A B α K} (h : Bsig_d I ω A B α K) : M.MemberSubset K B := by
  obtain ⟨S, ⟨F, _, hf⟩, hs⟩ := h
  exact ((hf K).mp hs).1

/-- 递归方程：量词遍历真实的较低序数层与真实的内部可数族。 -/
theorem bsig_unfold_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α) :
    Bsig_d I ω A B α K ↔ M.MemberSubset K B ∧ (∃ β, M.mem β α) ∧
      (Open_d A B K ∨ ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω A B β C) := by
  obtain ⟨S, hS⟩ := bh_exists_l I hZF (ω := ω) (A := A) (B := B) hα
  have eqv : Bsig_d I ω A B α K ↔ M.mem K S :=
    ⟨fun ⟨V, hv, hk⟩ => bh_unique_l I hZF hv hS ▸ hk, fun hk => ⟨S, hS, hk⟩⟩
  obtain ⟨F, hf, hs⟩ := hS
  have prev C : Bh_prev_d I B F C ↔ ∃ β, M.mem β α ∧ Bpi_d I ω A B β C := by
    constructor
    · rintro ⟨β, V, L, hv, hl, hc⟩
      have hb := (hf.1.2.2 β).mpr ⟨V, hv⟩
      exact ⟨β, hb, L, ⟨V, hf.recursionValue_of_pairMember hb hv, hl⟩, hc⟩
    · rintro ⟨β, hb, L, ⟨V, hv, hl⟩, hc⟩
      obtain ⟨W, hw⟩ := (hf.1.2.2 β).mp hb
      exact ⟨β, W, L, hw, bh_unique_l I hZF hv (hf.recursionValue_of_pairMember hb hw) ▸ hl, hc⟩
  refine eqv.trans ((hs K).trans (and_congr_right fun _ => and_congr ?_ ?_))
  · constructor
    · exact fun ⟨β, V, hv⟩ => ⟨β, (hf.1.2.2 β).mpr ⟨V, hv⟩⟩
    · rintro ⟨β, hb⟩
      obtain ⟨V, hv⟩ := (hf.1.2.2 β).mp hb
      exact ⟨β, V, hv⟩
  · exact or_congr Iff.rfl (exists_congr fun H => and_congr_right fun _ =>
      forall_congr' fun i => forall_congr' fun C => imp_congr_right fun _ => prev C)

end YesMetaZFC.SetTheory.Descriptive
