import YesMetaZFC.SetTheory.Descriptive.Analytic.Code
import YesMetaZFC.SetTheory.Descriptive.Distance

/-! # Borel 求值的闭证书语法

证书实数在节点编号处记数值：零为假，非零为真；真并节点记所选子编号的后继。
违规由有限读数见证。叶为假的违规读取完整有限标签，叶为真的违规则读取一处冲突。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Nv_d (E w a v : M.Domain) : Prop := ∃ i, M.PairMember I a i E ∧ M.PairMember I i v w
def nv_m {d} (E w a v : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 a.weaken .newest E.weaken) (Formula.orderedPairMem 𝒞 .newest v.weaken w.weaken))
derive_free_closed nv_m
theorem nv_sat_l {d} (ρ : Env M d) (E w a v : Term d) :
    Formula.satisfies ρ (nv_m (𝒞 := 𝒞) E w a v) ↔ Nv_d I (E.eval ρ) (w.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [nv_m, Nv_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Ns_d (T R E a v : M.Domain) : Prop := ∃ b j,
  M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b j E ∧ M.SuccessorOf v j
def ns_m {d} (T R E a v : Term d) : Formula 1 d := .existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken)
  (.conj (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken) (Formula.isSuccessor v.weaken.weaken .newest)))))
derive_free_closed ns_m
theorem ns_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R E a v : Term d) :
    Formula.satisfies ρ (ns_m (𝒞 := 𝒞) T R E a v) ↔
      Ns_d I (T.eval ρ) (R.eval ρ) (E.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [ns_m, Ns_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

def Nl_d (F E z x w : M.Domain) : Prop := ∃ a s v, M.PairMember I a s F ∧ Nv_d I E w a v ∧
  ((v = z ∧ M.MemberSubset s x) ∨ (v ≠ z ∧ ∃ j, Diff_d I s x j))
def nl_m {d} (F E z x w : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken w.weaken.weaken.weaken (.bound 2) .newest)
  (.disj (.conj (Formula.extensionalEq .newest z.weaken.weaken.weaken) (Formula.subset (.bound 1) x.weaken.weaken.weaken))
    (.conj (.neg (Formula.extensionalEq .newest z.weaken.weaken.weaken))
      (.existsE (diff_m (𝒞 := 𝒞) (.bound 2) x.weaken.weaken.weaken.weaken .newest))))))))
derive_free_closed nl_m
theorem nl_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F E z x w : Term d) :
    Formula.satisfies ρ (nl_m (𝒞 := 𝒞) F E z x w) ↔
      Nl_d I (F.eval ρ) (E.eval ρ) (z.eval ρ) (x.eval ρ) (w.eval ρ) := by
  simp only [nl_m, Nl_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, nv_sat_l I, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_subset_iff, Formula.satisfies_neg_iff,
    diff_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Nn_d (R N E z w : M.Domain) : Prop := ∃ a b v u, M.mem a N ∧ Rd_entry_d b a R ∧
  Nv_d I E w a v ∧ Nv_d I E w b u ∧ (v = z ↔ u = z)
def nn_m {d} (R N E z w : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (.mem (.bound 3) N.weaken.weaken.weaken.weaken) (.conj
  (rd_entry_m (.bound 2) (.bound 3) R.weaken.weaken.weaken.weaken) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken.weaken w.weaken.weaken.weaken.weaken (.bound 3) (.bound 1)) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken.weaken w.weaken.weaken.weaken.weaken (.bound 2) .newest)
  (.iff (Formula.extensionalEq (.bound 1) z.weaken.weaken.weaken.weaken)
    (Formula.extensionalEq .newest z.weaken.weaken.weaken.weaken)))))))))
derive_free_closed nn_m
theorem nn_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R N E z w : Term d) :
    Formula.satisfies ρ (nn_m (𝒞 := 𝒞) R N E z w) ↔
      Nn_d I (R.eval ρ) (N.eval ρ) (E.eval ρ) (z.eval ρ) (w.eval ρ) := by
  simp only [nn_m, Nn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, nv_sat_l I, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

def Nu_d (T R E z a v w : M.Domain) : Prop :=
  (v = z ∧ ∃ b u, M.mem b T ∧ Rd_entry_d b a R ∧ Nv_d I E w b u ∧ u ≠ z) ∨
  (v ≠ z ∧ ¬ Ns_d I T R E a v) ∨
  ∃ b j, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b j E ∧ M.SuccessorOf v j ∧ Nv_d I E w b z
def nu_m {d} (T R E z a v w : Term d) : Formula 1 d := .disj
  (.conj (Formula.extensionalEq v z) (.existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken)
    (.conj (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken) (.conj
      (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) .newest)
      (.neg (Formula.extensionalEq .newest z.weaken.weaken)))))))) (.disj
  (.conj (.neg (Formula.extensionalEq v z)) (.neg (ns_m (𝒞 := 𝒞) T R E a v)))
  (.existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken) (.conj
    (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken) (.conj
    (Formula.isSuccessor v.weaken.weaken .newest)
    (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) z.weaken.weaken))))))))
derive_free_closed nu_m
theorem nu_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R E z a v w : Term d) :
    Formula.satisfies ρ (nu_m (𝒞 := 𝒞) T R E z a v w) ↔
      Nu_d I (T.eval ρ) (R.eval ρ) (E.eval ρ) (z.eval ρ) (a.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [nu_m, Nu_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    rd_entry_sat_l hE, nv_sat_l I, Formula.satisfies_neg_iff, ns_sat_l I hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

def Nb_d (T R N F E z x w : M.Domain) : Prop := Nv_d I E w z z ∨ Nl_d I F E z x w ∨
  Nn_d I R N E z w ∨ ∃ a v, Buni_d I N F a ∧ Nv_d I E w a v ∧ Nu_d I T R E z a v w
def nb_m {d} (T R N F E z x w : Term d) : Formula 1 d := .disj (nv_m (𝒞 := 𝒞) E w z z) (.disj
  (nl_m (𝒞 := 𝒞) F E z x w) (.disj (nn_m (𝒞 := 𝒞) R N E z w)
    (.existsE (.existsE (.conj (buni_m (𝒞 := 𝒞) N.weaken.weaken F.weaken.weaken (.bound 1))
      (.conj (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) .newest)
        (nu_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken E.weaken.weaken z.weaken.weaken (.bound 1) .newest w.weaken.weaken)))))))
derive_free_closed nb_m
theorem nb_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F E z x w : Term d) :
    Formula.satisfies ρ (nb_m (𝒞 := 𝒞) T R N F E z x w) ↔
      Nb_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (E.eval ρ) (z.eval ρ) (x.eval ρ) (w.eval ρ) := by
  simp only [nb_m, Nb_d, Formula.satisfies_disj_iff, nv_sat_l I, nl_sat_l I hE, nn_sat_l I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, buni_sat_l I, nu_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem nv_unique_l {ω T E w a v u} (he : M.IsSetFunctionFromTo I E T ω) (hw : M.IsSetFunction I w)
    (h : Nv_d I E w a v) (k : Nv_d I E w a u) : v = u := by
  obtain ⟨i, hi, hv⟩ := h
  obtain ⟨j, hj, hu⟩ := k
  exact hw.2 i v u hv (he.1.2 a j i hj hi ▸ hu)

theorem nv_total_l {ω T E w a} (he : M.IsSetFunctionFromTo I E T ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (ha : M.mem a T) : ∃ v, M.mem v ω ∧ Nv_d I E w a v := by
  obtain ⟨i, hi, hai⟩ := he.2.2 a ha
  obtain ⟨v, hv, hiv⟩ := hw.2.2 i hi
  exact ⟨v, hv, i, hai, hiv⟩

end YesMetaZFC.SetTheory.Descriptive
