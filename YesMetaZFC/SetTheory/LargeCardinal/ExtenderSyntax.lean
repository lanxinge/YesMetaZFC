import YesMetaZFC.SetTheory.LargeCardinal.ExtenderShort

/-! # 扩展器性质的原一阶公式

全部量词绑定对象模型内的集合，有限长度可以非标准。各分量公式直接对应
预扩展器的数学条件；可数完备性以实际层族及共同纤维表达。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def em_family_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) ω.weaken.weaken) (.imp (fn0_m (.bound 1) L.weaken.weaken
    .newest) (.existsE (rd_entry_m (.bound 1) .newest F.weaken.weaken.weaken)))))) (.conj (.forallE (.forallE
    (.forallE (.imp (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 2) .newest
    F.weaken.weaken.weaken) (Formula.extensionalEq (.bound 1) .newest)))))) (.forallE (.forallE (.imp (rd_entry_m
    (.bound 1) .newest F.weaken.weaken) (.existsE (.existsE (.conj (.mem (.bound 1) ω.weaken.weaken.weaken.weaken)
    (.conj (fn0_m (.bound 1) L.weaken.weaken.weaken.weaken (.bound 3)) (.conj (.forallE (.iff (.mem .newest
    (.bound 1)) (fn0_m (.bound 2) κ.weaken.weaken.weaken.weaken.weaken .newest))) (FilterZF.maximal_m .newest
    (.bound 2))))))))))))
derive_free_closed em_family_m

def en_normal_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 7)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (fn0_m (.bound 7)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6)) (.imp (rd_entry_m (.bound 6) (.bound 5)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (.forallE (.iff (.mem .newest (.bound 5))
    (fn0_m (.bound 8) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest))) (.imp (fn0_m
    (.bound 4) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3)) (.imp (rd_entry_m (.bound 2)
    (.bound 1) (.bound 6)) (.imp (.mem .newest (.bound 5)) (.imp (.forallE (.imp (.mem .newest (.bound 1)) (.forallE
    (.forallE (.imp (rd_entry_m (.bound 2) (.bound 1) (.bound 6)) (.imp (rd_entry_m (.bound 5) .newest (.bound 2))
    (.mem (.bound 1) .newest))))))) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.conj
    (Formula.isSuccessor (.bound 4) (.bound 12)) (.conj (fn0_m (.bound 4)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3)) (.conj
    (Formula.subset (.bound 11) (.bound 3)) (.conj (rd_entry_m (.bound 12) (.bound 1) (.bound 3)) (.conj (.mem
    (.bound 1) (.bound 6)) (.conj (rd_entry_m (.bound 3) (.bound 2)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.conj (.mem
    .newest (.bound 2)) (.forallE (.imp (.mem .newest (.bound 1)) (en_graph_m (.bound 13)
    κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6)
    (.bound 9) .newest))))))))))))))))))))))))))))))))
derive_free_closed en_normal_m

def ea_part_m {d} (p : Bool) (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 6)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (fn0_m (.bound 6)
    L.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5)) (.imp (rd_entry_m (.bound 5) (.bound 4)
    F.weaken.weaken.weaken.weaken.weaken.weaken.weaken) (.imp (rd_entry_m (.bound 3) (.bound 1) (.bound 5)) (.imp
    (rd_entry_m (.bound 2) .newest (.bound 5)) (.existsE (.conj (.forallE (.iff (.mem .newest (.bound 1)) (.conj
    (fn0_m (.bound 8) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest) (ea_test_m p
    κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) .newest)))) (.iff (.mem
    .newest (.bound 5)) (if p then (Formula.extensionalEq (.bound 2) (.bound 1)) else (.mem (.bound 2)
    (.bound 1))))))))))))))))))
@[simp] theorem ea_part_m_closed_l {d} (p : Bool) (ω κ L F : Term d)
    (hω : ω.freeSupport = []) (hκ : κ.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) : (ea_part_m p ω κ L F).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [ea_part_m, Definitional.Formula.FreeClosed, hω, hκ, hL, hF]

def ex_complete_m {d} (κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.imp (fn0_m (.bound 3) L.weaken.weaken.weaken.weaken (.bound 2)) (.imp
    (rd_entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken.weaken) (.imp (.forallE (.iff (.mem .newest (.bound 1))
    (fn0_m (.bound 4) κ.weaken.weaken.weaken.weaken.weaken .newest))) (ed_complete_m κ.weaken.weaken.weaken.weaken
    .newest (.bound 1)))))))))
derive_free_closed ex_complete_m

def ex_principal_m {d} (ω κ F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) ω.weaken.weaken.weaken) (.imp (fn0_m (.bound 2)
    κ.weaken.weaken.weaken (.bound 1)) (.imp (rd_entry_m (.bound 1) .newest F.weaken.weaken.weaken) (.forallE (.iff
    (.mem .newest (.bound 1)) (.conj (.forallE (.imp (.mem .newest (.bound 1)) (fn0_m (.bound 4)
    κ.weaken.weaken.weaken.weaken.weaken .newest))) (.mem (.bound 2) .newest))))))))))
derive_free_closed ex_principal_m

def ex_nonprincipal_m {d} (κ F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.forallE (.forallE (.imp (rd_entry_m (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken)
    (.imp (rd_entry_m (.bound 1) .newest (.bound 3)) (.imp (.neg (.mem .newest κ.weaken.weaken.weaken.weaken))
    (ed_nonprincipal_m (.bound 2)))))))))
derive_free_closed ex_nonprincipal_m

def ex_countable_m {d} (ω κ L F : Term d) : Formula 1 d :=
  (.forallE (.forallE (.imp (ef_levels_m ω.weaken.weaken κ.weaken.weaken (.bound 1)) (.imp ((es_fiber_m (𝒞 :=
    kpair_convention_l)) ω.weaken.weaken L.weaken.weaken F.weaken.weaken (.bound 1) .newest) (.existsE (ef_fiber_m
    ω.weaken.weaken.weaken κ.weaken.weaken.weaken (.bound 2) .newest))))))
derive_free_closed ex_countable_m

theorem em_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (em_family_m ω κ L F) ↔ Em_family_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [em_family_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_exists_iff, rd_entry_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_iff_iff, FilterZF.maximal_sat_d, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨ht, hf, hm⟩ => ⟨ht, hf, hm⟩, fun h => ⟨h.total, h.function, h.measure⟩⟩

theorem en_normal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (en_normal_m ω κ L F) ↔ En_normal_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [en_normal_m, En_normal_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry_sat_l hE, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, en_graph_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ea_part_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Bool) (ω κ L F : Term d) :
    Formula.satisfies ρ (ea_part_m p ω κ L F) ↔ Ea_part_d p (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  cases p <;> simp only [ea_part_m, Ea_part_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_iff_iff,
    ea_test_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken] <;> rfl

def ea_atoms_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (ea_part_m false ω κ L F) (ea_part_m true ω κ L F)
derive_free_closed ea_atoms_m
theorem ea_atoms_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ea_atoms_m ω κ L F) ↔ Ea_atoms_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ea_atoms_m, Formula.satisfies_conj_iff, ea_part_sat_l hE]
  exact ⟨fun h p => by cases p; exact h.1; exact h.2, fun h => ⟨h false, h true⟩⟩

theorem ex_complete_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L F : Term d) :
    Formula.satisfies ρ (ex_complete_m κ L F) ↔ ∀ n a U D, Fn0_d n (L.eval ρ) a → Rd_entry_d a U (F.eval ρ) →
      (∀ s, M.mem s D ↔ Fn0_d n (κ.eval ρ) s) → Ed_complete_d (κ.eval ρ) D U := by
  simp only [ex_complete_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, ed_complete_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

theorem ex_principal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ F : Term d) :
    Formula.satisfies ρ (ex_principal_m ω κ F) ↔ ∀ n a U, M.mem n (ω.eval ρ) → Fn0_d n (κ.eval ρ) a →
      Rd_entry_d a U (F.eval ρ) → ∀ A, M.mem A U ↔ (∀ s, M.mem s A → Fn0_d n (κ.eval ρ) s) ∧ M.mem a A := by
  simp only [ex_principal_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE,
    rd_entry_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Definitional.Term.eval_weaken]; rfl

theorem ex_nonprincipal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ F : Term d) :
    Formula.satisfies ρ (ex_nonprincipal_m κ F) ↔ ∀ a U i α, Rd_entry_d a U (F.eval ρ) → Rd_entry_d i α a →
      ¬ M.mem α (κ.eval ρ) → Ed_nonprincipal_d U := by
  simp only [ex_nonprincipal_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rd_entry_sat_l hE,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, ed_nonprincipal_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ex_countable_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d)
    (I : kpair_convention_l.Interpretation M) : Formula.satisfies ρ (ex_countable_m ω κ L F) ↔
      ∀ H f, Ef_levels_d (ω.eval ρ) (κ.eval ρ) H → Es_fiber_d I (ω.eval ρ) (L.eval ρ) (F.eval ρ) H f →
        ∃ g, Ef_fiber_d (ω.eval ρ) (κ.eval ρ) H g := by
  simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, ef_levels_sat_l hE,
    es_fiber_sat_l I hE, Formula.satisfies_exists_iff, ef_fiber_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ex_pre_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (Formula.isOmega ω)
  (.conj (Formula.isCardinal kpair_convention_l κ) (.conj (.mem ω κ) (.conj (Formula.isOrdinal L)
    (.conj (.mem κ L) (.conj (Formula.isFunction kpair_convention_l F) (.conj (em_family_m ω κ L F) (.conj (es_coherent_m (𝒞 := kpair_convention_l) ω κ L F)
      (.conj (ex_complete_m κ L F) (.conj (ea_atoms_m ω κ L F) (.conj (en_normal_m ω κ L F)
        (.conj (ex_principal_m ω κ F) (ex_nonprincipal_m κ F))))))))))))
derive_free_closed ex_pre_m

theorem ex_pre_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ex_pre_m ω κ L F) ↔ Ex_pre_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isCardinal_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isOrdinal_iff, em_family_sat_l hZF.1, es_coherent_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    ex_complete_sat_l hZF.1, ea_atoms_sat_l hZF.1, en_normal_sat_l hZF.1,
    ex_principal_sat_l hZF.1, ex_nonprincipal_sat_l hZF.1]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩,
    fun h => ⟨h.omega, h.critical, h.uncountable, h.length, h.above, h.graph, h.measures, h.coherent,
      h.complete, h.atoms, h.normal, h.principal, h.nonprincipal⟩⟩

def ex_short_m {d} (ω κ L F : Term d) : Formula 1 d := .conj (ex_pre_m ω κ L F) (ex_countable_m ω κ L F)
derive_free_closed ex_short_m
theorem ex_short_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (ex_short_m ω κ L F) ↔ Ex_short_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [ex_short_m, Formula.satisfies_conj_iff, ex_pre_sat_l hZF,
    ex_countable_sat_l hZF.1 ρ ω κ L F (kp_pair_l (ZF.modelsKP hZF))]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.toEx_pre_d, h.countable⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

