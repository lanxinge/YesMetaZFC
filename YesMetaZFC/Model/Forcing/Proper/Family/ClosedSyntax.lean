import YesMetaZFC.Model.Forcing.Proper.Family.IndexedSyntax

/-! # 共同泛型闭包的内部证书

证书保存实际的公式码域、有限参数域及两张运算图。它只要求 N 对这些已构造
的有限元运算闭合；不把 N[G] 的初等性或提升结论作为前提。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ng_ops_d (ω δ F G b X w u C S T D P Q : M.Domain) : Prop :=
  (∀ x, ¬ M.mem x u) ∧ Scode_d I ω C ∧ Fseq_space_d I ω X S ∧
  M.IsCartesianProduct I T C ω ∧ M.IsCartesianProduct I D T S ∧
  M.IsSetFunctionFromTo I P D X ∧ M.IsSetFunctionFromTo I Q D X ∧
  (∀ p t, Entry_d M p t P → Ng_joint_d I false ω δ F G b X w u p t) ∧
  (∀ p t, Entry_d M p t Q → Ng_joint_d I true ω δ F G b X w u p t)

def ng_graph_m {n} (k : Bool) (ω δ F G b X w u K : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest K.weaken.weaken)
    (ng_joint_m k ω.weaken.weaken δ.weaken.weaken F.weaken.weaken G.weaken.weaken
      b.weaken.weaken X.weaken.weaken w.weaken.weaken u.weaken.weaken (.bound 1) .newest)))
derive_free_closed ng_graph_m

theorem ng_graph_sat_l (hE : Extensional M) {n} (k : Bool) (ρ : Env M n)
    (ω δ F G b X w u K : Term n) : Formula.satisfies ρ (ng_graph_m k ω δ F G b X w u K) ↔
      ∀ p t, Entry_d M p t (K.eval ρ) → Ng_joint_d I k (ω.eval ρ) (δ.eval ρ) (F.eval ρ)
        (G.eval ρ) (b.eval ρ) (X.eval ρ) (w.eval ρ) (u.eval ρ) p t := by
  simp only [ng_graph_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, ng_joint_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def ng_ops_m {n} (ω δ F G b X w u C S T D P Q : Term n) : Formula 1 n :=
  .conj (Formula.isEmpty u) (.conj (scode_m (𝒞 := kpair_convention_l) ω C)
    (.conj (fseq_space_m (𝒞 := kpair_convention_l) ω X S)
    (.conj (Formula.isCartesianProduct kpair_convention_l T C ω)
    (.conj (Formula.isCartesianProduct kpair_convention_l D T S)
    (.conj (Formula.isFunctionFromTo kpair_convention_l P D X)
    (.conj (Formula.isFunctionFromTo kpair_convention_l Q D X)
    (.conj (ng_graph_m false ω δ F G b X w u P) (ng_graph_m true ω δ F G b X w u Q))))))))
derive_free_closed ng_ops_m

theorem ng_ops_sat_l (hE : Extensional M) {n} (ρ : Env M n)
    (ω δ F G b X w u C S T D P Q : Term n) :
    Formula.satisfies ρ (ng_ops_m ω δ F G b X w u C S T D P Q) ↔
      Ng_ops_d I (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (X.eval ρ)
        (w.eval ρ) (u.eval ρ) (C.eval ρ) (S.eval ρ) (T.eval ρ) (D.eval ρ) (P.eval ρ) (Q.eval ρ) := by
  simp only [ng_ops_m, Ng_ops_d, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff,
    scode_sat_l I hE, fseq_space_sat_l I hE, Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_isFunctionFromTo_iff I hE, ng_graph_sat_l I hE]

def Ng_closed_d (ω δ F G b X N w : M.Domain) : Prop := ∃ u C S T D P Q,
  Ng_ops_d I ω δ F G b X w u C S T D P Q ∧ M.mem u N ∧
    Fc_closed_d I ω T P N ∧ Fc_closed_d I ω T Q N

def ng_closed_m {n} (ω δ F G b X N w : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (ng_ops_m ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      δ.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      G.weaken.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      X.weaken.weaken.weaken.weaken.weaken.weaken.weaken w.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (.conj (.mem (.bound 6) N.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
    (.conj (fc_closed_m (𝒞 := kpair_convention_l) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 3) (.bound 1) N.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
      (fc_closed_m (𝒞 := kpair_convention_l) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
        (.bound 3) .newest N.weaken.weaken.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed ng_closed_m

theorem ng_closed_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω δ F G b X N w : Term n) :
    Formula.satisfies ρ (ng_closed_m ω δ F G b X N w) ↔
      Ng_closed_d I (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (X.eval ρ) (N.eval ρ) (w.eval ρ) := by
  simp only [ng_closed_m, Ng_closed_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ng_ops_sat_l I hE, Formula.satisfies_mem_iff, fc_closed_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
