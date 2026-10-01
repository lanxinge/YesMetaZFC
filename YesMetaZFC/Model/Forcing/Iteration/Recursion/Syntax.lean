import YesMetaZFC.Model.Forcing.Iteration.Recursion.History
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Rule
import YesMetaZFC.Model.Forcing.Iteration.Limit.Basic

/-! # 支撑迭代的内部递归算子

合法历史的后继调用给定原公式规则，零与极限调用统一支撑极限。无效历史只为
满足一般递归定理的全定义要求而返回空集；递归不变式将排除实际轨迹进入该分支。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_good_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω e S δ F H : M.Domain) : Prop :=
  M.IsSequenceOfLength I S δ ∧ Row_history_d S F H ∧ Row_system_d I δ F H e ∧ Row_system_supp_d I k ω F

def row_good_m (k : Bool) {n} (ω e S δ F H : Term n) : Formula 1 n :=
  .conj (Formula.isSequenceOfLength kpair_convention_l S δ)
    (.conj (row_history_m S F H) (.conj (row_system_m δ F H e) (row_system_supp_m k ω F)))
derive_free_closed row_good_m

theorem row_good_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) (k : Bool) {n}
    (ρ : Env M n) (ω e S δ F H : Term n) : Formula.satisfies ρ (row_good_m k ω e S δ F H) ↔
      Row_good_d I k (ω.eval ρ) (e.eval ρ) (S.eval ρ) (δ.eval ρ) (F.eval ρ) (H.eval ρ) := by
  simp only [row_good_m, Row_good_d, Formula.satisfies_conj_iff, Formula.satisfies_isSequenceOfLength_iff I hE,
    row_history_sat_l hE, row_system_sat_l I hE, row_system_supp_sat_l I hE]

def Row_action_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω : M.Domain) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (δ F H e D V : M.Domain) : Prop :=
  ((∃ α, M.SuccessorOf δ α) ∧ φ.denote (row_rule_env_l ρ δ F H e) D V) ∨ Row_limit_d I k ω δ F H δ D V

def row_action_m {n m} (φ : BinarySchema (n+4)) (es : Fin n → Term m) (k : Bool)
    (ω δ F H e D V : Term m) : Formula 1 m :=
  .disj (.conj (.existsE (Formula.isSuccessor δ.weaken .newest))
    (binary_pred_m φ (Fin.cases e (Fin.cases H (Fin.cases F (Fin.cases δ es)))) D V))
    (row_limit_m k ω δ F H δ D V)

@[simp] theorem row_action_closed_l {n m} (φ : BinarySchema (n+4)) (es : Fin n → Term m) (k : Bool)
    (ω δ F H e D V : Term m) (hs : ∀ i, (es i).freeSupport = [])
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = [])
    (he : e.freeSupport = []) (hD : D.freeSupport = []) (hV : V.freeSupport = []) :
    (row_action_m φ es k ω δ F H e D V).FreeClosed := by
  simp only [row_action_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨Formula.isSuccessor_freeClosed _ _ (by simpa using hδ) rfl,
    binary_pred_closed_l _ _ _ _ (Fin.cases he (Fin.cases hH (Fin.cases hF (Fin.cases hδ hs)))) hD hV⟩,
    row_limit_m_freeClosed _ _ _ _ _ _ _ _ hω hδ hF hH hδ hD hV⟩

theorem row_action_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n m}
    (φ : BinarySchema (n+4)) (ρ : Env M m) (es : Fin n → Term m) (k : Bool) (ω δ F H e D V : Term m) :
    Formula.satisfies ρ (row_action_m φ es k ω δ F H e D V) ↔
      Row_action_d I k (ω.eval ρ) φ ⟨fun i => (es i).eval ρ, ρ.free⟩
        (δ.eval ρ) (F.eval ρ) (H.eval ρ) (e.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_action_m, Row_action_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff, binary_pred_sat_l,
    args_cons_l, row_limit_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Row_op_d (I : kpair_convention_l.Interpretation M) (k : Bool) (ω e : M.Domain) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (S c : M.Domain) : Prop :=
  (∃ δ F H D V, Row_good_d I k ω e S δ F H ∧ Row_action_d I k ω φ ρ δ F H e D V ∧ KPair_d M c D V) ∨
  ((¬ ∃ δ F H, Row_good_d I k ω e S δ F H) ∧ ∀ x, ¬ M.mem x c)

def row_domain_m (k : Bool) {m} (ω e S : Term m) : Formula 1 m :=
  .existsE (.existsE (.existsE (row_good_m k ω.weaken.weaken.weaken e.weaken.weaken.weaken S.weaken.weaken.weaken
    (.bound 2) (.bound 1) .newest)))
derive_free_closed row_domain_m

def row_op_s {n} (φ : BinarySchema (n+4)) (k : Bool) : BinarySchema (n+2) := {
  body := .disj
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
      (row_good_m k (.bound 8) (.bound 7) (.bound 6) (.bound 4) (.bound 3) (.bound 2))
      (.conj (row_action_m φ (fun i => .bound ⟨i.val+9, by omega⟩) k
        (.bound 8) (.bound 4) (.bound 3) (.bound 2) (.bound 7) (.bound 1) .newest)
        (kpair_m (.bound 5) (.bound 1) .newest))))))))
    (.conj (.neg (row_domain_m k (.bound 3) (.bound 2) (.bound 1))) (Formula.isEmpty .newest))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨⟨row_good_m_freeClosed _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl,
      row_action_closed_l _ _ _ _ _ _ _ _ _ _ (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl,
      kpair_m_freeClosed _ _ _ rfl rfl rfl⟩,
      row_domain_m_freeClosed _ _ _ _ rfl rfl rfl, Formula.isEmpty_freeClosed _ rfl⟩ }

def row_op_env_l {n} (ρ : Env M n) (ω e : M.Domain) : Env M (n+2) := (ρ.push ω).push e

theorem row_op_denote_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (φ : BinarySchema (n+4)) (ρ : Env M n) (k : Bool) (ω e S c) :
    (row_op_s φ k).denote (row_op_env_l ρ ω e) S c ↔ Row_op_d I k ω e φ ρ S c := by
  simp only [row_op_s, BinarySchema.denote, Row_op_d, row_domain_m, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_isEmpty_iff, row_good_sat_l I hE, row_action_sat_l I hE, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

end YesMetaZFC.Model.Forcing.Internal
