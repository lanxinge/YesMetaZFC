import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Comparison
import YesMetaZFC.Model.Forcing.Iteration.Proper.Lemma

/-! # 变动主前缀与商名称的内部递归状态

状态只编码当前条件和当前商名称。一步保留精确前缀，选择指定稠密集中的名称，
并记录在下一阶段的实际比较；全部不变量均有原公式，可用于模型内部的归纳与选择。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pr_state_d (I : kpair_convention_l.Interpretation M) (α B R b D N x : M.Domain) : Prop :=
  ∃ p τ K, KPair_d M x p τ ∧ Mstr_d M B R B N p ∧ Name_d M B τ ∧
  Row_quot_d I α B b D N K ∧ Mem_force_d M B R B p τ K

def row_pr_state_m {n} (α B R b D N x : Term n) : Formula 1 n :=
  let u (t : Term n) : Term (n+3) := t.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.conj (kpair_m (u x) (.bound 2) (.bound 1))
      (.conj (mstr_m (u B) (u R) (u B) (u N) (.bound 2))
      (.conj (name_m (u B) (.bound 1))
      (.conj (row_quot_m (u α) (u B) (u b) (u D) (u N) .newest)
      (mem_force_m (u B) (u R) (u B) (.bound 2) (.bound 1) .newest)))))))
derive_free_closed row_pr_state_m

theorem row_pr_state_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D N x : Term n) :
    Formula.satisfies ρ (row_pr_state_m α B R b D N x) ↔
      Row_pr_state_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (N.eval ρ) (x.eval ρ) := by
  simp only [row_pr_state_m, Row_pr_state_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, mstr_sat_l M hE, name_sat_l M hE, row_quot_sat_l I hE, mem_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Row_pr_move_d (I : kpair_convention_l.Interpretation M) (α B R b D V N β T E x y : M.Domain) : Prop :=
  ∃ p τ q σ K ν η, KPair_d M x p τ ∧ KPair_d M y q σ ∧ M.IsRestrictionOf I p q α ∧ Name_d M B σ ∧
  Row_quot_d I α B b D N K ∧ Check_d M b V ν ∧ Check_d M b E η ∧
  Mem_force_d M B R B p σ K ∧ Mem_force_d M B R B p σ η ∧ Rel_force_d M B R B ν p σ τ ∧
  Row_cut_lower_d I α B R b D N σ p β T q

def row_pr_move_m {n} (α B R b D V N β T E x y : Term n) : Formula 1 n :=
  let u (t : Term n) : Term (n+7) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (kpair_m (u x) (.bound 6) (.bound 5))
      (.conj (kpair_m (u y) (.bound 4) (.bound 3))
      (.conj (Formula.isRestriction kpair_convention_l (.bound 6) (.bound 4) (u α))
      (.conj (name_m (u B) (.bound 3))
      (.conj (row_quot_m (u α) (u B) (u b) (u D) (u N) (.bound 2))
      (.conj (check_m (u b) (u V) (.bound 1))
      (.conj (check_m (u b) (u E) .newest)
      (.conj (mem_force_m (u B) (u R) (u B) (.bound 6) (.bound 3) (.bound 2))
      (.conj (mem_force_m (u B) (u R) (u B) (.bound 6) (.bound 3) .newest)
      (.conj (rel_force_m (u B) (u R) (u B) (.bound 1) (.bound 6) (.bound 3) (.bound 5))
      (row_cut_lower_m (u α) (u B) (u R) (u b) (u D) (u N) (.bound 3) (.bound 6) (u β) (u T) (.bound 4))))))))))))))))))
derive_free_closed row_pr_move_m

theorem row_pr_move_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D V N β T E x y : Term n) :
    Formula.satisfies ρ (row_pr_move_m α B R b D V N β T E x y) ↔
      Row_pr_move_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) (N.eval ρ) (β.eval ρ) (T.eval ρ) (E.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [row_pr_move_m, Row_pr_move_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_isRestriction_iff I, name_sat_l M hE,
    row_quot_sat_l I hE, check_sat_l M hE, mem_force_sat_l M hE, rel_force_sat_l M hE, row_cut_lower_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def Row_pr_thread_d (I : kpair_convention_l.Interpretation M) (F G b D N A i x : M.Domain) : Prop :=
  ∃ α B R, Entry_d M i α A ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Row_pr_state_d I α B R b D N x

def row_pr_thread_m {n} (F G b D N A i x : Term n) : Formula 1 n :=
  let u (t : Term n) : Term (n+3) := t.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.conj (entry_m (u i) (.bound 2) (u A))
      (.conj (entry_m (.bound 2) (.bound 1) (u F))
      (.conj (entry_m (.bound 2) .newest (u G))
      (row_pr_state_m (.bound 2) (.bound 1) .newest (u b) (u D) (u N) (u x)))))))
derive_free_closed row_pr_thread_m

theorem row_pr_thread_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (F G b D N A i x : Term n) :
    Formula.satisfies ρ (row_pr_thread_m F G b D N A i x) ↔
      Row_pr_thread_d I (F.eval ρ) (G.eval ρ) (b.eval ρ) (D.eval ρ) (N.eval ρ) (A.eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [row_pr_thread_m, Row_pr_thread_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, row_pr_state_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def Row_pr_advance_d (I : kpair_convention_l.Interpretation M) (F G b D V N A E i x y : M.Domain) : Prop :=
  ∃ j α B R β C T U, M.SuccessorOf j i ∧ Entry_d M i α A ∧ Entry_d M j β A ∧
  Entry_d M α B F ∧ Entry_d M α R G ∧ Entry_d M β C F ∧ Entry_d M β T G ∧ Entry_d M i U E ∧
  Row_pr_move_d I α B R b D V N β T U x y

def row_pr_advance_m {n} (F G b D V N A E i x y : Term n) : Formula 1 n :=
  let u (t : Term n) : Term (n+8) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (Formula.isSuccessor (.bound 7) (u i))
      (.conj (entry_m (u i) (.bound 6) (u A))
      (.conj (entry_m (.bound 7) (.bound 3) (u A))
      (.conj (entry_m (.bound 6) (.bound 5) (u F))
      (.conj (entry_m (.bound 6) (.bound 4) (u G))
      (.conj (entry_m (.bound 3) (.bound 2) (u F))
      (.conj (entry_m (.bound 3) (.bound 1) (u G))
      (.conj (entry_m (u i) .newest (u E))
      (row_pr_move_m (.bound 6) (.bound 5) (.bound 4) (u b) (u D) (u V) (u N) (.bound 3) (.bound 1) .newest (u x) (u y)))))))))))))))))
derive_free_closed row_pr_advance_m

theorem row_pr_advance_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (F G b D V N A E i x y : Term n) :
    Formula.satisfies ρ (row_pr_advance_m F G b D V N A E i x y) ↔
      Row_pr_advance_d I (F.eval ρ) (G.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) (N.eval ρ) (A.eval ρ) (E.eval ρ) (i.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [row_pr_advance_m, Row_pr_advance_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, entry_sat_l M hE, row_pr_move_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
