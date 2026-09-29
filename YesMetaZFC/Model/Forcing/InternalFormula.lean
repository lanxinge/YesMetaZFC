import YesMetaZFC.Model.Forcing.InternalAtomicTruth

/-! # 原 Project 公式的内部力迫翻译

条件参数置于原赋值之后，量词通过固定重排保留原变量。否定采用加强否定，
布尔连接词由否定和合取组成；名称量词始终遍历地模型内部名称。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def fenv_l {M : SetTheory.Structure.{u}} {n} (ρ : Env M n) (B R z p : M.Domain) : Env M (n + 4) :=
  (((ρ.push B).push R).push z).push p

def param_shift_l {n} (i : Fin n) : Fin (n + 4) := ⟨i.val + 4, by omega⟩

def name_shift_l {n} : Fin (n + 5) → Fin (n + 5) :=
  Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 0
    (fun i => ⟨i.val + 5, by omega⟩)))))

def neg_code_m {n} (φ : Formula 1 (n + 4)) : Formula 1 (n + 4) :=
  .forallE (.imp (below_m (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1))
    (.neg (φ.rename (BoundEmbedding.unaryUnderOne (parameterCount := n + 3)))))
derive_free_closed neg_code_m

def imp_code_m {n} (φ ψ : Formula 1 (n + 4)) : Formula 1 (n + 4) :=
  neg_code_m (.conj φ (neg_code_m ψ))
derive_free_closed imp_code_m

def all_code_m {n} (φ : Formula 1 (n + 5)) : Formula 1 (n + 4) :=
  .forallE (.imp (name_m (.bound 4) .newest) (φ.rename name_shift_l))
derive_free_closed all_code_m

def some_code_m {n} (φ : Formula 1 (n + 5)) : Formula 1 (n + 4) :=
  .existsE (.conj (name_m (.bound 4) .newest) (φ.rename name_shift_l))
derive_free_closed some_code_m

def mem_code_m {n} (s t : Term n) : Formula 1 (n + 4) :=
  mem_force_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    (s.rename param_shift_l) (t.rename param_shift_l)
derive_free_closed mem_code_m

def eq_code_m {n} (s t : Term n) : Formula 1 (n + 4) :=
  eq_force_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    (s.rename param_shift_l) (t.rename param_shift_l)
derive_free_closed eq_code_m

def force_code_m {a} : {n : Nat} → Formula a n → Formula 1 (n + 4)
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem s t => mem_code_m s t
  | _, .atom .extensionalEq _ ts => eq_code_m (ts 0) (ts 1)
  | _, .atom .subset _ ts => all_code_m (imp_code_m
      (mem_code_m .newest (ts 0).weaken) (mem_code_m .newest (ts 1).weaken))
  | _, .neg φ => neg_code_m (force_code_m φ)
  | _, .conj φ ψ => .conj (force_code_m φ) (force_code_m ψ)
  | _, .disj φ ψ => neg_code_m (.conj (neg_code_m (force_code_m φ)) (neg_code_m (force_code_m ψ)))
  | _, .imp φ ψ => imp_code_m (force_code_m φ) (force_code_m ψ)
  | _, .iff φ ψ => .conj (imp_code_m (force_code_m φ) (force_code_m ψ))
      (imp_code_m (force_code_m ψ) (force_code_m φ))
  | _, .forallE φ => all_code_m (force_code_m φ)
  | _, .existsE φ => neg_code_m (all_code_m (neg_code_m (force_code_m φ)))
termination_by structural _ φ => φ

theorem force_code_closed_l {a n} (φ : Formula a n) (h : φ.FreeClosed) : (force_code_m φ).FreeClosed := by
  induction φ <;> simp only [force_code_m, Definitional.Formula.FreeClosed] at *
  case mem s t => exact mem_code_m_freeClosed s t h.1 h.2
  case atom r _ ts =>
    cases r
    · exact eq_code_m_freeClosed _ _ (h 0) (h 1)
    · exact all_code_m_freeClosed _ (imp_code_m_freeClosed _ _
        (mem_code_m_freeClosed _ _ rfl (by simpa using h 0))
        (mem_code_m_freeClosed _ _ rfl (by simpa using h 1)))
  case neg φ ih => exact neg_code_m_freeClosed _ (ih h)
  case conj φ ψ ih jh => exact ⟨ih h.1, jh h.2⟩
  case disj φ ψ ih jh =>
    apply neg_code_m_freeClosed
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨neg_code_m_freeClosed _ (ih h.1), neg_code_m_freeClosed _ (jh h.2)⟩
  case imp φ ψ ih jh => exact imp_code_m_freeClosed _ _ (ih h.1) (jh h.2)
  case iff φ ψ ih jh =>
    exact ⟨imp_code_m_freeClosed _ _ (ih h.1) (jh h.2), imp_code_m_freeClosed _ _ (jh h.2) (ih h.1)⟩
  case forallE φ ih => exact all_code_m_freeClosed _ (ih h)
  case existsE φ ih => exact neg_code_m_freeClosed _ (all_code_m_freeClosed _ (neg_code_m_freeClosed _ (ih h)))

variable (M : SetTheory.Structure.{u})

def Code_d {n} (B R z : M.Domain) (φ : Formula 1 (n + 4)) (ρ : Env M n) (p : M.Domain) : Prop :=
  Formula.satisfies (fenv_l ρ B R z p) φ

def Forces_d {a n} (B R z : M.Domain) (φ : Formula a n) (ρ : Env M n) (p : M.Domain) : Prop :=
  Code_d M B R z (force_code_m φ) ρ p

theorem fenv_param_l {n} (ρ : Env M n) (B R z p : M.Domain) :
    (fenv_l ρ B R z p).reindex param_shift_l = ρ := by cases ρ; rfl

theorem fenv_name_l {n} (ρ : Env M n) (B R z p x : M.Domain) :
    ((fenv_l ρ B R z p).push x).reindex name_shift_l = fenv_l (ρ.push x) B R z p := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))) i
  · rfl

theorem code_neg_l (hE : Extensional M) {n} (B R z : M.Domain) (φ : Formula 1 (n + 4))
    (ρ : Env M n) (p : M.Domain) :
    Code_d M B R z (neg_code_m φ) ρ p ↔ Neg_d M B R z (Code_d M B R z φ ρ) p := by
  simp only [Code_d, neg_code_m, Neg_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, below_sat_l M hE, Formula.satisfies_rename,
    fenv_l, Env.reindex_push_unaryUnderOne, Definitional.Term.eval_newest,
    Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push]
  rfl

theorem code_all_l (hE : Extensional M) {n} (B R z : M.Domain) (φ : Formula 1 (n + 5))
    (ρ : Env M n) (p : M.Domain) : Code_d M B R z (all_code_m φ) ρ p ↔
      ∀ x, Name_d M B x → Code_d M B R z φ (ρ.push x) p := by
  simp only [Code_d, all_code_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    name_sat_l M hE, Formula.satisfies_rename, fenv_name_l M, Definitional.Term.eval_newest,
    Term.eval_bound_four_push]
  rfl

theorem code_some_l (hE : Extensional M) {n} (B R z : M.Domain) (φ : Formula 1 (n + 5))
    (ρ : Env M n) (p : M.Domain) : Code_d M B R z (some_code_m φ) ρ p ↔
      ∃ x, Name_d M B x ∧ Code_d M B R z φ (ρ.push x) p := by
  simp only [Code_d, some_code_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    name_sat_l M hE, Formula.satisfies_rename, fenv_name_l M, Definitional.Term.eval_newest,
    Term.eval_bound_four_push]
  rfl

theorem code_mem_l (hE : Extensional M) {n} (B R z : M.Domain) (s t : Term n)
    (ρ : Env M n) (p : M.Domain) : Code_d M B R z (mem_code_m s t) ρ p ↔
      Mem_force_d M B R z p (s.eval ρ) (t.eval ρ) := by
  simp only [Code_d, mem_code_m, mem_force_sat_l M hE, Definitional.Term.eval_rename, fenv_param_l M]
  rfl

theorem code_eq_l (hE : Extensional M) {n} (B R z : M.Domain) (s t : Term n)
    (ρ : Env M n) (p : M.Domain) : Code_d M B R z (eq_code_m s t) ρ p ↔
      Eq_force_d M B R z p (s.eval ρ) (t.eval ρ) := by
  simp only [Code_d, eq_code_m, eq_force_sat_l M hE, Definitional.Term.eval_rename, fenv_param_l M]
  rfl

theorem code_defined_l {n} (B R z : M.Domain) (φ : Formula 1 (n + 4)) (h : φ.FreeClosed) (ρ : Env M n) :
    Defined_d M (Code_d M B R z φ ρ) := ⟨n + 3, ⟨φ, h⟩, ((ρ.push B).push R).push z, fun _ => Iff.rfl⟩

theorem forces_defined_l {a n} (B R z : M.Domain) (φ : Formula a n) (h : φ.FreeClosed) (ρ : Env M n) :
    Defined_d M (Forces_d M B R z φ ρ) := code_defined_l M B R z _ (force_code_closed_l φ h) ρ

end YesMetaZFC.Model.Forcing.Internal
