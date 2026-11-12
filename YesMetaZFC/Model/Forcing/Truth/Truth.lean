import YesMetaZFC.Model.Forcing.Atomic.Truth
import YesMetaZFC.Model.Forcing.Extension.Isomorphism

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
@[simp] theorem imp_code_m_freeClosed {n} (φ ψ : Formula 1 (n+4))
    (h : φ.FreeClosed) (k : ψ.FreeClosed) : (imp_code_m φ ψ).FreeClosed :=
  neg_code_m_freeClosed _ ⟨h, neg_code_m_freeClosed _ k⟩

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

/-! ## 内部正则真值的逻辑运算

逻辑运算只在非零条件上使用正则性。全称量词的反向真值由内部可定义的反例
稠密集推出；不存在假定量词已经具有真值对应的字段。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

def Regular_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (P : M.Domain → Prop) : Prop :=
  Lower_d M B R z P ∧ ∀ p, M.mem p B → p ≠ z → Dense_d M B R z P p → P p

def Eval_d (M : SetTheory.Structure.{u}) (B R z : M.Domain) (U : M.Domain → Prop)
    (P : M.Domain → Prop) (Q : Prop) : Prop := Regular_d M B R z P ∧ ((∃ p, U p ∧ P p) ↔ Q)

theorem eval_congr_l {P : M.Domain → Prop} {Q S : Prop} (h : Eval_d M B R z U P Q)
    (e : Q ↔ S) : Eval_d M B R z U P S := ⟨h.1, h.2.trans e⟩

variable (O : Cond_order_d M B R z)
include O

theorem regular_neg_l {P : M.Domain → Prop} (h : Lower_d M B R z P) :
    Regular_d M B R z (Neg_d M B R z P) := by
  refine ⟨neg_lower_l O P, fun p _ _ hd q hq hP => ?_⟩
  obtain ⟨r, hr, hn⟩ := hd q hq
  exact hn r (below_refl_l O hr.1 hr.2.1) (h q r hq.1 hr hP)

omit O in
theorem regular_conj_l {P Q : M.Domain → Prop}
    (hP : Regular_d M B R z P) (hQ : Regular_d M B R z Q) :
    Regular_d M B R z (fun p => P p ∧ Q p) := by
  refine ⟨fun p q hp hq h => ⟨hP.1 p q hp hq h.1, hQ.1 p q hp hq h.2⟩, fun p hp hn hd => ?_⟩
  exact ⟨hP.2 p hp hn (fun q hq => (hd q hq).elim fun r h => ⟨r, h.1, h.2.1⟩),
    hQ.2 p hp hn (fun q hq => (hd q hq).elim fun r h => ⟨r, h.1, h.2.2⟩)⟩

/-- 隶属力迫在稠密成立处成立；该原子规则只需要条件属于条件集。 -/
theorem mem_force_dense_l {s t p} (hp : M.mem p B)
    (hd : Dense_d M B R z (fun q => Mem_force_d M B R z q s t) p) : Mem_force_d M B R z p s t := by
  refine ⟨hp, fun q hq => ?_⟩
  obtain ⟨r, hr, _, h⟩ := hd q hq
  obtain ⟨v, a, b, hv, ha, hvb, he⟩ := h r (below_refl_l O hr.1 hr.2.1)
  exact ⟨v, a, b, below_trans_l O hq.1 hv hr, ha, hvb, he⟩

theorem regular_mem_l (s t : M.Domain) :
    Regular_d M B R z (fun p => Mem_force_d M B R z p s t) := by
  constructor
  · intro p q hp hq h
    refine ⟨hq.1, fun r hr => ?_⟩
    exact h.2 r (below_trans_l O hp hr hq)
  · exact fun _ hp _ hd => mem_force_dense_l O hp hd

theorem regular_eq_l (hZF : M.Models ZF) {s t} (hs : Name_d M B s) (ht : Name_d M B t) :
    Regular_d M B R z (fun p => Eq_force_d M B R z p s t) :=
  ⟨eq_force_lower_l O hZF hs ht, fun _ hp _ h => eq_force_dense_l O hZF hs ht hp h⟩

omit O in
/-- 正条件没有正则性质时，可加强到该性质的加强否定。 -/
theorem regular_neg_witness_l {P : M.Domain → Prop} (h : Regular_d M B R z P)
    {p} (hp : M.mem p B) (hz : p ≠ z) (hn : ¬ P p) :
    ∃ q, Below_d M B R z q p ∧ Neg_d M B R z P q := by
  classical
  apply Classical.byContradiction
  intro he
  apply hn (h.2 p hp hz ?_)
  intro q hq
  by_cases hq' : ∃ r, Below_d M B R z r q ∧ P r
  · exact hq'
  · exact False.elim (he ⟨q, hq, fun r hr hP => hq' ⟨r, hr, hP⟩⟩)

variable (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include hZF hU

theorem eval_neg_l {P : M.Domain → Prop} {Q : Prop} (hD : Defined_d M P)
    (h : Eval_d M B R z U P Q) : Eval_d M B R z U (Neg_d M B R z P) (¬ Q) :=
  ⟨regular_neg_l O h.1.1, (generic_neg_l O hZF hU hD h.1.1).trans (not_congr h.2)⟩

omit O hZF in
theorem eval_conj_l {P Q : M.Domain → Prop} {A C : Prop}
    (h : Eval_d M B R z U P A) (k : Eval_d M B R z U Q C) :
    Eval_d M B R z U (fun p => P p ∧ Q p) (A ∧ C) := by
  refine ⟨regular_conj_l h.1 k.1, ?_⟩
  constructor
  · rintro ⟨p, hp, hP, hQ⟩
    exact ⟨h.2.mp ⟨p, hp, hP⟩, k.2.mp ⟨p, hp, hQ⟩⟩
  · rintro ⟨hA, hC⟩
    obtain ⟨p, hp, hP⟩ := h.2.mpr hA
    obtain ⟨q, hq, hQ⟩ := k.2.mpr hC
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact ⟨r, hr, h.1.1 p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hP,
      k.1.1 q r (hU.proper q hq).1 ⟨hr'.1, hr'.2, hrq⟩ hQ⟩

/-- 对可定义名称族的全称量词取真值；反例见证集也必须具有实际公式。 -/
theorem eval_all_l {P : M.Domain → M.Domain → Prop} {Q : M.Domain → Prop}
    (hD : Defined_d M (fun p => ∀ x, Name_d M B x → P x p))
    (hC : Defined_d M (fun p => ∃ x, Name_d M B x ∧ Neg_d M B R z (P x) p))
    (h : ∀ x, Name_d M B x → Eval_d M B R z U (P x) (Q x)) :
    Eval_d M B R z U (fun p => ∀ x, Name_d M B x → P x p) (∀ x, Name_d M B x → Q x) := by
  refine ⟨⟨fun p q hp hq hP x hx => (h x hx).1.1 p q hp hq (hP x hx), ?_⟩, ?_⟩
  · intro p hp hn hd x hx
    exact (h x hx).1.2 p hp hn (fun q hq => (hd q hq).elim fun r hr => ⟨r, hr.1, hr.2 x hx⟩)
  · constructor
    · rintro ⟨p, hp, hP⟩ x hx
      exact (h x hx).2.mp ⟨p, hp, hP x hx⟩
    · intro hQ
      apply Classical.byContradiction
      intro hn
      obtain ⟨p, hp, hnP⟩ := (generic_decide_l O hZF hU hD).elim (fun h => False.elim (hn h)) id
      obtain ⟨q, hq, x, hx, hnX⟩ := generic_pick_l hZF hU hC hp (by
        intro q hq
        apply Classical.byContradiction
        intro hnC
        apply hnP q hq
        intro x hx
        apply (h x hx).1.2 q hq.1 hq.2.1
        intro r hr
        apply Classical.byContradiction
        intro hnX
        exact hnC ⟨r, hr, x, hx, fun s hs hP => hnX ⟨s, hs, hP⟩⟩)
      obtain ⟨r, hr, hP⟩ := (h x hx).2.mpr (hQ x hx)
      obtain ⟨s, hs, hsq, hsr⟩ := hU.directed q r hq hr
      have hs' := hU.proper s hs
      exact hnX s ⟨hs'.1, hs'.2, hsq⟩
        ((h x hx).1.1 r s (hU.proper r hr).1 ⟨hs'.1, hs'.2, hsr⟩ hP)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部原公式的内部力迫真值定理

原公式、内部力迫翻译与名称泛型商逐构造对应。量词见证由商类的名称代表取得；
全称量词的反向方向使用实际反例公式形成的稠密集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

theorem defined_congr_l {P Q : M.Domain → Prop} (h : Defined_d M P) (e : ∀ p, P p ↔ Q p) :
    Defined_d M Q := by
  obtain ⟨n, φ, ρ, hφ⟩ := h
  exact ⟨n, φ, ρ, fun p => (hφ p).trans (e p)⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include O hZF hU

private theorem code_eval_neg_l {n} {C : Formula 1 (n + 4)} {ρ : Env M n} {Q : Prop}
    (hC : C.FreeClosed) (h : Eval_d M B R z U (Code_d M B R z C ρ) Q) :
    Eval_d M B R z U (Code_d M B R z (neg_code_m C) ρ) (¬ Q) := by
  have he := funext fun p => propext (code_neg_l M hZF.1 B R z C ρ p)
  rw [he]
  exact eval_neg_l O hZF hU (code_defined_l M B R z C hC ρ) h

omit O hZF in
private theorem code_eval_conj_l {n} {C D : Formula 1 (n + 4)} {ρ : Env M n} {P Q : Prop}
    (h : Eval_d M B R z U (Code_d M B R z C ρ) P)
    (k : Eval_d M B R z U (Code_d M B R z D ρ) Q) :
    Eval_d M B R z U (Code_d M B R z (.conj C D) ρ) (P ∧ Q) := by
  have he : Code_d M B R z (.conj C D) ρ = (fun p => Code_d M B R z C ρ p ∧ Code_d M B R z D ρ p) :=
    funext fun _ => propext (Formula.satisfies_conj_iff _ C D)
  rw [he]
  exact eval_conj_l hU h k

private theorem code_eval_imp_l {n} {C D : Formula 1 (n + 4)} {ρ : Env M n} {P Q : Prop}
    (hC : C.FreeClosed) (hD : D.FreeClosed)
    (h : Eval_d M B R z U (Code_d M B R z C ρ) P)
    (k : Eval_d M B R z U (Code_d M B R z D ρ) Q) :
    Eval_d M B R z U (Code_d M B R z (imp_code_m C D) ρ) (P → Q) := by
  have hn := code_eval_neg_l O hZF hU hD k
  have hc := code_eval_conj_l hU h hn
  have hCD : (Definitional.Formula.conj C (neg_code_m D)).FreeClosed := by
    simp only [Definitional.Formula.FreeClosed]; exact ⟨hC, neg_code_m_freeClosed _ hD⟩
  apply eval_congr_l (code_eval_neg_l O hZF hU hCD hc)
  classical
  simp only [not_and, Classical.not_not]

local notation "E" => extension_l M hZF B R z U

def Env_val_d {n} (ρ : Env M n) (η : Env E n) : Prop :=
  ∀ t : Term n, Qval_d M B R z U (t.eval ρ) (t.eval η)

/-- 名称赋值直接投到商类；不选择商的代表元。 -/
def qenv_l {n} (ρ : Env M n) (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) : Env E n where
  bound i := Quot.mk _ ⟨ρ.bound i, hρ (.bound i)⟩
  free i := Quot.mk _ ⟨ρ.free i, hρ (.free i)⟩

omit O hU in
theorem qenv_val_l {n} (ρ : Env M n) (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) :
    Env_val_d (R := R) (z := z) (U := U) hZF ρ
      (qenv_l hZF ρ hρ) := by
  intro t
  cases t with
  | bound i => exact ⟨hρ (.bound i), rfl⟩
  | free i => exact ⟨hρ (.free i), rfl⟩

omit O hU in
theorem env_val_push_l {n} {ρ : Env M n} {η : Env E n} (h : Env_val_d hZF ρ η)
    {t : M.Domain} {x : (E).Domain} (hx : Qval_d M B R z U t x) :
    Env_val_d hZF (ρ.push t) (η.push x) := by
  intro s
  cases s with
  | free i => exact h (.free i)
  | bound i => exact Fin.cases hx (fun i => h (.bound i)) i

omit O hU in
theorem env_val_name_l {n} {ρ : Env M n} {η : Env E n} (h : Env_val_d hZF ρ η) (t : Term n) :
    Name_d M B (t.eval ρ) := qval_name_l (h t)

omit O hU in
/-- 任意扩张赋值都可在 Prop 中提升为内部名称赋值，不导出全局选择函数。 -/
theorem lift_env_l {n} (η : Env E n) : ∃ ρ : Env M n, Env_val_d hZF ρ η := by
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice (fun i => value_name_l (η.bound i))
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun i => value_name_l (η.free i))
  refine ⟨⟨b, f⟩, fun t => ?_⟩
  cases t with
  | bound i => exact (hb i).2
  | free i => exact (hf i).2

private theorem code_eval_all_l {n} {C : Formula 1 (n + 5)} {ρ : Env M n} {Q : (E).Domain → Prop}
    (hC : C.FreeClosed)
    (h : ∀ t, Name_d M B t → ∀ x : (E).Domain, Qval_d M B R z U t x →
      Eval_d M B R z U (Code_d M B R z C (ρ.push t)) (Q x)) :
    Eval_d M B R z U (Code_d M B R z (all_code_m C) ρ) (∀ x, Q x) := by
  have he := funext fun p => propext (code_all_l M hZF.1 B R z C ρ p)
  rw [he]
  have hd := defined_congr_l (code_defined_l M B R z (all_code_m C) (all_code_m_freeClosed _ hC) ρ)
    (code_all_l M hZF.1 B R z C ρ)
  have hc : Defined_d M (fun p => ∃ t, Name_d M B t ∧ Neg_d M B R z (Code_d M B R z C (ρ.push t)) p) :=
    defined_congr_l (code_defined_l M B R z (some_code_m (neg_code_m C))
      (some_code_m_freeClosed _ (neg_code_m_freeClosed _ hC)) ρ) (fun p => by
        rw [code_some_l M hZF.1]
        exact exists_congr fun t => and_congr_right fun _ => code_neg_l M hZF.1 B R z C (ρ.push t) p)
  have hall : Eval_d M B R z U (fun p => ∀ t, Name_d M B t → Code_d M B R z C (ρ.push t) p)
      (∀ t, Name_d M B t → ∃ x : (E).Domain, Qval_d M B R z U t x ∧ Q x) := by
    apply eval_all_l O hZF hU hd hc
    intro t ht
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U) ht
    apply eval_congr_l (h t ht x hx)
    exact ⟨fun hQ => ⟨x, hx, hQ⟩, fun ⟨y, hy, hQ⟩ =>
      (show y = x from qval_unique_l hy hx) ▸ hQ⟩
  apply eval_congr_l hall
  constructor
  · intro h x
    obtain ⟨t, ht, hx⟩ := value_name_l x
    obtain ⟨y, hy, hQ⟩ := h t ht
    exact (show y = x from qval_unique_l hy hx) ▸ hQ
  · intro h t ht
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U) ht
    exact ⟨x, hx, h x⟩

private theorem code_eval_mem_l {n} (s t : Term n) {ρ : Env M n} {η : Env E n}
    (hρ : Env_val_d hZF ρ η) :
    Eval_d M B R z U (Code_d M B R z (mem_code_m s t) ρ) ((E).mem (s.eval η) (t.eval η)) := by
  rw [funext fun p => propext (code_mem_l M hZF.1 B R z s t ρ p)]
  exact ⟨regular_mem_l O _ _, qval_mem_forcing_l O hZF hU (hρ s) (hρ t)⟩

private theorem code_eval_eq_l {n} (s t : Term n) {ρ : Env M n} {η : Env E n}
    (hρ : Env_val_d hZF ρ η) :
    Eval_d M B R z U (Code_d M B R z (eq_code_m s t) ρ) (s.eval η = t.eval η) := by
  rw [funext fun p => propext (code_eq_l M hZF.1 B R z s t ρ p)]
  exact ⟨regular_eq_l O hZF (qval_name_l (hρ s)) (qval_name_l (hρ t)),
    qval_eq_l O hZF hU (hρ s) (hρ t)⟩

/-- 同时核验正则性及全部连接词、量词的求值真值。 -/
theorem formula_eval_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env M n) (η : Env E n) (hρ : Env_val_d hZF ρ η) :
    Eval_d M B R z U (Forces_d M B R z φ ρ) (Formula.satisfies η φ) := by
  unfold Forces_d
  induction φ <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum =>
    simp only [force_code_m, Code_d, Formula.satisfies_falsum_iff]
    refine ⟨⟨fun _ _ _ _ h => h, fun p hp hn hd => ?_⟩, ?_⟩
    · obtain ⟨q, _, hq⟩ := hd p (below_refl_l O hp hn)
      exact hq
    · exact ⟨fun ⟨_, _, h⟩ => h, False.elim⟩
  case truth =>
    simp only [force_code_m, Code_d, Formula.satisfies_truth_iff]
    exact ⟨⟨fun _ _ _ _ h => h, fun _ _ _ _ => trivial⟩,
      ⟨fun _ => trivial, fun _ => hU.inhabited.elim fun p hp => ⟨p, hp, trivial⟩⟩⟩
  case mem s t =>
    simp only [force_code_m, Formula.satisfies_mem_iff]
    exact code_eval_mem_l O hZF hU s t hρ
  case atom r _ ts =>
    cases r
    · apply eval_congr_l (code_eval_eq_l O hZF hU (ts 0) (ts 1) hρ)
      simp only [Formula.satisfies_atom_extensionalEq_iff]
      change ((ts 0).eval η = (ts 1).eval η) ↔ _
      exact ⟨fun h x => congrArg (fun y => (E).mem x y) h |>.to_iff,
        fun h => (extension_ext_l O hZF hU).eq_of_same_members _ _ h⟩
    · simp only [force_code_m, Formula.satisfies_atom_subset_iff]
      change Eval_d M B R z U (Code_d M B R z (all_code_m _) ρ)
        (∀ x : (E).Domain, (E).mem x ((ts 0).eval η) → (E).mem x ((ts 1).eval η))
      apply code_eval_all_l O hZF hU
        (imp_code_m_freeClosed _ _ (mem_code_m_freeClosed _ _ rfl (by simpa using hφ 0))
          (mem_code_m_freeClosed _ _ rfl (by simpa using hφ 1)))
      intro t ht x hx
      exact code_eval_imp_l O hZF hU
        (mem_code_m_freeClosed _ _ rfl (by simpa using hφ 0))
        (mem_code_m_freeClosed _ _ rfl (by simpa using hφ 1))
        (by simpa only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken] using
          code_eval_mem_l O hZF hU .newest (ts 0).weaken (env_val_push_l hZF hρ hx))
        (by simpa only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken] using
          code_eval_mem_l O hZF hU .newest (ts 1).weaken (env_val_push_l hZF hρ hx))
  case neg φ ih =>
    simp only [force_code_m, Formula.satisfies_neg_iff]
    exact code_eval_neg_l O hZF hU (force_code_closed_l φ hφ) (ih hφ ρ η hρ)
  case conj φ ψ ih jh =>
    simp only [force_code_m, Formula.satisfies_conj_iff]
    exact code_eval_conj_l hU (ih hφ.1 ρ η hρ) (jh hφ.2 ρ η hρ)
  case disj φ ψ ih jh =>
    have hφ' := force_code_closed_l φ hφ.1
    have hψ' := force_code_closed_l ψ hφ.2
    have h := code_eval_conj_l hU (code_eval_neg_l O hZF hU hφ' (ih hφ.1 ρ η hρ))
      (code_eval_neg_l O hZF hU hψ' (jh hφ.2 ρ η hρ))
    have hc : (Definitional.Formula.conj (neg_code_m (force_code_m φ)) (neg_code_m (force_code_m ψ))).FreeClosed := by
      simp only [Definitional.Formula.FreeClosed]; exact ⟨neg_code_m_freeClosed _ hφ', neg_code_m_freeClosed _ hψ'⟩
    apply eval_congr_l (code_eval_neg_l O hZF hU hc h)
    classical
    simp only [Formula.satisfies_disj_iff, not_and, Classical.not_not]
    exact Classical.or_iff_not_imp_left.symm
  case imp φ ψ ih jh =>
    simp only [force_code_m, Formula.satisfies_imp_iff]
    exact code_eval_imp_l O hZF hU
      (force_code_closed_l φ hφ.1) (force_code_closed_l ψ hφ.2) (ih hφ.1 ρ η hρ) (jh hφ.2 ρ η hρ)
  case iff φ ψ ih jh =>
    simp only [force_code_m, Formula.satisfies_iff_iff]
    have h := code_eval_imp_l O hZF hU (force_code_closed_l φ hφ.1) (force_code_closed_l ψ hφ.2)
      (ih hφ.1 ρ η hρ) (jh hφ.2 ρ η hρ)
    have k := code_eval_imp_l O hZF hU (force_code_closed_l ψ hφ.2) (force_code_closed_l φ hφ.1)
      (jh hφ.2 ρ η hρ) (ih hφ.1 ρ η hρ)
    exact eval_congr_l (code_eval_conj_l hU h k) ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
  case forallE φ ih =>
    simp only [force_code_m, Formula.satisfies_forall_iff]
    exact code_eval_all_l O hZF hU (force_code_closed_l φ hφ)
      (fun t _ x hx => ih hφ (ρ.push t) (η.push x) (env_val_push_l hZF hρ hx))
  case existsE φ ih =>
    have hc := force_code_closed_l φ hφ
    have h := code_eval_all_l O hZF hU (neg_code_m_freeClosed _ hc)
      (fun t _ x hx => code_eval_neg_l O hZF hU hc
        (ih hφ (ρ.push t) (η.push x) (env_val_push_l hZF hρ hx)))
    apply eval_congr_l (code_eval_neg_l O hZF hU (all_code_m_freeClosed _ (neg_code_m_freeClosed _ hc)) h)
    classical
    simp only [Formula.satisfies_exists_iff, Classical.not_forall, Classical.not_not]

theorem forcing_truth_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env M n) (η : Env E n) (hρ : Env_val_d hZF ρ η) :
    (∃ p, U p ∧ Forces_d M B R z φ ρ p) ↔ Formula.satisfies η φ :=
  (formula_eval_l O hZF hU φ hφ ρ η hρ).2

end YesMetaZFC.Model.Forcing.Internal
