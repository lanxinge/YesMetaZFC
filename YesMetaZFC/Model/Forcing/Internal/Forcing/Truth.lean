import YesMetaZFC.Model.Forcing.Internal.Forcing.Logic
import YesMetaZFC.Model.Forcing.Internal.Extension.Quotient

/-! # 全部原公式的内部力迫真值定理

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
