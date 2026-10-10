import YesMetaZFC.Model.Forcing.Internal.Automorphism.Atomic
import YesMetaZFC.Model.Forcing.Internal.Forcing.Rules

/-! # 全部原公式的自同构不变性

否定通过条件双射搬运，量词通过名称的严格逆作用搬运。正文是原 Project 公式，
参数作用仍由实际内部 Nmap 图见证；不假定外部名称域良基或存在全局代表选择。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z F : M.Domain}

private theorem aut_neg_l (h : Aut_d M B R z F) {P Q : M.Domain → Prop}
    (he : ∀ p q, Entry_d M p q F → (P p ↔ Q q)) {p q} (hpq : Entry_d M p q F) :
    Neg_d M B R z P p ↔ Neg_d M B R z Q q := by
  constructor
  · intro hn s hs hQ
    obtain ⟨r, hrs⟩ := h.onto s hs.1
    exact hn r ((aut_below_l h hpq hrs).mpr hs) ((he r s hrs).mpr hQ)
  · intro hn r hr hP
    obtain ⟨s, hrs⟩ := h.total r hr.1
    exact hn s ((aut_below_l h hpq hrs).mp hr) ((he r s hrs).mp hP)

private theorem aut_all_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {P Q : M.Domain → Prop}
    (he : ∀ x y, Name_d M B x → Nmap_d M F x y → (P x ↔ Q y)) :
    (∀ x, Name_d M B x → P x) ↔ ∀ y, Name_d M B y → Q y := by
  constructor
  · intro hP y hy
    obtain ⟨x, hx, hxy⟩ := aut_nmap_onto_l hZF h hy
    exact (he x y hx hxy).mp (hP x hx)
  · intro hQ x hx
    obtain ⟨y, hxy⟩ := nmap_exists_l M hZF F x
    exact (he x y hx hxy).mpr (hQ y (nmap_name_l M hZF (fun p q hpq => (h.domain p q hpq).2) hxy))

/-- 同时作用于条件和全部名称参数，保持任意原公式的力迫关系。 -/
theorem aut_forces_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (ρ η : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
    (hρη : ∀ t : Term n, Nmap_d M F (t.eval ρ) (t.eval η))
    {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η q := by
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
      {x} (hx : Name_d M B x) : ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push x)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hx (fun i => hρ (.bound i)) i
  have pair {n} {ρ η : Env M n} (hρη : ∀ t : Term n, Nmap_d M F (t.eval ρ) (t.eval η))
      {x y} (hxy : Nmap_d M F x y) :
      ∀ t : Term (n+1), Nmap_d M F (t.eval (ρ.push x)) (t.eval (η.push y)) := by
    intro t
    cases t with
    | free i => exact hρη (.free i)
    | bound i => exact Fin.cases hxy (fun i => hρη (.bound i)) i
  have hn := @aut_neg_l M B R z F h
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ p q, Entry_d M p q F → (P p ↔ Q q))
      (k : ∀ p q, Entry_d M p q F → (V p ↔ W q)) :=
    fun p q hpq => and_congr (h p q hpq) (k p q hpq)
  induction φ generalizing p q with
  | falsum => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact aut_mem_force_l hZF h (hρ s) (hρ t) (hρη s) (hρη t) hpq
  | atom r _ ts =>
    cases r
    · simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact aut_eq_force_l hZF h (hρ (ts 0)) (hρ (ts 1)) (hρη (ts 0)) (hρη (ts 1)) hpq
    · simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      apply aut_all_l hZF h
      intro x y hx hxy
      have hm (t : Term _) (p q) (hpq : Entry_d M p q F) :=
        aut_mem_force_l hZF h hx (hρ t) hxy (hρη t) hpq
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (fun _ _ h => hn (hm (ts 1)) h)) hpq
  | neg φ ih =>
    simpa only [forces_neg_l hZF.1] using hn (fun _ _ h => ih ρ η hρ hρη h) hpq
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using and_congr (ih ρ η hρ hρη hpq) (jh ρ η hρ hρη hpq)
  | disj φ ψ ih jh =>
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (fun _ _ h => hn (fun _ _ h => ih ρ η hρ hρη h) h)
        (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq
  | imp φ ψ ih jh =>
    simpa only [forces_imp_l hZF.1] using
      hn (hc (fun _ _ h => ih ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq
  | iff φ ψ ih jh =>
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1] using
      and_congr
        (hn (hc (fun _ _ h => ih ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq)
        (hn (hc (fun _ _ h => jh ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => ih ρ η hρ hρη h) h)) hpq)
  | forallE φ ih =>
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    exact aut_all_l hZF h (fun x y hx hxy => ih (ρ.push x) (η.push y) (push hρ hx) (pair hρη hxy) hpq)
  | existsE φ ih =>
    simp only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d]
    simpa only [Neg_d] using hn (fun _ _ hpq => aut_all_l hZF h (fun x y hx hxy => hn
      (fun _ _ hpq => ih (ρ.push x) (η.push y) (push hρ hx) (pair hρη hxy) hpq) hpq)) hpq

/-- 自由闭合正文只需有限 bound 参数的名称及作用证书。 -/
theorem aut_forces_closed_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (hφ : φ.FreeClosed) (ρ η : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i))
    (hρη : ∀ i, Nmap_d M F (ρ.bound i) (η.bound i)) {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η q := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hn := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  obtain ⟨v, hv⟩ := nmap_exists_l M hZF F e
  let ρ' : Env M n := ⟨ρ.bound, fun _ => e⟩
  let η' : Env M n := ⟨η.bound, fun _ => v⟩
  have hρ' (t : Term n) : Name_d M B (t.eval ρ') := by
    cases t with
    | free _ => exact hn
    | bound i => exact hρ i
  have hρη' (t : Term n) : Nmap_d M F (t.eval ρ') (t.eval η') := by
    cases t with
    | free _ => exact hv
    | bound i => exact hρη i
  exact (forces_env_l hZF.1 φ hφ ρ ρ' (fun _ => rfl) p).trans
    ((aut_forces_l hZF h φ ρ' η' hρ' hρη' hpq).trans
      (forces_env_l hZF.1 φ hφ η' η (fun _ => rfl) q))

/-- 固定基条件后，带任意有限地参数的力迫真值沿条件自同构保持。 -/
theorem aut_check_forces_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (hφ : φ.FreeClosed) (ρ : Env M n) {b}
    (hb : Entry_d M b b F) (hρ : ∀ i, ∃ x, Check_d M b x (ρ.bound i))
    {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ ρ q :=
  aut_forces_closed_l hZF h φ hφ ρ ρ
    (fun i => (hρ i).elim fun _ hx => check_name_l M (check_range_l M hZF) (h.domain b b hb).1 hx)
    (fun i => (hρ i).elim fun _ hx => aut_check_fixed_l hZF h hb hx) hpq

end YesMetaZFC.Model.Forcing.Internal
