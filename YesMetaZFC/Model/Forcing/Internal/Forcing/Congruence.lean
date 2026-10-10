import YesMetaZFC.Model.Forcing.Internal.Forcing.Rules

/-! # 局部等号替换与有界存在见证

先在一个条件以下逐公式证明等同名称的替换，再把存在见证移入目标名称的
内部闭支撑。这一步使二步迭代的稠密集证明保持为地模型中的集合论证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

private theorem mem_congr_l {p s t a b} (hs : Name_d M B s) (ht : Name_d M B t)
    (ha : Name_d M B a) (hb : Name_d M B b)
    (h : Eq_force_d M B R z p s a) (k : Eq_force_d M B R z p t b) :
    Mem_force_d M B R z p s t ↔ Mem_force_d M B R z p a b :=
  ⟨fun hm => mem_force_right_l O hZF ha ht hb k (mem_force_left_l O hZF hs ha ht h hm),
    fun hm => mem_force_right_l O hZF hs hb ht (eq_force_symm_l hZF ht hb k)
      (mem_force_left_l O hZF ha hs hb (eq_force_symm_l hZF hs ha h) hm)⟩

private theorem eq_congr_l {p s t a b} (hs : Name_d M B s) (ht : Name_d M B t)
    (ha : Name_d M B a) (hb : Name_d M B b)
    (h : Eq_force_d M B R z p s a) (k : Eq_force_d M B R z p t b) :
    Eq_force_d M B R z p s t ↔ Eq_force_d M B R z p a b :=
  ⟨fun he => eq_force_trans_l O hZF ha hs hb (eq_force_symm_l hZF hs ha h)
      (eq_force_trans_l O hZF hs ht hb he k),
    fun he => eq_force_trans_l O hZF hs ha ht h
      (eq_force_trans_l O hZF ha hb ht he (eq_force_symm_l hZF ht hb k))⟩

/-- 在 p 下，逐参数等号力迫允许替换任意原公式的名称赋值。 -/
theorem forces_congr_below_l {a n p} (φ : Formula a n) (ρ η : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) (hη : ∀ t : Term n, Name_d M B (t.eval η))
    (hp : M.mem p B) (he : ∀ t : Term n, Eq_force_d M B R z p (t.eval ρ) (t.eval η)) :
    ∀ q, Below_d M B R z q p → (Forces_d M B R z φ ρ q ↔ Forces_d M B R z φ η q) := by
  have hn {P Q : M.Domain → Prop} (h : ∀ q, Below_d M B R z q p → (P q ↔ Q q)) :
      ∀ q, Below_d M B R z q p → (Neg_d M B R z P q ↔ Neg_d M B R z Q q) :=
    fun q hq => forall_congr' fun r => imp_congr_right fun hr => not_congr (h r (below_trans_l O hp hr hq))
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ q, Below_d M B R z q p → (P q ↔ Q q))
      (k : ∀ q, Below_d M B R z q p → (V q ↔ W q)) :=
    fun q hq => and_congr (h q hq) (k q hq)
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {s} (hs : Name_d M B s) :
      ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  induction φ with
  | falsum => intro q _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => intro q _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    intro q hq
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact mem_congr_l O hZF (hρ s) (hρ t) (hη s) (hη t)
      (eq_force_lower_l O hZF (hρ s) (hη s) p q hp hq (he s))
      (eq_force_lower_l O hZF (hρ t) (hη t) p q hp hq (he t))
  | atom r _ ts =>
    cases r
    · intro q hq
      simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact eq_congr_l O hZF (hρ (ts 0)) (hρ (ts 1)) (hη (ts 0)) (hη (ts 1))
        (eq_force_lower_l O hZF (hρ (ts 0)) (hη (ts 0)) p q hp hq (he (ts 0)))
        (eq_force_lower_l O hZF (hρ (ts 1)) (hη (ts 1)) p q hp hq (he (ts 1)))
    · intro q hq
      simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      apply forall_congr'
      intro s
      apply imp_congr_right
      intro hs
      have hm (t : Term _) (r : M.Domain) (hr : Below_d M B R z r p) :=
        mem_congr_l O hZF hs (hρ t) hs (hη t) (eq_force_refl_l O hZF hr.1 hs)
          (eq_force_lower_l O hZF (hρ t) (hη t) p r hp hr (he t))
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (hn (hm (ts 1)))) q hq
  | neg φ ih =>
    simpa only [forces_neg_l hZF.1] using hn (ih ρ η hρ hη he)
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using hc (ih ρ η hρ hη he) (jh ρ η hρ hη he)
  | disj φ ψ ih jh =>
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (hn (ih ρ η hρ hη he)) (hn (jh ρ η hρ hη he)))
  | imp φ ψ ih jh =>
    simpa only [forces_imp_l hZF.1, Neg_d] using hn (hc (ih ρ η hρ hη he) (hn (jh ρ η hρ hη he)))
  | iff φ ψ ih jh =>
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1, Neg_d] using
      hc (hn (hc (ih ρ η hρ hη he) (hn (jh ρ η hρ hη he))))
        (hn (hc (jh ρ η hρ hη he) (hn (ih ρ η hρ hη he))))
  | forallE φ ih =>
    intro q hq
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    refine forall_congr' fun s => imp_congr_right fun hs => ih (ρ.push s) (η.push s) (push hρ hs) (push hη hs) ?_ q hq
    intro t
    cases t with
    | free i => exact he (.free i)
    | bound i => exact Fin.cases (eq_force_refl_l O hZF hp hs) (fun i => he (.bound i)) i
  | existsE φ ih =>
    have hall : ∀ q, Below_d M B R z q p →
        ((∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (ρ.push s)) q) ↔
          ∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (η.push s)) q) := by
      intro q hq
      refine forall_congr' fun s => imp_congr_right fun hs => ?_
      apply hn (ih (ρ.push s) (η.push s) (push hρ hs) (push hη hs) ?_) q hq
      intro t
      cases t with
      | free i => exact he (.free i)
      | bound i => exact Fin.cases (eq_force_refl_l O hZF hp hs) (fun i => he (.bound i)) i
    simpa only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d] using hn hall

/-- 隶属于 A 的任意名称见证可在加强后改用 A 的内部支撑中的代表。 -/
theorem bounded_witness_l {a n} (φ : Formula a (n + 1)) (ρ : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {W A p t}
    (hA : M.mem A W) (hW : Supp_d M B W) (ht : Name_d M B t)
    (hm : Mem_force_d M B R z p t A) (hφ : Forces_d M B R z φ (ρ.push t) p) :
    Dense_d M B R z (fun q => ∃ s, M.mem s W ∧ Mem_force_d M B R z q s A ∧
      Forces_d M B R z φ (ρ.push s) q) p := by
  have push {s} (hs : Name_d M B s) : ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  intro q hq
  obtain ⟨r, s, b, hr, hsA, hrb, he⟩ := hm.2 q hq
  obtain ⟨hsW, hb⟩ := supp_entry_l M hW hA hsA
  have hs : Name_d M B s := ⟨W, hsW, hW⟩
  have hφr := (forces_regular_l O hZF φ _ (push ht)).1 p r hm.1 (below_trans_l O hm.1 hr hq) hφ
  have hc := forces_congr_below_l O hZF φ (ρ.push t) (ρ.push s) (push ht) (push hs) hr.1
    (fun v => by
      cases v with
      | free i => exact eq_force_refl_l O hZF hr.1 (hρ (.free i))
      | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hr.1 (hρ (.bound i))) i)
  exact ⟨r, hr, s, hsW, mem_force_entry_l O hZF hr.1 hs hb hsA hrb,
    (hc r (below_refl_l O hr.1 hr.2.1)).mp hφr⟩

/-- 固定有限参数时，在原公式中替换一个被迫相等的名称；自由默认值无需名称假设。 -/
theorem forces_name_congr_l {n p s t} (φ : UnarySchema n) (ρ : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) (hs : Name_d M B s) (ht : Name_d M B t)
    (hp : M.mem p B) (hz : p ≠ z) (he : Eq_force_d M B R z p s t) :
    Forces_d M B R z φ.body (ρ.push s) p ↔ Forces_d M B R z φ.body (ρ.push t) p := by
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  have push a (ha : Name_d M B a) : ∀ v : Term (n+1), Name_d M B (v.eval (η.push a)) := by
    intro v
    cases v with
    | free _ => exact hs
    | bound i => exact Fin.cases ha hρ i
  have hc := forces_congr_below_l O hZF φ.body (η.push s) (η.push t) (push s hs) (push t ht) hp (by
    intro v
    cases v with
    | free _ => exact eq_force_refl_l O hZF hp hs
    | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hp (hρ i)) i)
  exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).trans
    ((hc p (below_refl_l O hp hz)).trans
      (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).symm)

/-- 有界存在公式的全部见证密度由模型内名称支撑自动提供。 -/
theorem bounded_exists_l {a n} (φ : Formula a (n + 1)) (ρ : Env M n) (t : Term n)
    (hρ : ∀ v : Term n, Name_d M B (v.eval ρ)) {W p}
    (hW : Supp_d M B W) (ht : M.mem (t.eval ρ) W)
    (h : Forces_d M B R z (.existsE (.conj (.mem .newest t.weaken) φ)) ρ p) :
    Dense_d M B R z (fun q => ∃ s, M.mem s W ∧ Mem_force_d M B R z q s (t.eval ρ) ∧
      Forces_d M B R z φ (ρ.push s) q) p := by
  intro q hq
  obtain ⟨r, hr, s, hs, h⟩ := forces_exists_dense_l hZF.1 h q hq
  obtain ⟨hm, hφ⟩ := (forces_conj_l _ _ _ r).mp h
  have hm : Mem_force_d M B R z r s (t.eval ρ) := by
    simpa only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken] using
      (forces_mem_l hZF.1 _ _ _ r).mp hm
  obtain ⟨v, hv, hw⟩ := bounded_witness_l O hZF φ ρ hρ ht hW hs hm hφ r (below_refl_l O hr.1 hr.2.1)
  exact ⟨v, below_trans_l O hq.1 hv hr, hw⟩

end YesMetaZFC.Model.Forcing.Internal
