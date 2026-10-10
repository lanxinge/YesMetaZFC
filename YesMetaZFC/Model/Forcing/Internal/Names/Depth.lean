import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 固定深度名称条目的内部下降

任意正的固定条目深度都允许实际公式的内部归纳。Kuratowski 条目的左坐标
在泛型解释下可由原名称的三层条目代表，供二步名称摊平的递归使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Entry_path_d (M : SetTheory.Structure.{u}) : Nat → M.Domain → M.Domain → Prop
  | 0, x, y => x = y
  | k + 1, x, y => ∃ a b, Entry_d M a b x ∧ Entry_path_d M k a y

def entry_path_m (k : Nat) {n} (x y : Term n) : Formula 1 n := match k with
  | 0 => Formula.extensionalEq x y
  | k + 1 => .existsE (.existsE (.conj (entry_m (.bound 1) .newest x.weaken.weaken)
      (entry_path_m k (.bound 1) y.weaken.weaken)))

@[simp] theorem entry_path_m_freeClosed (k : Nat) {n} (x y : Term n)
    (hx : x.freeSupport = []) (hy : y.freeSupport = []) : (entry_path_m k x y).FreeClosed := by
  induction k generalizing n with
  | zero => exact (Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨hx, hy⟩
  | succ k ih =>
    simp only [entry_path_m, Definitional.Formula.FreeClosed]
    exact ⟨entry_m_freeClosed _ _ _ rfl rfl (by simpa using hx), ih _ _ rfl (by simpa using hy)⟩

theorem entry_path_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) (k : Nat) {n}
    (ρ : Env M n) (x y : Term n) : Formula.satisfies ρ (entry_path_m k x y) ↔ Entry_path_d M k (x.eval ρ) (y.eval ρ) := by
  induction k generalizing n with
  | zero => exact Formula.satisfies_extensionalEq_iff_eq hE ρ x y
  | succ k ih =>
    simp only [entry_path_m, Entry_path_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hE, ih, Definitional.Term.eval_weaken]
    rfl

private def entry_all_schema_m {n} (φ : UnarySchema n) : UnarySchema n where
  body := .forallE (.forallE (.imp (entry_m (.bound 1) .newest (.bound 2))
    (pred_m φ (fun i => .bound ⟨i.val + 3, by omega⟩) (.bound 1))))

private theorem entry_all_schema_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (φ : UnarySchema n) (ρ : Env M n) (x : M.Domain) :
    (entry_all_schema_m φ).denote ρ x ↔ ∀ a b, Entry_d M a b x → φ.denote ρ a := by
  simp only [UnarySchema.denote, entry_all_schema_m, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, entry_sat_l M hE, pred_sat_l M]
  rfl

private def entry_window_m {n} (φ : UnarySchema n) : Nat → UnarySchema n
  | 0 => { body := .truth }
  | k + 1 => { body := .conj φ.body (entry_all_schema_m (entry_window_m φ k)).body }

private theorem entry_window_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (φ : UnarySchema n) (ρ : Env M n) (k : Nat) (x : M.Domain) :
    (entry_window_m φ k).denote ρ x ↔ ∀ j, j < k → ∀ y, Entry_path_d M j x y → φ.denote ρ y := by
  induction k generalizing x with
  | zero =>
    simp only [entry_window_m, UnarySchema.denote, Formula.satisfies_truth_iff]
    exact ⟨fun _ j hj => False.elim (Nat.not_lt_zero j hj), fun _ => True.intro⟩
  | succ k ih =>
    have ht : (entry_window_m φ (k + 1)).denote ρ x ↔
        φ.denote ρ x ∧ ∀ a b, Entry_d M a b x → (entry_window_m φ k).denote ρ a := by
      exact (Formula.satisfies_conj_iff _ _ _).trans (and_congr Iff.rfl (entry_all_schema_l hE _ ρ x))
    rw [ht]
    constructor
    · rintro ⟨hx, hh⟩ j hj y hy
      cases j with
      | zero => exact hy ▸ hx
      | succ j =>
        obtain ⟨a, b, hab, hay⟩ := hy
        exact (ih a).mp (hh a b hab) j (Nat.lt_of_succ_lt_succ hj) y hay
    · intro hh
      exact ⟨hh 0 (Nat.zero_lt_succ k) x rfl, fun a b hab => (ih a).mpr
        (fun j hj y hy => hh (j + 1) (Nat.succ_lt_succ hj) y ⟨a, b, hab, hy⟩)⟩

/-- 任意固定正深度的条目下降归纳，正文始终是一条原公式。 -/
theorem entry_path_ind_l {M : SetTheory.Structure.{u}} (hE : Extensional M) (hI : Mem_ind_d M)
    (k : Nat) (hk : 0 < k) {n} (φ : UnarySchema n) (ρ : Env M n)
    (h : ∀ x, (∀ y, Entry_path_d M k x y → φ.denote ρ y) → φ.denote ρ x) : ∀ x, φ.denote ρ x := by
  cases k with
  | zero => exact False.elim (Nat.not_lt_zero 0 hk)
  | succ k =>
    have hall := entry_ind_l hI (entry_window_m φ (k + 1)) ρ (fun x ih =>
      (entry_window_l hE φ ρ (k + 1) x).mpr (by
        intro j hj y hy
        cases j with
        | zero =>
          have hx : φ.denote ρ x := h x (fun z ⟨a, b, hab, haz⟩ =>
            (entry_window_l hE φ ρ (k + 1) a).mp (ih a b hab) k (Nat.lt_succ_self k) z haz)
          exact hy ▸ hx
        | succ j =>
          obtain ⟨a, b, hab, hay⟩ := hy
          exact (entry_window_l hE φ ρ (k + 1) a).mp (ih a b hab) j (by omega) y hay))
    exact fun x => (entry_window_l hE φ ρ (k + 1) x).mp (hall x) 0 (Nat.zero_lt_succ k) x rfl

theorem entry_path_name_l {M : SetTheory.Structure.{u}} {B x y} (k : Nat)
    (hx : Name_d M B x) (h : Entry_path_d M k x y) : Name_d M B y := by
  induction k generalizing x with
  | zero => exact h ▸ hx
  | succ k ih =>
    obtain ⟨a, b, hab, hay⟩ := h
    exact ih (name_entry_l M hx hab).1 hay

/-- 任意原对象的固定深度条目后继都组成实际模型集合。 -/
theorem entry_path_set_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) (k : Nat) (x : M.Domain) :
    ∃ D, ∀ y, M.mem y D ↔ Entry_path_d M k x y := by
  induction k generalizing x with
  | zero =>
    obtain ⟨D, hD⟩ := KP.exists_pair (ZF.modelsKP hZF) x x
    exact ⟨D, fun y => (hD y).trans ⟨fun hh => hh.elim Eq.symm Eq.symm, fun hh => Or.inl hh.symm⟩⟩
  | succ k ih =>
    obtain ⟨A, hA⟩ := entry_domain_l M hZF x
    let ρ : Env M 0 := ⟨Fin.elim0, fun _ => x⟩
    let φ : BinarySchema 0 := {
      body := .forallE (.iff (.mem .newest (.bound 1)) (entry_path_m k (.bound 2) .newest)) }
    have hφ a D : φ.denote ρ a D ↔ ∀ y, M.mem y D ↔ Entry_path_d M k a y := by
      simp only [BinarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
        Formula.satisfies_mem_iff, entry_path_sat_l hZF.1]
      rfl
    obtain ⟨F, hF⟩ := ZF.exists_functionalImageOn hZF φ ρ A (fun a _ => by
      obtain ⟨D, hD⟩ := ih a
      exact ⟨D, (hφ a D).mpr hD⟩) (fun a _ D E hD hE =>
        hZF.1.eq_of_same_members D E (fun y => ((hφ a D).mp hD y).trans ((hφ a E).mp hE y).symm))
    obtain ⟨D, hD⟩ := KP.exists_union (ZF.modelsKP hZF) F
    refine ⟨D, fun y => ?_⟩
    constructor
    · intro hy
      obtain ⟨E, hE, hy⟩ := (hD y).mp hy
      obtain ⟨a, ha, hE⟩ := (hF E).mp hE
      obtain ⟨b, hab⟩ := (hA a).mp ha
      exact ⟨a, b, hab, ((hφ a E).mp hE y).mp hy⟩
    · rintro ⟨a, b, hab, hay⟩
      obtain ⟨E, hE⟩ := ih a
      exact (hD y).mpr ⟨E, (hF E).mpr ⟨a, (hA a).mpr ⟨b, hab⟩, (hφ a E).mpr hE⟩, (hE y).mpr hay⟩

/-- 泛型解释中条目的左坐标，可由原名称恰好三层下降的名称代表。 -/
theorem qval_entry_path_l {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {t} {v a b : (extension_l M hZF B R z U).Domain} (ht : Qval_d M B R z U t v)
    (h : Entry_d (extension_l M hZF B R z U) a b v) : ∃ x, Entry_path_d M 3 t x ∧ Qval_d M B R z U x a := by
  obtain ⟨p, hp, hpv⟩ := h
  obtain ⟨q, hqp, haq⟩ := (kpair_union_l _ hp a).mpr (Or.inl rfl)
  obtain ⟨s, c, hsc, _, hsp⟩ := (qval_mem_l O hZF hU ht).mp hpv
  obtain ⟨u, d, hud, _, huq⟩ := (qval_mem_l O hZF hU hsp).mp hqp
  obtain ⟨x, e, hxe, _, hxa⟩ := (qval_mem_l O hZF hU huq).mp haq
  exact ⟨x, ⟨s, c, hsc, u, d, hud, x, e, hxe, rfl⟩, hxa⟩

end YesMetaZFC.Model.Forcing.Internal
