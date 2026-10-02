import YesMetaZFC.SetTheory.InnerModel.OD.Brackets

/-! # 固定参数下的有限定义代入

每个参数以一个序数码给出，用原 AST 的存在量词块同时解码。量词块只对源
公式的外部元数递归，内部定义码及赋值仍允许非标准。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def od_ex_m : (k : Nat) → {d : Nat} → Formula 1 (d+k) → Formula 1 d
  | 0, _, φ => φ
  | k+1, _, φ => od_ex_m k (.existsE φ)

@[simp] theorem od_ex_closed_l (k : Nat) {d} (φ : Formula 1 (d+k)) (h : φ.FreeClosed) :
    (od_ex_m k φ).FreeClosed := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (.existsE φ) (by simpa only [Definitional.Formula.FreeClosed] using h)

theorem od_ex_sat_l (k : Nat) {d} (ρ : Env M d) (φ : Formula 1 (d+k)) :
    Formula.satisfies ρ (od_ex_m k φ) ↔ ∃ v : Fin k → M.Domain, Formula.satisfies (lr_env_l ρ v) φ := by
  induction k with
  | zero => exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ k ih =>
    rw [od_ex_m, ih]
    simp only [Formula.satisfies_exists_iff]
    constructor
    · rintro ⟨v, x, h⟩
      exact ⟨Fin.cases x v, by simpa only [lr_env_l, Fin.cases_zero, Fin.cases_succ] using h⟩
    · exact fun ⟨v, h⟩ => ⟨fun i => v i.succ, v 0, h⟩

def ob_subst_s {n} (φ : UnarySchema n) : BinarySchema n where
  body := od_ex_m n (.conj (lr_and_m (fun i : Fin n => ob_eval_m
    (lr_shift_l n (.bound ⟨i.val+2, by omega⟩)) (lr_shift_l n (.bound 1)) (.bound ⟨i.val, by omega⟩)))
    (pred_m φ (fun i => .bound ⟨i.val, by omega⟩) (lr_shift_l n .newest)))
  freeClosed := od_ex_closed_l n _ (by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])

theorem ob_subst_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n} (φ : UnarySchema n) (ρ : Env M n) (A x : M.Domain) :
    (ob_subst_s φ).denote ρ A x ↔ ∃ v : Fin n → M.Domain,
      (∀ i, Ob_eval_d I (ρ.bound i) A (v i)) ∧ φ.denote ⟨v, ρ.free⟩ x := by
  simp only [ob_subst_s, BinarySchema.denote, od_ex_sat_l, Formula.satisfies_conj_iff,
    lr_and_sat_l, ob_eval_sat_l I hE, pred_sat_l, lr_shift_sat_l]
  simp only [Definitional.Term.eval, lr_env_bound_l, lr_env_free_l]
  rfl

/-- OD[A] 对任意有限个 OD[A] 参数的唯一原公式定义封闭。 -/
theorem ob_closed_l (hZF : M.Models ZF) (A : M.Domain) {n} (φ : UnarySchema n) (ρ : Env M n)
    (hρ : ∀ i, Ob_d A (ρ.bound i)) {x} (hx : ∀ y, φ.denote ρ y ↔ y = x) : Ob_d A x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨q, hq⟩ := Classical.axiomOfChoice (fun i => (ob_code_l I hZF).mp (hρ i))
  let η : Env M n := ⟨q, ρ.free⟩
  refine ob_source_l hZF (ob_subst_s φ) η (fun i => (hq i).elim fun _ h => od_eval_ordinal_l I hZF h.1)
    (fun y => (ob_subst_sat_l I hZF.1 φ η A y).trans ?_)
  constructor
  · rintro ⟨v, hv, hy⟩
    have eq : v = ρ.bound := funext fun i => ob_eval_unique_l I hZF (hv i) (hq i)
    subst v
    exact (hx y).mp hy
  · intro hy
    exact ⟨ρ.bound, hq, (hx y).mpr hy⟩

theorem ob_trans_l (hZF : M.Models ZF) {A B x : M.Domain} (hA : Ob_d B A) (hx : Ob_d A x) : Ob_d B x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨q, hq⟩ := (ob_code_l I hZF).mp hx
  have ho := hq.elim fun _ h => od_eval_ordinal_l I hZF h.1
  let φ : UnarySchema 2 := { body := ob_eval_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases A (fun _ => q), fun _ => A⟩
  exact ob_closed_l hZF B φ ρ
    (Fin.cases hA (fun _ => ob_ordinal_l hZF B ho)) (fun y => (ob_eval_sat_l I hZF.1 _ _ _ _).trans
      ⟨fun h => ob_eval_unique_l I hZF h hq, fun he => he.symm ▸ hq⟩)

theorem ob_of_od_l (hZF : M.Models ZF) (A : M.Domain) {x : M.Domain} (hx : Od_d x) : Ob_d A x := by
  obtain ⟨n, φ, ρ, hρ, hx⟩ := (od_iff_external_l hZF).mp hx
  let ψ : BinarySchema n := {
    body := pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) .newest }
  refine ob_source_l hZF ψ ρ hρ (fun y => ?_)
  exact (pred_sat_l M φ ((ρ.push A).push y) _ _).trans (hx y)

theorem ob_pair_l (hZF : M.Models ZF) (B : M.Domain) {a b p : M.Domain}
    (ha : Ob_d B a) (hb : Ob_d B b) (hp : KPair_d M p a b) : Ob_d B p := by
  let φ : UnarySchema 2 := { body := kpair_m .newest (.bound 1) (.bound 2) }
  let ρ : Env M 2 := ⟨Fin.cases a (fun _ => b), fun _ => a⟩
  exact ob_closed_l hZF B φ ρ (Fin.cases ha (fun _ => hb)) (fun q =>
    (kpair_sat_l M hZF.1 _ _ _ _).trans ⟨fun h => kpair_unique_l M hZF.1 h hp, fun h => h.symm ▸ hp⟩)

theorem ob_pair_components_l (hZF : M.Models ZF) (B : M.Domain) {a b p : M.Domain}
    (h : Ob_d B p) (hp : KPair_d M p a b) : Ob_d B a ∧ Ob_d B b := by
  let ρ : Env M 1 := ⟨fun _ => p, fun _ => p⟩
  let φ : UnarySchema 1 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let ψ : UnarySchema 1 := { body := .existsE (kpair_m (.bound 2) .newest (.bound 1)) }
  have left y : φ.denote ρ y ↔ y = a := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]
    exact ⟨fun ⟨z, hz⟩ => (kpair_injective_l M hz hp).1, fun he => he.symm ▸ ⟨b, hp⟩⟩
  have right y : ψ.denote ρ y ↔ y = b := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]
    exact ⟨fun ⟨z, hz⟩ => (kpair_injective_l M hz hp).2, fun he => he.symm ▸ ⟨a, hp⟩⟩
  exact ⟨ob_closed_l hZF B φ ρ (fun _ => h) left, ob_closed_l hZF B ψ ρ (fun _ => h) right⟩

end YesMetaZFC.SetTheory.InnerModel
