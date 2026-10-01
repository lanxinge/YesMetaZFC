import YesMetaZFC.Model.SetTheory.Internal.CompileSemantics

/-! # 有限公式反射的参数块

参数量词块仍是原生产公式。以下语义把块与任意有限模型赋值对应起来，供收集
全部参数组的见证使用；不把外部赋值族直接当作模型内集合。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def lr_env_l {d} (ρ : Env M d) : {k : Nat} → (Fin k → M.Domain) → Env M (d+k)
  | 0, _ => ρ
  | k+1, v => (lr_env_l ρ (fun i : Fin k => v i.succ)).push (v 0)

theorem lr_env_bound_l {d k} (ρ : Env M d) (v : Fin k → M.Domain) (i : Fin k) :
    (lr_env_l ρ v).bound ⟨i.val, by omega⟩ = v i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => exact Fin.cases rfl (fun j => ih (fun i => v i.succ) j) i

theorem lr_env_shift_l {d k} (ρ : Env M d) (v : Fin k → M.Domain) (i : Fin d) :
    (lr_env_l ρ v).bound ⟨i.val+k, by omega⟩ = ρ.bound i := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun i => v i.succ)

theorem lr_env_free_l {d k} (ρ : Env M d) (v : Fin k → M.Domain) : (lr_env_l ρ v).free = ρ.free := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun i => v i.succ)

def lr_shift_l {d} (k : Nat) (x : Term d) : Term (d+k) := x.rename (fun i => ⟨i.val+k, by omega⟩)

@[simp] theorem lr_shift_closed_l {d} (k : Nat) (x : Term d) : (lr_shift_l k x).freeSupport = x.freeSupport :=
  Definitional.Term.freeSupport_rename _ _

theorem lr_shift_sat_l {d k} (ρ : Env M d) (v : Fin k → M.Domain) (x : Term d) :
    (lr_shift_l k x).eval (lr_env_l ρ v) = x.eval ρ := by
  cases x with
  | bound i => exact lr_env_shift_l ρ v i
  | free i => exact congrFun (lr_env_free_l ρ v) i

def lr_all_m : (k : Nat) → {d : Nat} → Term d → Formula 1 (d+k) → Formula 1 d
  | 0, _, _, φ => φ
  | k+1, _, X, φ => lr_all_m k X (Formula.forallMem (lr_shift_l k X) φ)

@[simp] theorem lr_all_closed_l (k : Nat) {d} (X : Term d) (φ : Formula 1 (d+k))
    (hX : X.freeSupport = []) (hφ : φ.FreeClosed) : (lr_all_m k X φ).FreeClosed := by
  induction k with
  | zero => exact hφ
  | succ k ih =>
    apply ih
    simp only [Formula.forallMem, Definitional.Formula.FreeClosed, Definitional.Term.freeSupport_newest,
      Definitional.Term.freeSupport_weaken, lr_shift_closed_l]
    exact ⟨⟨trivial, hX⟩, hφ⟩

theorem lr_all_sat_l (k : Nat) {d} (ρ : Env M d) (X : Term d) (φ : Formula 1 (d+k)) :
    Formula.satisfies ρ (lr_all_m k X φ) ↔ ∀ v : Fin k → M.Domain,
      (∀ i, M.mem (v i) (X.eval ρ)) → Formula.satisfies (lr_env_l ρ v) φ := by
  induction k with
  | zero => exact ⟨fun h _ _ => h, fun h => h Fin.elim0 (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    rw [lr_all_m, ih]
    simp only [Formula.satisfies_forallMem_iff, lr_shift_sat_l]
    constructor
    · exact fun h v hv => h (fun i => v i.succ) (fun i => hv i.succ) (v 0) (hv 0)
    · intro h v hv x hx
      simpa only [lr_env_l, Fin.cases_zero, Fin.cases_succ] using h (Fin.cases x v) (Fin.cases hx hv)

/-- 自由闭合的原公式只读取 bound 参数，不要求两个自由环境相同。 -/
theorem lr_env_congr_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ η : Env M n)
    (h : ∀ i, ρ.bound i = η.bound i) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have ht {n} (ρ η : Env M n) (h : ∀ i, ρ.bound i = η.bound i) (t : Term n)
      (hc : t.freeSupport = []) : t.eval ρ = t.eval η := by
    cases t with
    | free _ => simp at hc
    | bound i => exact h i
  induction φ <;> simp only [Definitional.Formula.FreeClosed] at hφ
    <;> try simp only [Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff]
  case mem s t => simp only [Formula.satisfies_mem_iff, ht ρ η h s hφ.1, ht ρ η h t hφ.2]
  case atom r _ ts =>
    cases r <;> simp only [Formula.satisfies_atom_extensionalEq_iff, Formula.satisfies_atom_subset_iff,
      ht ρ η h (ts 0) (hφ 0), ht ρ η h (ts 1) (hφ 1)]
  case neg φ ih => exact not_congr (ih hφ ρ η h)
  case conj φ ψ ih jh => exact and_congr (ih hφ.1 ρ η h) (jh hφ.2 ρ η h)
  case disj φ ψ ih jh => exact or_congr (ih hφ.1 ρ η h) (jh hφ.2 ρ η h)
  case imp φ ψ ih jh => exact imp_congr (ih hφ.1 ρ η h) (jh hφ.2 ρ η h)
  case iff φ ψ ih jh => exact iff_congr (ih hφ.1 ρ η h) (jh hφ.2 ρ η h)
  case forallE φ ih => exact forall_congr' (fun x => ih hφ (ρ.push x) (η.push x) (Fin.cases rfl h))
  case existsE φ ih => exact exists_congr (fun x => ih hφ (ρ.push x) (η.push x) (Fin.cases rfl h))

end YesMetaZFC.SetTheory
