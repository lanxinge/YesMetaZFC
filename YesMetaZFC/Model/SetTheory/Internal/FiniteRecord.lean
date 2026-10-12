import YesMetaZFC.SetTheory.InnerModel.Separation.Tuple
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 固定元数记录的原一阶公式

记录仍是模型内的右嵌套有序对。这里只对语法元数递归；游戏历史的长度
不进入此元递归。任意固定原公式可直接作用于记录的全部坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rt_push_d {d} (ρ : Env M d) : (n : Nat) → (Fin n → M.Domain) → Env M (d+n)
  | 0, _ => ρ
  | n+1, v => (rt_push_d ρ n (fun i => v i.succ)).push (v 0)

def rt_exists_m {d} : (n : Nat) → Formula 1 (d+n) → Formula 1 d
  | 0, φ => φ
  | n+1, φ => rt_exists_m n (.existsE φ)

theorem rt_exists_closed_l {d n} (φ : Formula 1 (d+n)) : (rt_exists_m n φ).FreeClosed ↔ φ.FreeClosed := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.existsE φ)

theorem rt_exists_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (d+n)) :
    Formula.satisfies ρ (rt_exists_m n φ) ↔ ∃ v : Fin n → M.Domain, Formula.satisfies (rt_push_d ρ n v) φ := by
  induction n with
  | zero => exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ n ih =>
    rw [rt_exists_m, ih]
    simp only [Formula.satisfies_exists_iff]
    constructor
    · rintro ⟨v, x, h⟩
      refine ⟨(Fin.cases x v : Fin (n+1) → M.Domain), ?_⟩
      simpa only [rt_push_d, Fin.cases_zero, Fin.cases_succ] using h
    · rintro ⟨v, h⟩
      exact ⟨fun i => v i.succ, v 0, h⟩

theorem rt_push_new_l {d n} (ρ : Env M d) (v : Fin n → M.Domain) (i : Fin n) :
    (rt_push_d ρ n v).bound ⟨i.val, by omega⟩ = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact ih (fun i => v i.succ) i

theorem rt_push_old_l {d n} (ρ : Env M d) (v : Fin n → M.Domain) (i : Fin d) :
    (rt_push_d ρ n v).bound ⟨n+i.val, by omega⟩ = ρ.bound i := by
  induction n with
  | zero =>
    simp only [rt_push_d, Nat.zero_add]
    exact congrArg ρ.bound (Fin.ext rfl)
  | succ n ih =>
    have eq : (⟨n+1+i.val, by omega⟩ : Fin (d+(n+1))) = (⟨n+i.val, by omega⟩ : Fin (d+n)).succ := by
      apply Fin.ext
      change n+1+i.val = n+i.val+1
      omega
    rw [eq]
    exact ih (fun i => v i.succ)

theorem rt_push_free_l {d n} (ρ : Env M d) (v : Fin n → M.Domain) :
    (rt_push_d ρ n v).free = ρ.free := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun i => v i.succ)

def rt_tuple_m {d} : {n : Nat} → (Fin (n+1) → Term d) → Term d → Formula 1 d
  | 0, v, p => Formula.extensionalEq p (v 0)
  | n+1, v, p => .existsE (.conj (kpair0_m p.weaken (v 0).weaken .newest)
      (rt_tuple_m (n := n) (fun i => (v i.succ).weaken) .newest))

theorem rt_tuple_closed_l {d n} (v : Fin (n+1) → Term d) (p : Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hp : p.freeSupport = []) : (rt_tuple_m v p).FreeClosed := by
  induction n generalizing d with
  | zero => exact (Formula.extensionalEq_freeClosed_iff ..).mpr ⟨hp, hv 0⟩
  | succ n ih =>
    exact ⟨kpair0_m_freeClosed _ _ _ (by simpa using hp) (by simpa using hv 0) rfl,
      ih (fun i => (v i.succ).weaken) .newest (fun i => by simpa using hv i.succ) rfl⟩

theorem rt_tuple_sat_l (hE : Extensional M) {d n} (ρ : Env M d) (v : Fin (n+1) → Term d) (p : Term d) :
    Formula.satisfies ρ (rt_tuple_m v p) ↔ Rt_tuple_d (fun i => (v i).eval ρ) (p.eval ρ) := by
  induction n generalizing d with
  | zero => exact Formula.satisfies_extensionalEq_iff_eq hE ..
  | succ n ih =>
    simp only [rt_tuple_m, Rt_tuple_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hE, ih, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 记录的各坐标由实际配对成员路径留在同一传递层。 -/
theorem Rt_tuple_d.members_l {C p : M.Domain} {k : Nat} {v : Fin (k+1) → M.Domain}
    (tuple : Rt_tuple_d v p) (trans : M.TransitiveSet C) (hp : M.mem p C) : ∀ i, M.mem (v i) C := by
  induction k generalizing p with
  | zero => exact Fin.cases (tuple ▸ hp) (fun i => Fin.elim0 i)
  | succ k ih =>
    obtain ⟨q, pair, tail⟩ := tuple
    have mem := pair.mem_l M trans hp
    exact Fin.cases mem.1 (ih tail mem.2)

/-- 固定记录的全部配对见证在传递层中绝对，无需层内集合论公理实例。 -/
theorem rt_tuple_source_l (hE : Extensional M) {C : M.Domain} (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) {n} (v : Fin (n+1) → (rt_model_l C nc).Domain)
    (p : (rt_model_l C nc).Domain) : Rt_tuple_d v p ↔ Rt_tuple_d (fun i => (v i).val) p.val := by
  have pair (p a b : (rt_model_l C nc).Domain) :
      KPair_d (rt_model_l C nc) p a b ↔ KPair_d M p.val a.val b.val := by
    let ρ : Env (rt_model_l C nc) 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => p⟩
    exact (kpair0_sat_l (rt_model_ext_l hE trans nc) ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l trans nc (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hE ..))
  induction n generalizing p with
  | zero => exact ⟨congrArg Subtype.val, Subtype.ext⟩
  | succ n ih =>
    constructor
    · rintro ⟨q, hp, tail⟩
      exact ⟨q.val, (pair ..).mp hp, (ih (fun i => v i.succ) q).mp tail⟩
    · rintro ⟨q, hp, tail⟩
      let q' : (rt_model_l C nc).Domain := ⟨q, (hp.mem_l M trans p.property).2⟩
      exact ⟨q', (pair ..).mpr hp, (ih (fun i => v i.succ) q').mpr tail⟩

def rt_record_m {d n} (φ : Formula 1 (n+1)) (p : Term d) : Formula 1 d :=
  let t : Fin (n+1) → Term (d+(n+1)) := fun i => .bound ⟨i.val, by omega⟩
  let q := p.rename (fun i => ⟨n+1+i.val, by omega⟩)
  rt_exists_m (n+1) (.conj (rt_tuple_m t q) (φ.bind t))

theorem rt_record_closed_l {d n} (φ : Formula 1 (n+1)) (p : Term d)
    (hφ : φ.FreeClosed) (hp : p.freeSupport = []) : (rt_record_m φ p).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) ?_, ?_⟩
  · simpa only [Definitional.Term.freeSupport_rename] using hp
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr hφ

theorem rt_record_sat_l (hE : Extensional M) {d n} (ρ : Env M d) (φ : Formula 1 (n+1))
    (p : Term d) (hφ : φ.FreeClosed) : Formula.satisfies ρ (rt_record_m φ p) ↔
      ∃ v : Fin (n+1) → M.Domain, Rt_tuple_d v (p.eval ρ) ∧ Formula.satisfies (⟨v, ρ.free⟩ : Env M (n+1)) φ := by
  unfold rt_record_m
  rw [rt_exists_sat_l]
  apply exists_congr
  intro v
  rw [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, Formula.satisfies_bind]
  have new : (fun i : Fin (n+1) => (Term.bound (⟨i.val, by omega⟩ : Fin (d+(n+1)))).eval (rt_push_d ρ (n+1) v)) = v :=
    funext (rt_push_new_l ρ v)
  have old : (p.rename (fun i : Fin d => ⟨n+1+i.val, by omega⟩)).eval (rt_push_d ρ (n+1) v) = p.eval ρ := by
    rw [Definitional.Term.eval_rename]
    cases p with
    | bound i => exact rt_push_old_l ρ v i
    | free i => exact congrFun (rt_push_free_l ρ v) i
  rw [old, new]
  exact and_congr Iff.rfl (Formula.closed_env_l φ hφ new)

end YesMetaZFC.SetTheory.Internal
