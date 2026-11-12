import YesMetaZFC.SetTheory.InnerModel.Separation.Tuple
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.Model.SetTheory.Embedding.Relative

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

/-! ## 固定坐标块的量词

新坐标块置于原环境之前。记录编码只依赖语法元数，模型内历史长度不参与元递归。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rb_exists_m {d n} (φ : Formula 1 (n+d)) : Formula 1 d :=
  rt_exists_m n (φ.rename (fun i => ⟨i.val,by omega⟩))

def rb_forall_m {d n} (φ : Formula 1 (n+d)) : Formula 1 d := .neg (rb_exists_m (.neg φ))

@[simp] theorem rb_exists_closed_l {d n} (φ : Formula 1 (n+d)) :
    (rb_exists_m φ).FreeClosed ↔ φ.FreeClosed := by
  rw [rb_exists_m,rt_exists_closed_l]
  simp -implicitDefEqProofs

@[simp] theorem rb_forall_closed_l {d n} (φ : Formula 1 (n+d)) :
    (rb_forall_m φ).FreeClosed ↔ φ.FreeClosed := by
  simp only [rb_forall_m,Definitional.Formula.FreeClosed,rb_exists_closed_l]

theorem rb_exists_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+d)) :
    Formula.satisfies ρ (rb_exists_m φ) ↔ ∃ v : Fin n → M.Domain,
      Formula.satisfies (⟨Fin.addCases v ρ.bound,ρ.free⟩ : Env M (n+d)) φ := by
  rw [rb_exists_m,rt_exists_sat_l]
  apply exists_congr
  intro v
  rw [Formula.satisfies_rename]
  have eq : (rt_push_d ρ n v).reindex (fun i : Fin (n+d) => ⟨i.val,by omega⟩) =
      (⟨Fin.addCases v ρ.bound,ρ.free⟩ : Env M (n+d)) := by
    change (⟨_,_⟩ : Env M (n+d)) = _
    rw [Env.mk.injEq]
    refine ⟨funext (Fin.addCases (fun i => ?_) (fun i => ?_)),rt_push_free_l ρ v⟩
    · simpa [Function.comp_def] using rt_push_new_l ρ v i
    · simpa [Function.comp_def] using rt_push_old_l ρ v i
  exact eq ▸ Iff.rfl

theorem rb_forall_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+d)) :
    Formula.satisfies ρ (rb_forall_m φ) ↔ ∀ v : Fin n → M.Domain,
      Formula.satisfies (⟨Fin.addCases v ρ.bound,ρ.free⟩ : Env M (n+d)) φ := by
  simp only [rb_forall_m,Formula.satisfies_neg_iff,rb_exists_sat_l,not_exists,Classical.not_not]

@[simp] theorem rb_old_eval_l {d n} (ρ : Env M d) (v : Fin n → M.Domain) (t : Term d) :
    (t.rename (Fin.natAdd n)).eval (⟨Fin.addCases v ρ.bound,ρ.free⟩ : Env M (n+d)) = t.eval ρ := by
  cases t <;> simp [Definitional.Term.rename,Definitional.Term.bind,Definitional.Term.eval]

def rb_conj_m {d} : {n : Nat} → (Fin n → Formula 1 d) → Formula 1 d
  | 0, _ => .truth
  | n+1, φ => .conj (φ 0) (rb_conj_m (n := n) (fun i => φ i.succ))

@[simp] theorem rb_conj_closed_l {d n} (φ : Fin n → Formula 1 d) :
    (rb_conj_m φ).FreeClosed ↔ ∀ i, (φ i).FreeClosed := by
  induction n with
  | zero => simp [rb_conj_m,Definitional.Formula.FreeClosed]
  | succ n ih => simpa only [rb_conj_m,Definitional.Formula.FreeClosed,Fin.forall_fin_succ] using and_congr Iff.rfl (ih _)

theorem rb_conj_sat_l {d n} (ρ : Env M d) (φ : Fin n → Formula 1 d) :
    Formula.satisfies ρ (rb_conj_m φ) ↔ ∀ i, Formula.satisfies ρ (φ i) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i,fun _ => True.intro⟩
  | succ n ih => simpa only [rb_conj_m,Formula.satisfies_conj_iff,Fin.forall_fin_succ] using and_congr Iff.rfl (ih _)

end YesMetaZFC.SetTheory.Internal

/-! ## 固定元数记录列的实际坐标函数

按原元组码读取坐标；函数性来自元组唯一性。替代收集的每一列仍使用
同一内部指标域，语法元数不代替对象模型中的时间递归。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Rt_coord_d {n} (a : Fin (n+1)) (r x : M.Domain) : Prop :=
  ∃ v : Fin (n+1) → M.Domain, Rt_tuple_d v r ∧ v a = x

def rt_coord0_m {n} (a : Fin (n+1)) : Formula 1 2 := rt_exists_m (n+1) (.conj
  (rt_tuple_m (fun i : Fin (n+1) => .bound ⟨i.val, by omega⟩) (.bound ⟨n+1, by omega⟩))
  (Formula.extensionalEq (.bound ⟨a.val, by omega⟩) (.bound ⟨n+2, by omega⟩)))

theorem rt_coord0_closed_l {n} (a : Fin (n+1)) : (rt_coord0_m a).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, (Formula.extensionalEq_freeClosed_iff ..).mpr ⟨rfl, rfl⟩⟩

theorem rt_coord0_sat_l (hE : Extensional M) {n} (a : Fin (n+1)) (ρ : Env M 2) :
    Formula.satisfies ρ (rt_coord0_m a) ↔ Rt_coord_d a (ρ.bound 0) (ρ.bound 1) := by
  rw [rt_coord0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Term.eval_bound]
  have new (i : Fin (n+1)) : (rt_push_d ρ (n+1) v).bound ⟨i.val, by omega⟩ = v i := rt_push_new_l ρ v i
  rw [show (rt_push_d ρ (n+1) v).bound ⟨n+1, by omega⟩ = ρ.bound 0 from rt_push_old_l ρ v 0,
    show (rt_push_d ρ (n+1) v).bound ⟨n+2, by omega⟩ = ρ.bound 1 from rt_push_old_l ρ v 1,
    new a, show (fun i : Fin (n+1) => (rt_push_d ρ (n+1) v).bound ⟨i.val, by omega⟩) = v from funext new]

def rt_coord_m {d n} (a : Fin (n+1)) (r x : Term d) : Formula 1 d :=
  (rt_coord0_m a).bind (Fin.cases r (fun _ => x))

@[simp] theorem rt_coord_closed_l {d n} (a : Fin (n+1)) (r x : Term d)
    (hr : r.freeSupport = []) (hx : x.freeSupport = []) : (rt_coord_m a r x).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hr (fun _ => hx)) _).mpr (rt_coord0_closed_l a)

theorem rt_coord_sat_l (hE : Extensional M) {d n} (a : Fin (n+1)) (ρ : Env M d) (r x : Term d) :
    Formula.satisfies ρ (rt_coord_m a r x) ↔ Rt_coord_d a (r.eval ρ) (x.eval ρ) := by
  rw [rt_coord_m, Formula.satisfies_bind, rt_coord0_sat_l hE]; rfl

theorem rt_coordinate_l (hZF : M.Models ZF) {A D F N : M.Domain} {k : Nat} (a : Fin (k+1))
    (fn : Fn0_d A D F) (rows : ∀ i r, Rd_entry_d i r F → ∃ v : Fin (k+1) → M.Domain, Rt_tuple_d v r)
    (bound : ∀ i r (v : Fin (k+1) → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → M.mem (v a) N) :
    ∃ G, Fn0_d A N G ∧
      ∀ i x, Rd_entry_d i x G ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d a r x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (rt_coord_m a .newest (.bound 1))) }
  have sat i x : φ.denote ρ i x ↔ ∃ r, Rd_entry_d i r F ∧ Rt_coord_d a r x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rt_coord_sat_l hZF.1]; rfl
  obtain ⟨G, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := N) (by
    intro i hi
    obtain ⟨r, _, hr⟩ := fn.2.1 i hi
    obtain ⟨v, code⟩ := rows i r hr
    exact ⟨v a, (sat i (v a)).mpr ⟨r, hr, v, code, rfl⟩⟩) (by
    intro i _ x y hx hy
    obtain ⟨r, hr, v, code, eq⟩ := (sat i x).mp hx
    obtain ⟨s, hs, w, pack, eq'⟩ := (sat i y).mp hy
    have rs := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i s r hs hr
    subst s
    exact eq.symm.trans ((congrFun (rt_tuple_inj_l code pack) a).trans eq')) (by
    intro i x _ hx
    obtain ⟨r, hr, v, code, eq⟩ := (sat i x).mp hx
    exact eq ▸ bound i r v hr code)
  refine ⟨G, fn0_of_function_l (ZF.modelsKP hZF) gf, fun i x => (gs i x).trans ?_⟩
  exact (and_congr_right fun _ => sat i x).trans ⟨And.right, fun h =>
    ⟨h.elim fun r h => (fn.bound_l h.1).1, h⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 同一记录的坐标回读与唯一性

只用已有元组码的单射性，不要求额外集合论公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Rt_coord_d.read_l {n} {a : Fin (n+1)} {r x : M.Domain}
    (h : Rt_coord_d a r x) (v : Fin (n+1) → M.Domain) (code : Rt_tuple_d v r) : v a = x := by
  obtain ⟨w,pack,eq⟩ := h
  exact (congrFun (rt_tuple_inj_l code pack) a).trans eq

theorem Rt_coord_d.unique_l {n} {a : Fin (n+1)} {r x y : M.Domain}
    (h : Rt_coord_d a r x) (g : Rt_coord_d a r y) : x = y := by
  obtain ⟨v,code,eq⟩ := h
  exact eq.symm.trans (g.read_l v code)

end YesMetaZFC.SetTheory.Internal

/-! ## 拥有秩层中的实际有限记录

记录的坐标与证书均处于同一给定集合中。原公式相对化后是背景的有界公式，
可直接放入内部历史谓词，并沿实际初等图搬运。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def rt_record_in0_m {n} (φ : Formula 1 (n+1)) : Formula 1 2 :=
  .conj (.mem (.bound 1) (.bound 0))
    (lr_rel_m (rt_record_m (d := 1) φ .newest) (.bound 0) (fun i => .bound i.succ))

def rt_record_in_m {d n} (φ : Formula 1 (n+1)) (C r : Term d) : Formula 1 d :=
  (rt_record_in0_m φ).bind (Fin.cases C (fun _ => r))

def Rt_record_in_d {n} (φ : Formula 1 (n+1)) (C r : M.Domain) : Prop :=
  Formula.satisfies (⟨Fin.cases C (fun _ => r), fun _ => C⟩ : Env M 2) (rt_record_in0_m φ)

theorem rt_record_in0_closed_l {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) :
    (rt_record_in0_m φ).FreeClosed :=
  ⟨⟨rfl, rfl⟩, lr_rel_closed_l _ (rt_record_closed_l φ _ closed rfl) _ _ rfl (fun _ => rfl)⟩

theorem rt_record_in0_delta_l {n} (φ : Formula 1 (n+1)) : (rt_record_in0_m φ).IsDelta0 :=
  .conj (.mem ..) (lr_rel_delta_l ..)

theorem rt_record_in_closed_l {d n} (φ : Formula 1 (n+1)) (C r : Term d)
    (closed : φ.FreeClosed) (hC : C.freeSupport = []) (hr : r.freeSupport = []) :
    (rt_record_in_m φ C r).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hC (fun _ => hr)) _).mpr
    (rt_record_in0_closed_l φ closed)

theorem rt_record_in_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (C r : Term d)
    (closed : φ.FreeClosed) : Formula.satisfies ρ (rt_record_in_m φ C r) ↔
      Rt_record_in_d φ (C.eval ρ) (r.eval ρ) := by
  rw [rt_record_in_m, Formula.satisfies_bind]
  exact Formula.closed_env_l _ (rt_record_in0_closed_l φ closed)
    (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

theorem Rt_record_in_d.member_l {n} {φ : Formula 1 (n+1)} {C r : M.Domain}
    (h : Rt_record_in_d φ C r) : M.mem r C := ((Formula.satisfies_conj_iff ..).mp h).1

variable (hE : Extensional M)
include hE

theorem rt_record_in_read_l {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) {C r : M.Domain}
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) : Rt_record_in_d φ C r ↔
    M.mem r C ∧ ∃ v : Fin (n+1) → (rt_model_l C nc).Domain, Rt_tuple_d (fun i => (v i).val) r ∧
      Formula.satisfies (⟨v, fun _ => v 0⟩ : Env (rt_model_l C nc) (n+1)) φ := by
  constructor
  · intro h
    let a : (rt_model_l C nc).Domain := ⟨r, h.member_l⟩
    let ρ : Env (rt_model_l C nc) 1 := ⟨fun _ => a, fun _ => a⟩
    have valid := (sc_relative_sat_l trans nc (rt_record_m φ .newest)
      (rt_record_closed_l _ _ closed rfl) ρ _ (.bound 0) (fun i => .bound i.succ) rfl (fun _ => rfl)).mp
      ((Formula.satisfies_conj_iff ..).mp h).2
    obtain ⟨v, tuple, valid⟩ := (rt_record_sat_l (rt_model_ext_l hE trans nc) ρ φ .newest closed).mp valid
    exact ⟨h.member_l, v, (rt_tuple_source_l hE trans nc v a).mp tuple,
      (Formula.closed_env_l φ closed (ρ := ⟨v, ρ.free⟩) (η := ⟨v, fun _ => v 0⟩) rfl).mp valid⟩
  · rintro ⟨hr, v, tuple, valid⟩
    let a : (rt_model_l C nc).Domain := ⟨r, hr⟩
    let ρ : Env (rt_model_l C nc) 1 := ⟨fun _ => a, fun _ => a⟩
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, (sc_relative_sat_l trans nc (rt_record_m φ .newest)
      (rt_record_closed_l _ _ closed rfl) ρ _ (.bound 0) (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr ?_⟩
    exact (rt_record_sat_l (rt_model_ext_l hE trans nc) ρ φ .newest closed).mpr
      ⟨v, (rt_tuple_source_l hE trans nc v a).mpr tuple,
        (Formula.closed_env_l φ closed (ρ := ⟨v, fun _ => v 0⟩) (η := ⟨v, ρ.free⟩) rfl).mp valid⟩

/-- 固定有限记录只需要配对闭包，与整个工作源的超幂性质无关。 -/
theorem rt_record_in_save_l {n C} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (trans : M.TransitiveSet C)
    (pair : ∀ a b, M.mem a C → M.mem b C → ∃ p, M.mem p C ∧ Pair_d M p a b)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) (n+1)) (valid : Formula.satisfies ρ φ) :
    ∃ r, Rt_record_in_d φ C r ∧ Rt_tuple_d (fun i => (ρ.bound i).val) r := by
  have tuple {k} (v : Fin (k+1) → (rt_model_l C nc).Domain) :
      ∃ r, M.mem r C ∧ Rt_tuple_d (fun i => (v i).val) r := by
    induction k with
    | zero => exact ⟨(v 0).val, (v 0).property, rfl⟩
    | succ k ih =>
      obtain ⟨r, hr, tail⟩ := ih (fun i => v i.succ)
      let r₀ : (rt_model_l C nc).Domain := ⟨r, hr⟩
      obtain ⟨q, code⟩ := (rt_pair_l trans nc hE pair).total (v 0) r₀
      exact ⟨q.val, q.property, (rt_tuple_source_l hE trans nc v q).mp ⟨r₀, code,
        (rt_tuple_source_l hE trans nc (fun i => v i.succ) r₀).mpr tail⟩⟩
  obtain ⟨r, hr, code⟩ := tuple ρ.bound
  exact ⟨r, (rt_record_in_read_l hE φ closed trans nc).mpr
    ⟨hr, ρ.bound, code, (Formula.closed_env_l φ closed
      (ρ := ρ) (η := ⟨ρ.bound, fun _ => ρ.bound 0⟩) rfl).mp valid⟩, code⟩

end YesMetaZFC.SetTheory.Internal
