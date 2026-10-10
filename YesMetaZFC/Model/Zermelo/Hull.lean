import YesMetaZFC.Model.Zermelo.ScopeLimits

/-! # 同一载体内的 Z 闭包范围
先把 ω 及其成员加入传递的旧范围，再取全部有限幂集扩张的并。
这是集合树载体中的实际集合；不假设反射、模型存在或更强的成员良基性。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional
universe u
attribute [local implicit_reducible] SetTheory.signature

private theorem hl_nat_sub : ∀ n, V.sub (V.nat.{u} n) V.omega
  | 0 => fun x hx => (V.empty_mem x hx).elim
  | n+1 => fun x hx => st_use ((V.succ_mem _ _).mp hx) (fun k => k.elim
      (fun h => hl_nat_sub n x h)
      (fun e => (V.mem_left e).mpr (V.elem_mem V.omega ⟨n⟩)))

private theorem hl_omega_trans : Sl_trans V.omega.{u} :=
  fun _x hx y hy => st_use hx (fun ⟨⟨n⟩, e⟩ => hl_nat_sub n y ((V.mem_right e).mp hy))

private theorem hl_succ_trans (d : V.{u}) (h : Sl_trans d) : Sl_trans (V.succ d) :=
  fun x hx y hy => st_use ((V.succ_mem d x).mp hx) (fun k =>
    (V.succ_mem d y).mpr (nn_in (.inl (k.elim (fun hx => h x hx y hy)
      (fun e => (V.mem_right e).mp hy)))))

def hl_seed (d : V.{u}) : V.{u} := V.union (V.pair d (V.succ V.omega))

theorem hl_seed_mem (d x : V.{u}) : x ∈ hl_seed d ↔ ¬¬(x ∈ d ∨ x ∈ V.succ V.omega) :=
  ⟨fun h => st_use ((V.union_mem _ _).mp h) (fun ⟨_a, ha, hx⟩ =>
      st_use ((V.pair_mem _ _ _).mp ha) (fun k => k.elim
        (fun e => nn_in (.inl ((V.mem_right e).mp hx)))
        (fun e => nn_in (.inr ((V.mem_right e).mp hx))))),
    fun h => st_use h (fun k => k.elim
      (fun hx => (V.union_mem _ _).mpr (nn_in ⟨d,
        (V.pair_mem _ _ _).mpr (nn_in (.inl (V.eq_refl _))), hx⟩))
      (fun hx => (V.union_mem _ _).mpr (nn_in ⟨V.succ V.omega,
        (V.pair_mem _ _ _).mpr (nn_in (.inr (V.eq_refl _))), hx⟩)))⟩

theorem hl_seed_sub (d : V.{u}) : V.sub d (hl_seed d) :=
  fun x hx => (hl_seed_mem d x).mpr (nn_in (.inl hx))

theorem hl_seed_omega (d : V.{u}) : V.omega ∈ hl_seed d :=
  (hl_seed_mem d _).mpr (nn_in (.inr ((V.succ_mem _ _).mpr (nn_in (.inr (V.eq_refl _))))))

theorem hl_seed_trans (d : V.{u}) (h : Sl_trans d) : Sl_trans (hl_seed d) :=
  fun x hx y hy => st_use ((hl_seed_mem d x).mp hx) (fun k =>
    (hl_seed_mem d y).mpr (k.elim (fun hx => nn_in (.inl (h x hx y hy)))
      (fun hx => nn_in (.inr (hl_succ_trans _ hl_omega_trans x hx y hy)))))

theorem hl_stage_mono (d : V.{u}) {n m : Nat} (h : n ≤ m) :
    V.sub (sl_stage d n) (sl_stage d m) := by
  induction h with
  | refl => exact fun _ => id
  | step _ ih => exact fun x hx => (sc_bounds _).1 x (ih x hx)

/-- 全部有限阶段的并；指标仍处于原载体允许的同一个宇宙。 -/
def hl_range (d : V.{u}) : V.{u} :=
  V.union (.sup (ULift Nat) (fun n => sl_stage (hl_seed d) n.down))

theorem hl_mem (d x : V.{u}) : x ∈ hl_range d ↔ ¬¬∃ n, x ∈ sl_stage (hl_seed d) n :=
  ⟨fun h => st_use ((V.union_mem _ _).mp h) (fun ⟨_a, ha, hx⟩ =>
      st_use ha (fun ⟨⟨n⟩, e⟩ => nn_in ⟨n, (V.mem_right e).mp hx⟩)),
    fun h => st_use h (fun ⟨n, hx⟩ => (V.union_mem _ _).mpr
      (nn_in ⟨_, V.elem_mem (.sup (ULift Nat) (fun n => sl_stage (hl_seed d) n.down)) ⟨n⟩, hx⟩))⟩

theorem hl_stage (d : V.{u}) (n : Nat) : V.sub (sl_stage (hl_seed d) n) (hl_range d) :=
  fun x hx => (hl_mem d x).mpr (nn_in ⟨n, hx⟩)

theorem hl_sub (d : V.{u}) : V.sub d (hl_range d) :=
  fun x hx => hl_stage d 0 x (hl_seed_sub d x hx)

/-- 任意旧范围的子集都进入闭包，故全部旧收集池同时进入。 -/
theorem hl_power (d : V.{u}) : V.sub (V.power d) (hl_range d) :=
  fun x hx => hl_stage d 1 x ((sc_bounds _).2 x ((V.power_mem _ _).mpr
    (fun y hy => hl_seed_sub d y ((V.power_mem d x).mp hx y hy))))

theorem hl_self (d : V.{u}) : d ∈ hl_range d :=
  hl_power d d ((V.power_mem d d).mpr (fun _ => id))

theorem hl_trans (d : V.{u}) (h : Sl_trans d) : Sl_trans (hl_range d) :=
  fun x hx y hy => st_use ((hl_mem d x).mp hx) (fun ⟨n, hn⟩ =>
    hl_stage d n y (sl_stage_trans _ (hl_seed_trans d h) n x hn y hy))

theorem hl_empty (d : V.{u}) : V.empty ∈ hl_range d :=
  hl_power d _ ((V.power_mem _ _).mpr (fun x hx => (V.empty_mem x hx).elim))

theorem hl_omega (d : V.{u}) : V.omega ∈ hl_range d := hl_stage d 0 _ (hl_seed_omega d)

theorem hl_pair (d : V.{u}) {a b : V.{u}} (ha : a ∈ hl_range d) (hb : b ∈ hl_range d) :
    V.pair a b ∈ hl_range d :=
  st_use ((hl_mem d a).mp ha) (fun ⟨n, hn⟩ => st_use ((hl_mem d b).mp hb) (fun ⟨m, hm⟩ =>
    hl_stage d (n+m+1) _ ((sc_bounds _).2 _ ((V.power_mem _ _).mpr (fun _x hx =>
      st_use ((V.pair_mem _ _ _).mp hx) (fun k => k.elim
        (fun e => (V.mem_left e).mpr (hl_stage_mono _ (Nat.le_add_right n m) a hn))
        (fun e => (V.mem_left e).mpr (hl_stage_mono _ (Nat.le_add_left m n) b hm))))))))

/-- 闭包中的每个集合，其任意原生子集也在闭包中。 -/
theorem hl_subset (d : V.{u}) (h : Sl_trans d) {a b : V.{u}} (hb : b ∈ hl_range d)
    (ha : V.sub a b) : a ∈ hl_range d :=
  st_use ((hl_mem d b).mp hb) (fun ⟨n, hn⟩ => hl_stage d (n+1) _ ((sc_bounds _).2 _
    ((V.power_mem _ _).mpr (fun x hx => sl_stage_trans _ (hl_seed_trans d h) n b hn x (ha x hx)))))

theorem hl_union (d : V.{u}) (h : Sl_trans d) {a : V.{u}} (ha : a ∈ hl_range d) :
    V.union a ∈ hl_range d := by
  apply st_use ((hl_mem d a).mp ha)
  intro ⟨n, hn⟩
  have ht := sl_stage_trans _ (hl_seed_trans d h) n
  exact hl_stage d (n+1) _ ((sc_bounds _).2 _ ((V.power_mem _ _).mpr (fun x hx =>
    st_use ((V.union_mem _ _).mp hx) (fun ⟨y, hy, hx⟩ => ht y (ht a hn y hy) x hx))))

theorem hl_powerset (d : V.{u}) (h : Sl_trans d) {a : V.{u}} (ha : a ∈ hl_range d) :
    V.power a ∈ hl_range d := by
  apply st_use ((hl_mem d a).mp ha)
  intro ⟨n, hn⟩
  have ht := sl_stage_trans _ (hl_seed_trans d h) n a hn
  exact hl_stage d (n+2) _ ((sc_bounds _).2 _ ((V.power_mem _ _).mpr (fun x hx =>
    (sc_bounds _).2 x ((V.power_mem _ _).mpr (fun y hy => ht y ((V.power_mem _ _).mp hx y hy))))))

theorem hl_sep (d : V.{u}) (h : Sl_trans d) {a : V.{u}} (ha : a ∈ hl_range d)
    (p : V.{u} → Prop) : V.sep a p ∈ hl_range d :=
  hl_subset d h ha (fun _x hx => st_use hx (fun ⟨⟨i, _⟩, e⟩ => nn_in ⟨i, e⟩))

theorem hl_succ (d : V.{u}) (h : Sl_trans d) {a : V.{u}} (ha : a ∈ hl_range d) :
    V.succ a ∈ hl_range d := by
  apply st_use ((hl_mem d a).mp ha)
  intro ⟨n, hn⟩
  exact hl_stage d (n+1) _ ((sc_bounds _).2 _ ((V.power_mem _ _).mpr (fun x hx =>
    st_use ((V.succ_mem _ _).mp hx) (fun k => k.elim
      (fun hx => sl_stage_trans _ (hl_seed_trans d h) n a hn x hx)
      (fun e => (V.mem_left e).mpr hn)))))

/-- 全分离使用原模式正文及其全部量词；闭包容纳实际构造的分离子集。 -/
theorem hl_separation {n} (φ : Project.UnarySchema n) (d : V.{u}) (h : Sl_trans d)
    (ρ : Env.{u} (Project.fo_bound_context n) []) :
    sc_sat (Project.fo_formula (Axioms.Schema.separationCore φ)
      (Axioms.Schema.separation_core_closed φ)) (hl_range d) ρ := by
  intro a ha
  let p (x : V.{u}) := sc_sat (Project.fo_formula φ.body φ.freeClosed) (hl_range d) (ρ.pushBound x)
  refine nn_in ⟨V.sep a p, hl_sep d h ha p, fun x _ => ?_⟩
  have e := sc_pbind φ.body φ.freeClosed (.bound ∘ BoundEmbedding.unaryUnderTwo)
    (fun _ => rfl) (hl_range d) (((ρ.pushBound a).pushBound (V.sep a p)).pushBound x)
    (ρ.pushBound x) (fun i => fin_cases rfl (fun _ => rfl) i)
  exact (V.sep_mem a x p (fun e => (sat_congr (gl_form (Project.fo_formula φ.body φ.freeClosed))
    (ρ := (ρ.pushBound _).pushFree (hl_range d)) (τ := (ρ.pushBound _).pushFree (hl_range d))
    ⟨(fun i => match i with | .here => e | .there _ => V.eq_refl _),
      fun _ => V.eq_refl _⟩).mp)).trans (and_congr Iff.rfl e.symm)

private theorem hl_close {s n} (φ : Project.Formula s n) (hc : φ.FreeClosed) (d : V.{u})
    (ρ : Env.{u} [] []) (h : ∀ τ : Env.{u} (Project.fo_bound_context n) [],
      sc_sat (Project.fo_formula φ hc) d τ) :
    sc_sat (Project.fo_formula (Definitional.Formula.forallClosure n φ)
      ((Definitional.Formula.freeClosed_forallClosure φ).mpr hc)) d ρ := by
  induction n with
  | zero => exact h ρ
  | succ n ih => exact ih (.forallE φ) hc (fun τ x _ => h (τ.pushBound x))

/-- 闭包满足原 Z 的每一条公理及全分离模式，所有量词使用同一个实际范围。 -/
theorem hl_z (d : V.{u}) (h : Sl_trans d) (s : Project.Sentence) (hs : SetTheory.Z s)
    (ρ : Env.{u} [] []) : sc_sat (Project.fo_sentence s) (hl_range d) ρ := by
  have ht := hl_trans d h
  cases hs with
  | extensionality =>
    intro a ha b hb k
    exact V.ext (fun x => ⟨fun hx => (k x (ht a ha x hx)).mp hx,
      fun hx => (k x (ht b hb x hx)).mpr hx⟩)
  | emptySet => exact nn_in ⟨V.empty, hl_empty d, fun x _ => V.empty_mem x⟩
  | pairing => exact fun a ha b hb => nn_in ⟨V.pair a b, hl_pair d ha hb, fun x _ => V.pair_mem a b x⟩
  | union =>
    intro a ha
    refine nn_in ⟨V.union a, hl_union d h ha, fun x _ => ?_⟩
    exact (V.union_mem a x).trans (nn_congr ⟨fun ⟨y, hy, hx⟩ => ⟨y, ht a ha y hy, hy, hx⟩,
      fun ⟨y, _, hy, hx⟩ => ⟨y, hy, hx⟩⟩)
  | powerSet =>
    intro a ha
    refine nn_in ⟨V.power a, hl_powerset d h ha, fun x hx => ?_⟩
    exact (V.power_mem a x).trans ⟨fun k y _ hy => k y hy,
      fun k y hy => k y (ht x hx y hy) hy⟩
  | infinity =>
    exact nn_in ⟨V.omega, hl_omega d,
      nn_in ⟨V.empty, hl_empty d, (fun x _ => V.empty_mem x), V.omega_zero⟩,
      fun a ha k => nn_in ⟨V.succ a, hl_succ d h ha, (fun x _ => V.succ_mem a x), V.omega_succ k⟩⟩
  | foundation =>
    intro a ha k
    have e := V.foundation a (st_use k (fun ⟨x, _, hx⟩ => nn_in ⟨x, hx⟩))
    exact st_use e (fun ⟨x, hx, hm⟩ => nn_in ⟨x, ht a ha x hx, hx, fun y _ hy => hm y hy⟩)
  | separation φ =>
    exact hl_close (Axioms.Schema.separationCore φ) (Axioms.Schema.separation_core_closed φ)
      (hl_range d) ρ (hl_separation φ d h)

/-- 原收集模式把容器交付到这个实际的 Z 闭包，正文保持指定的范围 R。 -/
theorem hl_collection {n} (φ : Project.BinarySchema n) (r i j w : V.{u}) (hi : Sc_cover i j) :
    sat (sc_prefix n (Project.fo_sentence (Axioms.Schema.collection φ)))
      (((((FirstOrder.Env.empty.pushFree r).pushFree w).pushFree i).pushFree j).pushFree (hl_range w)) :=
  sc_collection_closed φ r i j w (hl_range w) hi (hl_power w)

/-- info: 'YesMetaZFC.Model.Zermelo.hl_powerset' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_powerset
/-- info: 'YesMetaZFC.Model.Zermelo.hl_pair' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_pair
/-- info: 'YesMetaZFC.Model.Zermelo.hl_z' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_z
/-- info: 'YesMetaZFC.Model.Zermelo.hl_collection' does not depend on any axioms -/
#guard_msgs in
#print axioms hl_collection
end YesMetaZFC.Model.Zermelo
