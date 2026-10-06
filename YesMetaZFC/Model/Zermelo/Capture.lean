import YesMetaZFC.Model.Zermelo.ScopeLimits

/-! # 标准自然数检查结果的实际集合捕获

检查程序仍是原有的 Nat → Bool 总函数。捕获集的分支直接来自通过检查的
标准自然数；高层重新构造该集合，并与低层集合的升层像逐成员对应。
原收集正文的范围和参数随之搬运；重新构造的收集池保持相同的成员。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional
universe u
attribute [local implicit_reducible] SetTheory.signature

private theorem cp_nat_mem (n m : Nat) (h : n < m) : V.nat.{u} n ∈ V.nat m := by
  induction m with
  | zero => exact (Nat.not_lt_zero n h).elim
  | succ m ih =>
    apply (V.succ_mem (V.nat m) (V.nat n)).mpr
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with e | h
    · exact nn_in (.inr (e ▸ V.eq_refl _))
    · exact nn_in (.inl (ih h))

/-- 集合树中的标准数码不会把两个不同的宿主自然数识别为相等。 -/
theorem cp_nat_inj {n m : Nat} (h : V.eq (V.nat.{u} n) (V.nat m)) : n = m := by
  rcases Nat.lt_trichotomy n m with hnm | e | hmn
  · exact (sl_irrefl (V.nat m) ((V.mem_left h).mp (cp_nat_mem n m hnm))).elim
  · exact e
  · exact (sl_irrefl (V.nat n) ((V.mem_left h).mpr (cp_nat_mem m n hmn))).elim

private theorem cp_lift_succ (a : V.{u}) :
    V.eq (gl_lift (V.succ a)) (V.succ (gl_lift a)) := by
  cases a with
  | sup ι f =>
    constructor
    · intro ⟨i⟩
      cases i with
      | inl i => exact nn_in ⟨.inl ⟨i⟩, V.eq_refl _⟩
      | inr _ => exact nn_in ⟨.inr ⟨⟩, V.eq_refl _⟩
    · intro i
      cases i with
      | inl i => exact nn_in ⟨⟨.inl i.down⟩, V.eq_refl _⟩
      | inr _ => exact nn_in ⟨⟨.inr ⟨⟩⟩, V.eq_refl _⟩

/-- 升层后的旧数码等于在高层重新构造的同一标准数码。 -/
theorem cp_nat_lift (n : Nat) : V.eq (gl_lift (V.nat.{u} n)) (V.nat n) := by
  induction n with
  | zero => exact ⟨(fun ⟨i⟩ => nomatch i), (fun i => nomatch i)⟩
  | succ n ih => exact V.eq_trans (cp_lift_succ (V.nat n)) (V.succ_eq ih)

/-- 数据由检查器的实际输出决定，不由公式的语义真假决定。 -/
def cp_set (f : Nat → Bool) : V.{u} :=
  .sup (ULift {n : Nat // f n = true}) (fun i => V.nat i.down.val)

/-- 对每个标准输入，捕获集的成员判定精确等于原检查器。 -/
theorem cp_set_mem (f : Nat → Bool) (n : Nat) : V.nat.{u} n ∈ cp_set f ↔ f n = true := by
  constructor
  · intro h
    cases e : f n with
    | true => rfl
    | false =>
      exact False.elim (h (fun ⟨⟨⟨m, hm⟩⟩, hnm⟩ => by
        have enm := cp_nat_inj hnm
        cases enm
        rw [e] at hm
        cases hm))
  · intro h
    exact V.elem_mem (cp_set f) ⟨⟨n, h⟩⟩

/-- 高层独立重建捕获集，与低层集合的升层像相同。 -/
theorem cp_set_lift (f : Nat → Bool) : V.eq (gl_lift (cp_set.{u} f)) (cp_set f) :=
  ⟨fun i => nn_in ⟨⟨i.down.down⟩, cp_nat_lift i.down.down.val⟩,
   fun i => nn_in ⟨⟨⟨i.down⟩⟩, cp_nat_lift i.down.val⟩⟩

private theorem cp_body_lift {n} (φ : Project.BinarySchema n) (r : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (x y : V.{u}) :
    sc_sat (Project.fo_formula φ.body φ.freeClosed) (gl_lift r)
      (((gl_env ρ).pushBound (gl_lift x)).pushBound (gl_lift y)) ↔
    sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y) := by
  apply Iff.trans ?_ (gl_abs (Project.fo_formula φ.body φ.freeClosed) r
    ((ρ.pushBound x).pushBound y))
  apply sat_congr
  constructor
  · intro s j
    cases j with
    | here => exact V.eq_refl _
    | there j => cases j with
      | here => exact V.eq_refl _
      | there _ => exact V.eq_refl _
  · intro s j
    cases j with
    | here => exact V.eq_refl _
    | there j => nomatch j

private theorem cp_collect_mem_lift {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a y : V.{u}) :
    gl_lift y ∈ sc_collect φ (gl_lift r) (gl_lift i) (gl_lift w) (gl_env ρ) (gl_lift a) ↔
      y ∈ sc_collect φ r i w ρ a := by
  apply (sc_collect_mem φ (gl_lift r) (gl_lift i) (gl_lift w) (gl_env ρ)
    (gl_lift a) (gl_lift y)).trans
  apply Iff.trans ?_ (sc_collect_mem φ r i w ρ a y).symm
  apply and_congr (gl_mem y w)
  constructor
  · intro h
    apply st_use h
    rintro ⟨x, hx, ha, h⟩
    -- 稳定存在中的代表只用于稳定结论，不从双重否定中选择集合。
    apply st_use (gl_member i hx)
    intro ⟨z, hz, e⟩
    have he : Env_rel (b := .set :: .set :: Project.fo_bound_context n) (f := [.set])
        ((((gl_env ρ).pushBound x).pushBound (gl_lift y)).pushFree (gl_lift r))
        ((((gl_env ρ).pushBound (gl_lift z)).pushBound (gl_lift y)).pushFree (gl_lift r)) := by
      refine ⟨?_, fun _ => V.eq_refl _⟩
      intro s j
      cases s
      cases j with
      | here => exact V.eq_refl _
      | there j => cases j with
        | here => exact e
        | there _ => exact V.eq_refl _
    exact nn_in ⟨z, hz, (gl_mem z a).mp ((V.mem_left e).mp ha),
      (cp_body_lift φ r ρ z y).mp ((sat_congr _ he).mp h)⟩
  · intro h
    exact st_use h (fun ⟨x, hx, ha, h⟩ =>
      nn_in ⟨gl_lift x, (gl_mem x i).mpr hx, (gl_mem x a).mpr ha,
        (cp_body_lift φ r ρ x y).mpr h⟩)

/-- 升层后按原公式重新收集，得到的是旧收集对象的升层像。 -/
theorem cp_collect_lift {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) :
    V.eq (gl_lift (sc_collect φ r i w ρ a))
      (sc_collect φ (gl_lift r) (gl_lift i) (gl_lift w) (gl_env ρ) (gl_lift a)) := by
  apply V.ext
  intro y
  constructor
  · intro h
    apply st_use (gl_member (sc_collect φ r i w ρ a) h)
    intro ⟨z, hz, e⟩
    exact (V.mem_left e).mpr ((cp_collect_mem_lift φ r i w ρ a z).mpr hz)
  · intro h
    have hw := ((sc_collect_mem φ (gl_lift r) (gl_lift i) (gl_lift w)
      (gl_env ρ) (gl_lift a) y).mp h).1
    apply st_use (gl_member w hw)
    intro ⟨z, _hz, e⟩
    exact (V.mem_left e).mpr ((gl_mem z (sc_collect φ r i w ρ a)).mpr
      ((cp_collect_mem_lift φ r i w ρ a z).mp ((V.mem_left e).mp h)))

/-- 参数的实际重建可替换外延相同的旧参数，整个收集对象随之保持。 -/
theorem cp_collect_congr {n} (φ : Project.BinarySchema n) (r i w a : V.{u})
    (ρ τ : Env.{u} (Project.fo_bound_context n) []) (h : Env_rel ρ τ) :
    V.eq (sc_collect φ r i w ρ a) (sc_collect φ r i w τ a) := by
  have k x y : sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y) ↔
      sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((τ.pushBound x).pushBound y) := by
    have e := env_push (s := SetSort.set) (env_push (s := SetSort.set) h (V.eq_refl x)) (V.eq_refl y)
    exact sat_congr (gl_form (Project.fo_formula φ.body φ.freeClosed))
      ⟨e.1, fun j => match j with | .here => V.eq_refl _ | .there j => nomatch j⟩
  apply V.ext
  intro y
  apply (sc_collect_mem φ r i w ρ a y).trans
  apply Iff.trans ?_ (sc_collect_mem φ r i w τ a y).symm
  exact and_congr Iff.rfl (nn_congr
    ⟨fun ⟨x, hx, ha, hp⟩ => ⟨x, hx, ha, (k x y).mp hp⟩,
     fun ⟨x, hx, ha, hp⟩ => ⟨x, hx, ha, (k x y).mpr hp⟩⟩)

/-- info: 'YesMetaZFC.Model.Zermelo.cp_set_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms cp_set_mem
/-- info: 'YesMetaZFC.Model.Zermelo.cp_set_lift' does not depend on any axioms -/
#guard_msgs in
#print axioms cp_set_lift
/-- info: 'YesMetaZFC.Model.Zermelo.cp_collect_lift' does not depend on any axioms -/
#guard_msgs in
#print axioms cp_collect_lift
end YesMetaZFC.Model.Zermelo
