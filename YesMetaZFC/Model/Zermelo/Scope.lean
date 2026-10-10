import YesMetaZFC.Model.Zermelo.GuardedLift

/-! # 跨范围的受限证明组合
先把事实搬到共同载体并保留内部范围；覆盖该内部范围的外层限制可以消去。
确实改变内部范围时，存在量词向大范围运输，全称量词向小范围运输，否定及蕴含前件反向。
方向判据是可计算的充分条件；本层不保证任意原 ZF 推导均能通过这些组合规则。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory
universe u
attribute [local implicit_reducible] SetTheory.signature

abbrev sc_sat {b f} (φ : Formula ℒ b f) (a : V.{u}) (ρ : Env.{u} b f) : Prop :=
  sat (gl_form φ) (ρ.pushFree a)

/-- 两个布尔值分别判定是否允许扩大、缩小范围；只读取原公式语法。 -/
def sc_test {b f} : Formula ℒ b f → Bool × Bool
  | .falsum | .truth | .equal _ _ | .rel _ _ => (true, true)
  | .neg p => ((sc_test p).2, (sc_test p).1)
  | .conj p q | .disj p q => ((sc_test p).1 && (sc_test q).1, (sc_test p).2 && (sc_test q).2)
  | .imp p q => ((sc_test p).2 && (sc_test q).1, (sc_test p).1 && (sc_test q).2)
  | .iff p q =>
      let k := ((sc_test p).1 && (sc_test p).2) && ((sc_test q).1 && (sc_test q).2)
      (k, k)
  | .forallE _ p => (false, (sc_test p).2)
  | .existsE _ p => ((sc_test p).1, false)

theorem sc_fixed {b f} (φ : Formula ℒ b f) (a c : V.{u}) (ρ : Env.{u} b f) :
    sat (φ.weakenFree SetSort.set) (ρ.pushFree a) ↔
      sat (φ.weakenFree SetSort.set) (ρ.pushFree c) :=
  (sat_weaken φ ρ a).trans (sat_weaken φ ρ c).symm

-- 直接分解布尔合取，避免经命题等号引入外延性。
private theorem sc_and : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | false, _, h => nomatch h
  | true, false, h => nomatch h
  | true, true, _ => ⟨rfl, rfl⟩

/-- 同时证明两个方向，蕴含前件直接调用相反方向的归纳假设。 -/
theorem sc_sound {b f} (φ : Formula ℒ b f) (a c : V.{u}) (h : V.sub a c)
    (ρ : Env.{u} b f) :
    ((sc_test φ).1 = true → sc_sat φ a ρ → sc_sat φ c ρ) ∧
    ((sc_test φ).2 = true → sc_sat φ c ρ → sc_sat φ a ρ) := by
  induction φ with
  | falsum | truth => exact ⟨fun _ => id, fun _ => id⟩
  | equal t s =>
    exact ⟨fun _ => (sc_fixed (.equal t s) a c ρ).mp,
      fun _ => (sc_fixed (.equal t s) a c ρ).mpr⟩
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons s .nil) =>
      ⟨fun _ => (sc_fixed (.rel .membership (.cons t (.cons s .nil))) a c ρ).mp,
       fun _ => (sc_fixed (.rel .membership (.cons t (.cons s .nil))) a c ρ).mpr⟩
  | neg _ ih =>
    exact ⟨fun k n p => n ((ih ρ).2 k p), fun k n p => n ((ih ρ).1 k p)⟩
  | conj _ _ ih ik =>
    exact ⟨fun k p => let e := sc_and k
        ⟨(ih ρ).1 e.1 p.1, (ik ρ).1 e.2 p.2⟩,
      fun k p => let e := sc_and k
        ⟨(ih ρ).2 e.1 p.1, (ik ρ).2 e.2 p.2⟩⟩
  | disj _ _ ih ik =>
    constructor
    · intro k p
      have e := sc_and k
      exact st_use p (fun p => p.elim (fun p => nn_in (.inl ((ih ρ).1 e.1 p)))
        (fun p => nn_in (.inr ((ik ρ).1 e.2 p))))
    · intro k p
      have e := sc_and k
      exact st_use p (fun p => p.elim (fun p => nn_in (.inl ((ih ρ).2 e.1 p)))
        (fun p => nn_in (.inr ((ik ρ).2 e.2 p))))
  | imp _ _ ih ik =>
    exact ⟨fun k p q => let e := sc_and k
        (ik ρ).1 e.2 (p ((ih ρ).2 e.1 q)),
      fun k p q => let e := sc_and k
        (ik ρ).2 e.2 (p ((ih ρ).1 e.1 q))⟩
  | iff p q ih ik =>
    have t : (((sc_test p).1 && (sc_test p).2) && ((sc_test q).1 && (sc_test q).2)) = true →
        (sc_sat (.iff p q) a ρ ↔ sc_sat (.iff p q) c ρ) := by
      intro k
      have e := sc_and k
      have ep := sc_and e.1
      have eq := sc_and e.2
      exact st_iff_congr ⟨(ih ρ).1 ep.1, (ih ρ).2 ep.2⟩ ⟨(ik ρ).1 eq.1, (ik ρ).2 eq.2⟩
    exact ⟨fun k => (t k).mp, fun k => (t k).mpr⟩
  | forallE s φ ih =>
    cases s
    exact ⟨(fun k => nomatch k), fun k p x hx => (ih (ρ.pushBound x)).2 k (p x (h x hx))⟩
  | existsE s φ ih =>
    cases s
    exact ⟨fun k p => st_use p (fun ⟨x, hx, hp⟩ =>
      nn_in ⟨x, h x hx, (ih (ρ.pushBound x)).1 k hp⟩), (fun k => nomatch k)⟩

/-- 已保留内部范围的任意公式，可吸收一个覆盖该范围的外层限制。 -/
theorem sc_absorb {b f} (φ : Formula ℒ b f) (d a : V.{u}) (h : V.sub d a)
    (ρ : Env.{u} b f) : sc_sat (gl_form φ) a (ρ.pushFree d) ↔ sc_sat φ d ρ := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | equal t s => exact sat_weaken (s := SetSort.set) (gl_form (.equal t s)) (ρ.pushFree d) a
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons s .nil) =>
      sat_weaken (s := SetSort.set) (gl_form (.rel .membership (.cons t (.cons s .nil))))
        (ρ.pushFree d) a
  | neg _ ih => exact not_congr (ih ρ)
  | conj _ _ ih ik => exact and_congr (ih ρ) (ik ρ)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih ρ) (ik ρ))
  | imp _ _ ih ik => exact imp_congr (ih ρ) (ik ρ)
  | iff _ _ ih ik => exact st_iff_congr (ih ρ) (ik ρ)
  | forallE s φ ih =>
    cases s
    exact ⟨fun p x hx => (ih (ρ.pushBound x)).mp (p x (h x hx) hx),
      fun p x _ hx => (ih (ρ.pushBound x)).mpr (p x hx)⟩
  | existsE s φ ih =>
    cases s
    exact nn_congr ⟨fun ⟨x, _, hx, hp⟩ => ⟨x, hx, (ih (ρ.pushBound x)).mp hp⟩,
      fun ⟨x, hx, hp⟩ => ⟨x, h x hx, hx, (ih (ρ.pushBound x)).mpr hp⟩⟩

/-- 内部范围相同即可跨两个外层范围组合；不限制割公式的量词复杂度。 -/
theorem sc_mp_fixed {b f} (φ : Formula ℒ b f) (ψ : Formula ℒ b (.set :: f))
    (d a c : V.{u}) (ρ : Env.{u} b f) (ha : V.sub d a) (hc : V.sub d c)
    (p : sc_sat (gl_form φ) a (ρ.pushFree d))
    (q : sc_sat (.imp (gl_form φ) ψ) c (ρ.pushFree d)) : sc_sat ψ c (ρ.pushFree d) :=
  q ((sc_absorb φ d c hc ρ).mpr ((sc_absorb φ d a ha ρ).mp p))

/-- 在接收蕴含的范围内解释割公式，方向由布尔判据检查。 -/
theorem sc_mp_up {b f} (φ ψ : Formula ℒ b f) (a c : V.{u}) (ρ : Env.{u} b f)
    (h : V.sub a c) (k : (sc_test φ).1 = true)
    (p : sc_sat φ a ρ) (q : sc_sat (.imp φ ψ) c ρ) : sc_sat ψ c ρ :=
  q ((sc_sound φ a c h ρ).1 k p)

theorem sc_mp_down {b f} (φ ψ : Formula ℒ b f) (a c : V.{u}) (ρ : Env.{u} b f)
    (h : V.sub a c) (k : (sc_test φ).2 = true)
    (p : sc_sat φ c ρ) (q : sc_sat (.imp φ ψ) a ρ) : sc_sat ψ a ρ :=
  q ((sc_sound φ a c h ρ).2 k p)

/-- 保留旧范围并容纳它的全部子集；不要求旧范围本身具有传递性。 -/
def sc_next (a : V.{u}) : V.{u} := V.union (V.pair a (V.power a))

theorem sc_bounds (a : V.{u}) : V.sub a (sc_next a) ∧ V.sub (V.power a) (sc_next a) :=
  ⟨fun _x hx => (V.union_mem _ _).mpr (nn_in ⟨a,
      (V.pair_mem _ _ _).mpr (nn_in (.inl (V.eq_refl _))), hx⟩),
    fun _x hx => (V.union_mem _ _).mpr (nn_in ⟨V.power a,
      (V.pair_mem _ _ _).mpr (nn_in (.inr (V.eq_refl _))), hx⟩)⟩

/-- 实际后继范围容纳此前构造的任意收集池。 -/
theorem sc_pool {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f) (a : V.{u}) :
    gl_pool φ ρ a ∈ sc_next gl_space :=
  (sc_bounds gl_space).2 _ (gl_pool_bound φ ρ a)

/-- 原核的变量代入保持已标注的范围，不代入额外加入的范围变量。 -/
theorem sc_subst {b f b' f'} (φ : Formula ℒ b f)
    (θ : VariableSubstitution ℒ b b' f') (η : VariableSubstitution ℒ f b' f') (d : V.{u})
    (ρ : Env.{u} b' f') (τ : Env.{u} b f)
    (h : ∀ {s} (i : Variable b s), (θ i).eval ρ = τ.boundVal i)
    (k : ∀ {s} (i : Variable f s), (η i).eval ρ = τ.freeVal i) :
    sc_sat (φ.substituteMapped θ η) d ρ ↔ sc_sat φ d τ := by
  induction φ generalizing b' f' with
  | falsum | truth => exact Iff.rfl
  | equal t t' =>
    exact (sat_weaken (s := SetSort.set) (.equal (t.substituteMapped θ η) (t'.substituteMapped θ η)) ρ d).trans
      ((sat_eq _ _ _).trans ((tm_subst t θ η ρ τ h k) ▸ (tm_subst t' θ η ρ τ h k) ▸
        (sat_eq t t' τ).symm.trans (sat_weaken (s := SetSort.set) (.equal t t') τ d).symm))
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons t' .nil) =>
      (sat_weaken (s := SetSort.set) (.rel .membership (.cons (t.substituteMapped θ η)
        (.cons (t'.substituteMapped θ η) .nil))) ρ d).trans
        ((sat_mem _ _ _).trans ((tm_subst t θ η ρ τ h k) ▸ (tm_subst t' θ η ρ τ h k) ▸
          (sat_mem t t' τ).symm.trans
            (sat_weaken (s := SetSort.set) (.rel .membership (.cons t (.cons t' .nil))) τ d).symm))
  | neg _ ih => exact not_congr (ih _ _ _ _ h k)
  | conj _ _ ih ik => exact and_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k))
  | imp _ _ ih ik => exact imp_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | iff _ _ ih ik => exact st_iff_congr (ih _ _ _ _ h k) (ik _ _ _ _ h k)
  | forallE s φ ih | existsE s φ ih =>
    cases s
    have e x := ih (VariableSubstitution.liftBound SetSort.set θ)
      (VariableSubstitution.weakenBound SetSort.set η) (ρ.pushBound x) (τ.pushBound x)
      (fun i => match i with | .here => rfl | .there i => (tm_weaken _ ρ x).trans (h i))
      (fun i => (tm_weaken _ ρ x).trans (k i))
    first
    | exact ⟨fun p x hx => (e x).mp (p x hx), fun p x hx => (e x).mpr (p x hx)⟩
    | exact nn_congr ⟨fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mp p⟩,
        fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mpr p⟩⟩

/-- 消去带界全称时，直接输出原实例化公式的带界像。 -/
theorem sc_inst {b f} (φ : Formula ℒ (.set :: b) f) (t : Term ℒ b f SetSort.set)
    (d : V.{u}) (ρ : Env.{u} b f) (h : sc_sat (.forallE .set φ) d ρ)
    (k : t.eval ρ ∈ d) : sc_sat (φ.instantiateTop t) d ρ :=
  (sc_subst φ _ _ d ρ (ρ.pushBound (t.eval ρ))
    (fun i => match i with | .here => rfl | .there _ => rfl) (fun _ => rfl)).mpr
      (h (t.eval ρ) k)

/-- 同一成员证书也供原核的存在引入使用。 -/
theorem sc_exists {b f} (φ : Formula ℒ (.set :: b) f) (t : Term ℒ b f SetSort.set)
    (d : V.{u}) (ρ : Env.{u} b f) (h : sc_sat (φ.instantiateTop t) d ρ)
    (k : t.eval ρ ∈ d) : sc_sat (.existsE .set φ) d ρ :=
  nn_in ⟨t.eval ρ, k, (sc_subst φ _ _ d ρ (ρ.pushBound (t.eval ρ))
    (fun i => match i with | .here => rfl | .there _ => rfl) (fun _ => rfl)).mp h⟩

/-- info: 'YesMetaZFC.Model.Zermelo.sc_mp_up' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_mp_up
/-- info: 'YesMetaZFC.Model.Zermelo.sc_mp_down' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_mp_down
/-- info: 'YesMetaZFC.Model.Zermelo.sc_pool' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_pool
/-- info: 'YesMetaZFC.Model.Zermelo.sc_mp_fixed' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_mp_fixed
/-- info: 'YesMetaZFC.Model.Zermelo.sc_inst' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_inst
/-- info: 'YesMetaZFC.Model.Zermelo.sc_exists' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_exists
end YesMetaZFC.Model.Zermelo
