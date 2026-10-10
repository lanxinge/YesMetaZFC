import YesMetaZFC.Model.Zermelo.Semantics

/-! # 保留量词范围的升层
旧载体在上一宇宙中成为实际集合；公式中的全部量词显式限制到这个集合。
升层后的公式仍使用原始 AST 和高层的通常语义，不增加越界实例化规则。
本层证明受限升层的保真与收集交付，不断言任意原 ZF 推导都能完成这种处理。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory
universe u
attribute [local implicit_reducible] SetTheory.signature

/-- 原树的逐层嵌入；只扩大分支指标所在的宇宙。 -/
def gl_lift : V.{u} → V.{u+1}
  | .sup ι f => .sup (ULift.{u+1} ι) (fun i => gl_lift (f i.down))

theorem gl_eq : ∀ a b : V.{u}, V.eq (gl_lift a) (gl_lift b) ↔ V.eq a b
  | .sup _ _f, .sup _ _g =>
    ⟨fun h => ⟨fun i => st_use (h.1 ⟨i⟩) (fun ⟨j, e⟩ =>
        nn_in ⟨j.down, (gl_eq _ _).mp e⟩),
      fun j => st_use (h.2 ⟨j⟩) (fun ⟨i, e⟩ => nn_in ⟨i.down, (gl_eq _ _).mp e⟩)⟩,
     fun h => ⟨fun i => st_use (h.1 i.down) (fun ⟨j, e⟩ =>
        nn_in ⟨⟨j⟩, (gl_eq _ _).mpr e⟩),
      fun j => st_use (h.2 j.down) (fun ⟨i, e⟩ => nn_in ⟨⟨i⟩, (gl_eq _ _).mpr e⟩)⟩⟩

theorem gl_mem (a b : V.{u}) : gl_lift a ∈ gl_lift b ↔ a ∈ b := by
  cases b with
  | sup ι f =>
    exact nn_congr
      ⟨fun ⟨i, h⟩ => ⟨i.down, (gl_eq _ _).mp h⟩,
       fun ⟨i, h⟩ => ⟨⟨i⟩, (gl_eq _ _).mpr h⟩⟩

/-- 旧载体在高层中的实际集合，作为升层公式的量词范围。 -/
def gl_space : V.{u+1} := .sup V.{u} gl_lift

def gl_env {b f} (ρ : Env.{u} b f) : Env.{u+1} b f where
  boundVal i := gl_lift (ρ.boundVal i)
  freeVal i := gl_lift (ρ.freeVal i)

-- 新增的首个自由变量表示旧载体；源公式的自由变量全部后移一格。
def gl_form {b f} : Formula ℒ b f → Formula ℒ b (.set :: f)
  | .falsum => .falsum
  | .truth => .truth
  | .equal t s => .equal (t.weakenFree SetSort.set) (s.weakenFree SetSort.set)
  | .rel .membership (.cons t (.cons s .nil)) =>
      .rel .membership (.cons (t.weakenFree SetSort.set) (.cons (s.weakenFree SetSort.set) .nil))
  | .neg p => .neg (gl_form p)
  | .conj p q => .conj (gl_form p) (gl_form q)
  | .disj p q => .disj (gl_form p) (gl_form q)
  | .imp p q => .imp (gl_form p) (gl_form q)
  | .iff p q => .iff (gl_form p) (gl_form q)
  | .forallE .set p => .forallE .set (.imp
      (.rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil))) (gl_form p))
  | .existsE .set p => .existsE .set (.conj
      (.rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil))) (gl_form p))

theorem gl_tm {b f s} (t : Term ℒ b f s) (ρ : Env.{u} b f) (a : V.{u+1}) :
    (t.weakenFree SetSort.set).eval ((gl_env ρ).pushFree a) = gl_lift (t.eval ρ) := by
  cases t with
  | bvar _ | fvar _ => rfl
  | app g _ => nomatch g

theorem gl_push {b f} (ρ : Env.{u} b f) (x : V.{u}) (a : V.{u+1}) :
    Env_rel (((gl_env ρ).pushFree (sort := SetSort.set) a).pushBound (gl_lift x))
      ((gl_env (ρ.pushBound (sort := SetSort.set) x)).pushFree (sort := SetSort.set) a) :=
  ⟨(fun i => match i with | .here => V.eq_refl _ | .there _ => V.eq_refl _),
    fun _ => V.eq_refl _⟩

/-- 任意原公式的精确保真；包含任意量词交替和否定。 -/
theorem gl_sat {b f} (φ : Formula ℒ b f) (ρ : Env.{u} b f) :
    sat (gl_form φ) ((gl_env ρ).pushFree gl_space) ↔ sat φ ρ := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | equal t s =>
    exact (sat_eq _ _ _).trans ((gl_tm t ρ gl_space) ▸ (gl_tm s ρ gl_space) ▸
      (gl_eq _ _).trans (sat_eq t s ρ).symm)
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons s .nil) =>
      (sat_mem _ _ _).trans ((gl_tm t ρ gl_space) ▸ (gl_tm s ρ gl_space) ▸
        (gl_mem _ _).trans (sat_mem t s ρ).symm)
  | neg _ ih => exact not_congr (ih ρ)
  | conj _ _ ih ik => exact and_congr (ih ρ) (ik ρ)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih ρ) (ik ρ))
  | imp _ _ ih ik => exact imp_congr (ih ρ) (ik ρ)
  | iff _ _ ih ik => exact st_iff_congr (ih ρ) (ik ρ)
  | forallE s φ ih =>
    cases s
    constructor
    · intro h x
      exact (ih (ρ.pushBound x)).mp ((sat_congr (gl_form φ) (gl_push ρ x gl_space)).mp
        (h (gl_lift x) (V.elem_mem gl_space x)))
    · intro h x hx
      apply st_use hx
      intro ⟨y, e⟩
      exact (sat_congr (gl_form φ) (env_push (env_refl _) e)).mpr
        ((sat_congr (gl_form φ) (gl_push ρ y gl_space)).mpr ((ih (ρ.pushBound y)).mpr (h y)))
  | existsE s φ ih =>
    cases s
    constructor
    · intro h
      apply st_use h
      intro ⟨x, hx, h⟩
      -- 此处只在稳定存在中取得旧代表，不从成员证明中选择数据。
      exact st_use hx (fun ⟨y, e⟩ => nn_in ⟨y, (ih (ρ.pushBound y)).mp
        ((sat_congr (gl_form φ) (gl_push ρ y gl_space)).mp
          ((sat_congr (gl_form φ) (env_push (env_refl _) e)).mp h))⟩)
    · intro h
      exact st_use h (fun ⟨y, h⟩ => nn_in ⟨gl_lift y, V.elem_mem gl_space y,
        (sat_congr (gl_form φ) (gl_push ρ y gl_space)).mpr ((ih (ρ.pushBound y)).mpr h)⟩)

def gl_args {b f} (ρ : Env.{u} b f) (x y : V.{u}) : Env.{u} b (.set :: .set :: f) :=
  (ρ.pushFree x).pushFree y

theorem gl_bind {b f} (ρ : Env.{u} b f) (x y : V.{u}) (x' y' : V.{u+1})
    (h : V.eq (gl_lift x) x') (k : V.eq (gl_lift y) y') :
    Env_rel (f := .set :: .set :: .set :: f) ((gl_env (gl_args ρ x y)).pushFree gl_space)
      ((gl_args (gl_env ρ) x' y').pushFree gl_space) :=
  ⟨(fun _ => V.eq_refl _), fun i => match i with
    | .here => V.eq_refl _
    | .there .here => k
    | .there (.there .here) => h
    | .there (.there (.there _)) => V.eq_refl _⟩

theorem gl_member (a : V.{u}) {x : V.{u+1}} (h : x ∈ gl_lift a) :
    ¬¬∃ y : V.{u}, y ∈ a ∧ V.eq x (gl_lift y) := by
  cases a with
  | sup ι f => exact st_use h (fun ⟨⟨i⟩, e⟩ => nn_in ⟨f i, V.elem_mem (.sup ι f) i, e⟩)

/-- 范围已经固定的公式可再次升层，沿用原范围与原证明，不重建收集见证。 -/
theorem gl_abs {b f} (φ : Formula ℒ b f) (a : V.{u}) (ρ : Env.{u} b f) :
    sat (gl_form φ) ((gl_env ρ).pushFree (gl_lift a)) ↔ sat (gl_form φ) (ρ.pushFree a) := by
  induction φ with
  | falsum | truth => exact Iff.rfl
  | equal t s =>
    exact (sat_eq _ _ _).trans ((gl_tm t ρ (gl_lift a)) ▸ (gl_tm s ρ (gl_lift a)) ▸
      (gl_eq _ _).trans ((sat_eq t s ρ).symm.trans
        (sat_weaken (s := SetSort.set) (.equal t s) ρ a).symm))
  | rel r ts =>
    exact match r, ts with
    | .membership, .cons t (.cons s .nil) =>
      (sat_mem _ _ _).trans ((gl_tm t ρ (gl_lift a)) ▸ (gl_tm s ρ (gl_lift a)) ▸
        (gl_mem _ _).trans ((sat_mem t s ρ).symm.trans
          (sat_weaken (s := SetSort.set) (.rel .membership (.cons t (.cons s .nil))) ρ a).symm))
  | neg _ ih => exact not_congr (ih ρ)
  | conj _ _ ih ik => exact and_congr (ih ρ) (ik ρ)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih ρ) (ik ρ))
  | imp _ _ ih ik => exact imp_congr (ih ρ) (ik ρ)
  | iff _ _ ih ik => exact st_iff_congr (ih ρ) (ik ρ)
  | forallE s φ ih =>
    cases s
    constructor
    · intro h x hx
      exact (ih (ρ.pushBound x)).mp ((sat_congr (gl_form φ) (gl_push ρ x (gl_lift a))).mp
        (h (gl_lift x) ((gl_mem x a).mpr hx)))
    · intro h x hx
      exact st_use (gl_member a hx) (fun ⟨y, hy, e⟩ =>
        (sat_congr (gl_form φ) (env_push (env_refl _) e)).mpr
          ((sat_congr (gl_form φ) (gl_push ρ y (gl_lift a))).mpr
            ((ih (ρ.pushBound y)).mpr (h y hy))))
  | existsE s φ ih =>
    cases s
    constructor
    · intro h
      exact st_use h (fun ⟨x, hx, h⟩ => st_use (gl_member a hx) (fun ⟨y, hy, e⟩ =>
        nn_in ⟨y, hy, (ih (ρ.pushBound y)).mp
          ((sat_congr (gl_form φ) (gl_push ρ y (gl_lift a))).mp
            ((sat_congr (gl_form φ) (env_push (env_refl _) e)).mp h))⟩))
    · intro h
      exact st_use h (fun ⟨y, hy, h⟩ => nn_in ⟨gl_lift y, (gl_mem y a).mpr hy,
        (sat_congr (gl_form φ) (gl_push ρ y (gl_lift a))).mpr ((ih (ρ.pushBound y)).mpr h)⟩)

/-- 保留全部关系见证的显式池，不选取代表。 -/
def gl_pool {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f)
    (a : V.{u}) : V.{u+1} :=
  .sup {y : V.{u} // ∃ x, x ∈ a ∧ sat φ (gl_args ρ x y)} (fun y => gl_lift y.val)

/-- 池的精确成员式：在高层旧范围中，对源关系作有界投影。 -/
theorem gl_pool_mem {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f)
    (a : V.{u}) (y : V.{u+1}) : y ∈ gl_pool φ ρ a ↔ y ∈ gl_space ∧
      ¬¬∃ x : V.{u+1}, x ∈ gl_lift a ∧
        sat (gl_form φ) ((gl_args (gl_env ρ) x y).pushFree gl_space) := by
  constructor
  · intro h
    exact st_use h (fun ⟨⟨z, x, hx, hz⟩, e⟩ =>
      ⟨(V.mem_left e).mpr (V.elem_mem gl_space z), nn_in
        ⟨gl_lift x, (gl_mem x a).mpr hx,
          (sat_congr (gl_form φ) (gl_bind ρ x z (gl_lift x) y (V.eq_refl _) (V.eq_symm e))).mp
            ((gl_sat φ (gl_args ρ x z)).mpr hz)⟩⟩)
  · intro ⟨hy, h⟩
    apply st_use hy
    intro ⟨z, e⟩
    apply st_use h
    intro ⟨x, hx, hr⟩
    exact st_use (gl_member a hx) (fun ⟨w, hw, d⟩ => nn_in ⟨⟨z, w, hw,
      (gl_sat φ (gl_args ρ w z)).mp ((sat_congr (gl_form φ)
        (gl_bind ρ w z x y (V.eq_symm d) (V.eq_symm e))).mpr hr)⟩, e⟩)

/-- 整个收集对象的代数正规形；外延相等可用于原公式的任意上下文。 -/
theorem gl_pool_eq {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f)
    (a : V.{u}) : V.eq (gl_pool φ ρ a) (V.sep gl_space (fun y =>
      ¬¬∃ x : V.{u+1}, x ∈ gl_lift a ∧
        sat (gl_form φ) ((gl_args (gl_env ρ) x y).pushFree gl_space))) := by
  let p := fun y => ¬¬∃ x : V.{u+1}, x ∈ gl_lift a ∧
    sat (gl_form φ) ((gl_args (gl_env ρ) x y).pushFree gl_space)
  have he : ∀ {y z}, V.eq y z → p y → p z := fun {y z} e h => st_use h (fun ⟨x, hx, hr⟩ =>
    nn_in ⟨x, hx, (sat_congr (gl_form φ)
      (ρ := (gl_args (gl_env ρ) x y).pushFree gl_space)
      (τ := (gl_args (gl_env ρ) x z).pushFree gl_space)
      ⟨(fun _ => V.eq_refl _), fun i => match i with
      | .here => V.eq_refl _
      | .there .here => e
      | .there (.there _) => V.eq_refl _⟩).mp hr⟩)
  exact V.ext (fun y => (gl_pool_mem φ ρ a y).trans (V.sep_mem gl_space y p he).symm)

/-- 同一旧范围上的所有收集输出，统一落在它的幂集中，与公式复杂度无关。 -/
theorem gl_pool_bound {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f)
    (a : V.{u}) : gl_pool φ ρ a ∈ V.power gl_space :=
  (V.power_mem _ _).mpr (fun y h => ((gl_pool_mem φ ρ a y).mp h).1)

/-- 收集容器留在高层，内部关系交付为高层原语义下的带界公式。 -/
theorem gl_collect {b f} (φ : Formula ℒ b (.set :: .set :: f)) (ρ : Env.{u} b f)
    (a : V.{u}) (h : ∀ x : V.{u}, x ∈ a → ¬¬∃ y : V.{u}, sat φ (gl_args ρ x y)) :
    V.sub (gl_pool φ ρ a) gl_space ∧ ∀ x : V.{u+1}, x ∈ gl_lift a →
      ¬¬∃ y : V.{u+1}, y ∈ gl_pool φ ρ a ∧
        sat (gl_form φ) ((gl_args (gl_env ρ) x y).pushFree gl_space) := by
  refine ⟨fun x hx => ((gl_pool_mem φ ρ a x).mp hx).1, fun x hx => ?_⟩
  apply st_use (gl_member a hx)
  intro ⟨z, hz, e⟩
  apply st_use (h z hz)
  intro ⟨y, hy⟩
  have k := (sat_congr (gl_form φ)
    (gl_bind ρ z y x (gl_lift y) (V.eq_symm e) (V.eq_refl _))).mp
      ((gl_sat φ (gl_args ρ z y)).mpr hy)
  exact nn_in ⟨gl_lift y, (gl_pool_mem φ ρ a (gl_lift y)).mpr
    ⟨V.elem_mem gl_space y, nn_in ⟨x, hx, k⟩⟩, k⟩

/-- 高层通常的全称消去：旧范围条件由变换后的公式本身给出。 -/
theorem gl_use {f} (φ : Formula ℒ [SetSort.set] f)
    (t : OpenTerm ℒ (.set :: f) SetSort.set) (ρ : Env.{u} [] (.set :: f))
    (h : sat (gl_form (.forallE .set φ)) ρ) (k : t.eval ρ ∈ ρ.freeVal .here) :
    sat ((gl_form φ).instantiateTop t) ρ :=
  (sat_inst (gl_form φ) t ρ).mpr (h (t.eval ρ) k)

/-- info: 'YesMetaZFC.Model.Zermelo.gl_collect' does not depend on any axioms -/
#guard_msgs in
#print axioms gl_collect
/-- info: 'YesMetaZFC.Model.Zermelo.gl_use' does not depend on any axioms -/
#guard_msgs in
#print axioms gl_use
/-- info: 'YesMetaZFC.Model.Zermelo.gl_abs' does not depend on any axioms -/
#guard_msgs in
#print axioms gl_abs
/-- info: 'YesMetaZFC.Model.Zermelo.gl_pool_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms gl_pool_eq
/-- info: 'YesMetaZFC.Model.Zermelo.gl_pool_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms gl_pool_bound
end YesMetaZFC.Model.Zermelo
