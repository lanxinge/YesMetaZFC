/-! # 异质值列

该有限积骨架只依赖排序族与分量类型，不依赖原生结构、模型公理或满足关系。
-/

namespace YesMetaZFC.Logic.FirstOrder
universe u x y z

/-- 由排序列表索引的异质语义值列。 -/
inductive Values {S : Type u} (Carrier : S → Type x) :
    List S → Type (max u x) where
  | nil : Values Carrier []
  | cons {sort : S} {sorts : List S} :
      Carrier sort → Values Carrier sorts → Values Carrier (sort :: sorts)

namespace Values

/-- 对异质值列逐排序应用一个载体映射。 -/
def map {S : Type u} {Source : S → Type x} {Target : S → Type y}
    (f : ∀ sort, Source sort → Target sort) :
    {sorts : List S} → Values Source sorts → Values Target sorts
  | _, .nil => .nil
  | _, .cons value rest => .cons (f _ value) (map f rest)

@[simp] theorem map_nil {S : Type u}
    {Source : S → Type x} {Target : S → Type y}
    (f : ∀ sort, Source sort → Target sort) :
    map f (.nil : Values Source []) = .nil := rfl

@[simp] theorem map_cons {S : Type u}
    {Source : S → Type x} {Target : S → Type y}
    (f : ∀ sort, Source sort → Target sort)
    {sort : S} {sorts : List S} (value : Source sort) (rest : Values Source sorts) :
    map f (.cons value rest) = .cons (f sort value) (map f rest) := rfl

/-- 异质值列逐项映射保持复合。 -/
theorem map_comp {S : Type u} {A : S → Type x} {B : S → Type y} {C : S → Type z}
    (g : ∀ s, B s → C s) (f : ∀ s, A s → B s) {ss} (ts : Values A ss) :
    (ts.map f).map g = ts.map (fun s a => g s (f s a)) := by
  induction ts with
  | nil => rfl
  | cons t ts h => exact congrArg (Values.cons (g _ (f _ t))) h

@[simp] theorem map_id {S : Type u} {A : S → Type x} {ss} (ts : Values A ss) :
    ts.map (fun _ a => a) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts h => exact congrArg (Values.cons t) h

end Values
end YesMetaZFC.Logic.FirstOrder
