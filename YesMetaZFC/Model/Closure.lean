/-! # 任意指标族的多排序闭包

一条规则由一族已给定的输入和一个输出组成；指标可以打包运算符、实参及定义域证书。
排序、载体、规则指标及输入指标分别保持 universe 多态，不要求可数性或有限性。
归纳闭包不选择数据，也不提升载体。无限元规则同样适用，但不声称 ω 步即封闭。
-/

namespace YesMetaZFC.Model
universe u v w x y z

/-- 已实例化规则的任意指标族；零输入规则允许生成常元。 -/
structure RuleFamily_l {S : Type u} (C : S → Type v) (I : Type w) where
  Arity : I → Type x
  sort : (i : I) → Arity i → S
  arg : (i : I) → (j : Arity i) → C (sort i j)
  target : I → S
  value : (i : I) → C (target i)

namespace RuleFamily_l
variable {S : Type u} {C : S → Type v} {I : Type w}
variable (F : RuleFamily_l.{u, v, w, x} C I)

/-- 将任意多排序运算族实例化为规则；指标不要求可数，元数不要求有限。 -/
def of_operations_l (J : I → Type x) (s : (i : I) → J i → S) (t : I → S)
    (f : (i : I) → ((j : J i) → C (s i j)) → C (t i)) :
    RuleFamily_l C (Σ i, (j : J i) → C (s i j)) where
  Arity i := J i.1
  sort i := s i.1
  arg i := i.2
  target i := t i.1
  value i := f i.1 i.2

def Closed_l (A : ∀ s, C s → Prop) : Prop :=
  ∀ i, (∀ j, A (F.sort i j) (F.arg i j)) → A (F.target i) (F.value i)

/-- 实际最小闭包；递归前提仅出现在正位置。 -/
inductive Closure_l (A : ∀ s, C s → Prop) : ∀ s, C s → Prop where
  | seed {s a} : A s a → Closure_l A s a
  | rule (i : I) : (∀ j, Closure_l A (F.sort i j) (F.arg i j)) →
      Closure_l A (F.target i) (F.value i)

theorem closed_l (A : ∀ s, C s → Prop) : F.Closed_l (F.Closure_l A) :=
  Closure_l.rule

theorem least_l {A B : ∀ s, C s → Prop} (h : ∀ s a, A s a → B s a)
    (hB : F.Closed_l B) {s a} (ha : F.Closure_l A s a) : B s a := by
  induction ha with
  | seed ha => exact h _ _ ha
  | rule i _ ih => exact hB i ih

theorem mono_l {A B : ∀ s, C s → Prop} (h : ∀ s a, A s a → B s a)
    {s a} (ha : F.Closure_l A s a) : F.Closure_l B s a :=
  F.least_l (fun s a ha => .seed (h s a ha)) (F.closed_l B) ha

theorem closure_iff_l {A : ∀ s, C s → Prop} (hA : F.Closed_l A) {s a} :
    F.Closure_l A s a ↔ A s a :=
  ⟨F.least_l (fun _ _ h => h) hA, Closure_l.seed⟩

theorem idempotent_l (A : ∀ s, C s → Prop) {s a} :
    F.Closure_l (F.Closure_l A) s a ↔ F.Closure_l A s a :=
  F.closure_iff_l (F.closed_l A)

/-- 重编号或选取任意子族，不需要给指标选择逆函数。 -/
def reindex_l {J : Type y} (g : J → I) : RuleFamily_l C J where
  Arity j := F.Arity (g j)
  sort j := F.sort (g j)
  arg j := F.arg (g j)
  target j := F.target (g j)
  value j := F.value (g j)

theorem reindex_le_l {J : Type y} (g : J → I) {A : ∀ s, C s → Prop} {s a}
    (h : (F.reindex_l g).Closure_l A s a) : F.Closure_l A s a :=
  (F.reindex_l g).least_l (B := F.Closure_l A) (fun _ _ => Closure_l.seed)
    (fun j h => Closure_l.rule (g j) h) h

theorem reindex_iff_l {J : Type y} (g : J → I) (hg : Function.Surjective g)
    {A : ∀ s, C s → Prop} {s a} :
    (F.reindex_l g).Closure_l A s a ↔ F.Closure_l A s a := by
  refine ⟨F.reindex_le_l g, F.least_l (fun _ _ => Closure_l.seed) ?_⟩
  intro i h
  obtain ⟨j, rfl⟩ := hg i
  exact Closure_l.rule j h

/-- 合并两个规则族；只提升输入指标，不提升模型载体。 -/
def sum_l {J : Type y} (G : RuleFamily_l.{u, v, y, z} C J) : RuleFamily_l C (I ⊕ J) where
  Arity
    | .inl i => ULift.{z} (F.Arity i)
    | .inr i => ULift.{x} (G.Arity i)
  sort
    | .inl i, j => F.sort i j.down
    | .inr i, j => G.sort i j.down
  arg
    | .inl i, j => F.arg i j.down
    | .inr i, j => G.arg i j.down
  target
    | .inl i => F.target i
    | .inr i => G.target i
  value
    | .inl i => F.value i
    | .inr i => G.value i

theorem sum_closed_iff_l {J : Type y} (G : RuleFamily_l.{u, v, y, z} C J)
    (A : ∀ s, C s → Prop) :
    (F.sum_l G).Closed_l A ↔ F.Closed_l A ∧ G.Closed_l A := by
  constructor
  · intro h
    exact ⟨fun i hi => h (.inl i) (fun j => hi j.down),
      fun i hi => h (.inr i) (fun j => hi j.down)⟩
  · rintro ⟨hF, hG⟩ (i | i) h
    · exact hF i (fun j => h ⟨j⟩)
    · exact hG i (fun j => h ⟨j⟩)

/-- 合并任意指标族的规则，允许每个分量具有不同的规则指标类型。 -/
def union_l {K : Type y} {J : K → Type w}
    (G : (k : K) → RuleFamily_l.{u, v, w, x} C (J k)) :
    RuleFamily_l C (Sigma J) where
  Arity i := (G i.1).Arity i.2
  sort i := (G i.1).sort i.2
  arg i := (G i.1).arg i.2
  target i := (G i.1).target i.2
  value i := (G i.1).value i.2

theorem union_closed_iff_l {K : Type y} {J : K → Type w}
    (G : (k : K) → RuleFamily_l.{u, v, w, x} C (J k)) (A : ∀ s, C s → Prop) :
    (union_l G).Closed_l A ↔ ∀ k, (G k).Closed_l A :=
  ⟨fun h k j => h ⟨k, j⟩, fun h i => h i.1 i.2⟩

/-- 任意生成族先逐个闭包再合并，与合并后闭包相同；不是说闭集之并总是闭。 -/
theorem closure_union_iff_l {K : Type y} (A : K → ∀ s, C s → Prop) {s a} :
    F.Closure_l (fun s a => ∃ k, F.Closure_l (A k) s a) s a ↔
      F.Closure_l (fun s a => ∃ k, A k s a) s a := by
  constructor
  · apply F.least_l _ (F.closed_l _)
    rintro s a ⟨k, h⟩
    exact F.mono_l (fun s a ha => ⟨k, ha⟩) h
  · apply F.mono_l
    rintro s a ⟨k, h⟩
    exact ⟨k, .seed h⟩

end RuleFamily_l
end YesMetaZFC.Model
