import Std

/-!
# 宿主层滤子

用谓词表示子集、用谓词族表示子集族。该接口不要求载体有可判定等式，也不
在 `Type` 层选择代表元。普通滤子允许包含空集；需要通常意义下的真滤子时，
另加 `Filter.Proper`。

有限基生成只保存一个显式有限列表作证。有限交性质因此给出生成滤子为真的
构造性充分条件，不需要 Zorn 引理或选择公理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u v

namespace Filter

/-- 在 `α` 上的子集族，以子集谓词为参数。 -/
abbrev SetFamily (α : Type u) := (α → Prop) → Prop

/-- 全载体子集。 -/
def univSet {α : Type u} : α → Prop := fun _ => True

/-- 空子集。 -/
def emptySet {α : Type u} : α → Prop := fun _ => False

/-- 两个子集的交。 -/
def Inter {α : Type u} (s t : α → Prop) : α → Prop := fun x => s x ∧ t x

/-- 子集包含关系。 -/
def Subset {α : Type u} (s t : α → Prop) : Prop := ∀ ⦃x⦄, s x → t x

/-- 子集补集。 -/
def Complement {α : Type u} (s : α → Prop) : α → Prop := fun x => ¬ s x

end Filter

/-- `α` 上的滤子：包含全空间、向上封闭并对二元交封闭的子集族。 -/
structure Filter (α : Type u) where
  sets : Filter.SetFamily α
  univ_mem : sets Filter.univSet
  upward : ∀ ⦃s t : α → Prop⦄, sets s → Filter.Subset s t → sets t
  inter_mem : ∀ ⦃s t : α → Prop⦄, sets s → sets t → sets (Filter.Inter s t)

/-- 滤子不包含空集时称为真滤子。 -/
def Filter.Proper {α : Type u} (F : Filter α) : Prop := ¬ F.sets Filter.emptySet

namespace Filter

/-- 滤子成员关系的记号接口。 -/
instance {α : Type u} : Membership (α → Prop) (Filter α) :=
  ⟨fun F s => F.sets s⟩

/-- 若谓词的真值集属于滤子，则称该谓词最终成立。 -/
def Eventually {α : Type u} (F : Filter α) (p : α → Prop) : Prop := F.sets p

/-- 若谓词的补集不属于滤子，则称该谓词频繁成立。 -/
def Frequently {α : Type u} (F : Filter α) (p : α → Prop) : Prop :=
  ¬ F.sets (Complement p)

/-- 最终成立的谓词在逐点蕴含下保持。 -/
theorem Eventually.mono_l {α : Type u} {F : Filter α} {p q : α → Prop}
    (hp : Eventually F p) (hpq : Subset p q) : Eventually F q := F.upward hp hpq

/-- 两个最终成立的谓词最终同时成立。 -/
theorem Eventually.and_l {α : Type u} {F : Filter α} {p q : α → Prop}
    (hp : Eventually F p) (hq : Eventually F q) : Eventually F (Inter p q) :=
  F.inter_mem hp hq

/-- 由 `base` 生成的主滤子，即所有包含 `base` 的子集。 -/
def principal {α : Type u} (base : α → Prop) : Filter α where
  sets := fun s => Subset base s
  univ_mem := by
    intro x hx
    trivial
  upward := by
    intro s t hs hst x hx
    exact hst (hs hx)
  inter_mem := by
    intro s t hs ht x hx
    exact ⟨hs hx, ht hx⟩

/-- 像滤子：目标子集属于像滤子，当且仅当其原像属于原滤子。 -/
def map {α : Type u} {β : Type v} (f : α → β) (F : Filter α) : Filter β where
  sets := fun s => F.sets (fun x => s (f x))
  univ_mem := F.univ_mem
  upward := by
    intro s t hs hst
    apply F.upward hs
    intro x hx
    exact hst hx
  inter_mem := by
    intro s t hs ht
    exact F.inter_mem hs ht

/-- 映射保持真滤子，因为空集的原像仍为空集。 -/
theorem map_proper_of_proper_l {α : Type u} {β : Type v} {f : α → β} {F : Filter α}
    (hF : Proper F) : Proper (map f F) := by
  intro h
  exact hF h

/-- 拉回滤子：若 `s` 包含某个目标大集的原像，则 `s` 属于拉回滤子。 -/
def comap {α : Type u} {β : Type v} (f : α → β) (G : Filter β) : Filter α where
  sets := fun s => ∃ t, G.sets t ∧ Subset (fun x => t (f x)) s
  univ_mem := by
    refine ⟨univSet, G.univ_mem, ?_⟩
    intro x hx
    trivial
  upward := by
    intro s t hs hst
    rcases hs with ⟨u, hu, hsub⟩
    exact ⟨u, hu, fun x hx => hst (hsub hx)⟩
  inter_mem := by
    intro s t hs ht
    rcases hs with ⟨s', hs', hsubS⟩
    rcases ht with ⟨t', ht', hsubT⟩
    refine ⟨Inter s' t', G.inter_mem hs' ht', ?_⟩
    intro x hx
    change s' (f x) ∧ t' (f x) at hx
    exact ⟨hsubS hx.1, hsubT hx.2⟩

/-- 真滤子沿满射拉回仍为真滤子。 -/
theorem comap_proper_of_surjective_l {α : Type u} {β : Type v} {f : α → β} {G : Filter β}
    (hG : Proper G) (hf : Function.Surjective f) : Proper (comap f G) := by
  intro hEmpty
  rcases hEmpty with ⟨t, ht, hsub⟩
  apply hG
  apply G.upward ht
  intro y hy
  rcases hf y with ⟨x, rfl⟩
  exact hsub hy

/-- `f` 从 `F` 到 `G` 收敛，按目标大集的原像直接定义。 -/
def Tendsto {α : Type u} {β : Type v} (f : α → β) (F : Filter α) (G : Filter β) : Prop :=
  ∀ s, G.sets s → F.sets (fun x => s (f x))

/-- `f` 收敛到 `G`，当且仅当 `f` 的像滤子包含 `G` 的每个大集。 -/
theorem tendsto_iff_map_l {α : Type u} {β : Type v} {f : α → β} {F : Filter α} {G : Filter β} :
    Tendsto f F G ↔ ∀ s, G.sets s → (map f F).sets s := Iff.rfl

/-- 非空基生成的主滤子是真滤子。 -/
theorem proper_principal_of_nonempty_l {α : Type u} {s : α → Prop}
    (h : ∃ x, s x) : Proper (principal s) := by
  intro hEmpty
  rcases h with ⟨x, hx⟩
  exact hEmpty hx

/-- 主滤子为真至少保证其基非空的双重否定；此方向不消去双重否定。 -/
theorem not_not_nonempty_of_proper_principal_l {α : Type u} {s : α → Prop}
    (h : Proper (principal s)) : ¬¬ ∃ x, s x := by
  intro hn
  apply h
  intro x hx
  exact hn ⟨x, hx⟩

/-- 有限多个子集的交；空列表对应全空间。 -/
def finiteInter {α : Type u} : List (α → Prop) → α → Prop
  | [] => univSet
  | s :: ss => Inter s (finiteInter ss)

/-- 有限交与列表拼接相容。 -/
theorem finiteInter_append_l {α : Type u} (xs ys : List (α → Prop)) :
    ∀ x, finiteInter (xs ++ ys) x ↔ Inter (finiteInter xs) (finiteInter ys) x := by
  induction xs with
  | nil =>
      intro x
      simp [finiteInter, Inter, univSet]
  | cons s ss ih =>
      intro x
      simp only [List.cons_append, finiteInter, Inter]
      rw [ih x]
      constructor
      · rintro ⟨hs, hss, hys⟩
        exact ⟨⟨hs, hss⟩, hys⟩
      · rintro ⟨⟨hs, hss⟩, hys⟩
        exact ⟨hs, hss, hys⟩

/-- `base` has the finite intersection property when every finite subfamily has
nonempty intersection. Repetitions in the witnessing list are harmless. -/
def HasFiniteIntersectionProperty {α : Type u} (base : Filter.SetFamily α) : Prop :=
  ∀ xs : List (α → Prop), (∀ s, s ∈ xs → base s) → ∃ x, finiteInter xs x

/-- The filter generated by a family consists of supersets of its finite intersections. -/
def generated {α : Type u} (base : Filter.SetFamily α) : Filter α where
  sets := fun s => ∃ xs : List (α → Prop),
    (∀ t, t ∈ xs → base t) ∧ Filter.Subset (finiteInter xs) s
  univ_mem := by
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · intro x hx
      trivial
  upward := by
    intro s t hs hst
    rcases hs with ⟨xs, hbase, hsub⟩
    exact ⟨xs, hbase, fun x hx => hst (hsub hx)⟩
  inter_mem := by
    intro s t hs ht
    rcases hs with ⟨xs, hxs, hsubS⟩
    rcases ht with ⟨ys, hys, hsubT⟩
    refine ⟨xs ++ ys, ?_, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hxs v hv
      · exact hys v hv
    · intro x hx
      have hxy := (finiteInter_append_l xs ys x).mp hx
      change finiteInter xs x ∧ finiteInter ys x at hxy
      exact ⟨hsubS hxy.1, hsubT hxy.2⟩

/-- Every member of the basis belongs to its generated filter. -/
theorem base_mem_generated_l {α : Type u} {base : Filter.SetFamily α}
    {s : α → Prop} (hs : base s) : (generated base).sets s := by
  refine ⟨[s], ?_, ?_⟩
  · intro t ht
    have hts : t = s := by simpa using ht
    simpa [hts] using hs
  · intro x hx
    exact hx.1

/-- The finite intersection of basis members belongs to any filter containing the basis. -/
theorem finiteInter_mem_l {α : Type u} {base : Filter.SetFamily α} (F : Filter α)
    (hbase : ∀ s, base s → F.sets s) (xs : List (α → Prop))
    (hxs : ∀ s, s ∈ xs → base s) : F.sets (finiteInter xs) := by
  induction xs with
  | nil => exact F.univ_mem
  | cons s ss ih =>
      have hss : ∀ t, t ∈ ss → base t := by
        intro t ht
        exact hxs t (List.mem_cons_of_mem s ht)
      exact F.inter_mem (hbase s (hxs s List.mem_cons_self)) (ih hss)

/-- The generated filter is contained in every filter containing the basis. -/
theorem generated_le_of_base_l {α : Type u} {base : Filter.SetFamily α} (F : Filter α)
    (hbase : ∀ s, base s → F.sets s) :
    ∀ s, (generated base).sets s → F.sets s := by
  intro s hs
  rcases hs with ⟨xs, hxs, hsub⟩
  exact F.upward (finiteInter_mem_l F hbase xs hxs) hsub

/-- A finite-intersection family generates a proper filter. -/
theorem generated_proper_of_fip_l {α : Type u} {base : Filter.SetFamily α}
    (hbase : HasFiniteIntersectionProperty base) : Proper (generated base) := by
  intro hempty
  rcases hempty with ⟨xs, hxs, hsub⟩
  rcases hbase xs hxs with ⟨x, hx⟩
  exact hsub hx

/-- 真滤子不能同时包含一个集合及其补集。 -/
theorem not_complement_mem_of_proper_l {α : Type u} {F : Filter α}
    (hF : Proper F) {s : α → Prop} (hs : F.sets s) :
    ¬ F.sets (Complement s) := by
  intro hcomp
  apply hF
  apply F.upward (F.inter_mem hs hcomp)
  intro x hx
  exact hx.2 hx.1

/-- Containment of the underlying families of two filters. -/
def Extends {α : Type u} (F G : Filter α) : Prop :=
  ∀ s, F.sets s → G.sets s

/-- Maximality among proper filters, stated without choosing a larger filter. -/
def IsMaximalProper {α : Type u} (F : Filter α) : Prop :=
  Proper F ∧ ∀ G, Extends F G → Proper G → ∀ s, G.sets s → F.sets s

/-- 超滤定义为极大真滤子；补集判定留给单独的经典命题定理。 -/
abbrev IsUltrafilter {α : Type u} (F : Filter α) : Prop := IsMaximalProper F

end Filter
end SetTheory
end YesMetaZFC
