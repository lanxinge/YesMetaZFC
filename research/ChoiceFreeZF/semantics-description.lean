import Init

/-! # 唯一描述的 W 型闭包

先在命题中证明描述的子树关系良基，再通过良基递归重建树。
最后给出实际描述完备树、原等号关系替换及外延性反例；不声明 ZF 模型。
-/

namespace ZFDescription
universe u v

/-- 描述以单元素谓词给出；存在性一直留在 Prop。 -/
def D (A : Type u) := {p : A → Prop // ∃ a, ∀ b, p b ↔ b = a}

def pure {A : Type u} (a : A) : D A := ⟨fun b => b = a, a, fun _ => Iff.rfl⟩

theorem eq_pure {A : Type u} (d : D A) {a : A} (h : d.val a) : d = pure a := by
  obtain ⟨b, hb⟩ := d.property
  have ha : a = b := (hb a).mp h
  apply Subtype.ext
  exact funext (fun c => propext (by simpa only [pure, ha] using hb c))

theorem exists_pure {A : Type u} (d : D A) : ∃ a, d = pure a := by
  obtain ⟨a, ha⟩ := d.property
  exact ⟨a, eq_pure d ((ha a).mpr rfl)⟩

theorem pure_inj {A : Type u} {a b : A} (h : pure a = pure b) : a = b := by
  have h' : (pure b).val a := h ▸ (show (pure a).val a from rfl)
  exact h'

def map {A : Type u} {B : Type v} (f : A → B) (d : D A) : D B :=
  ⟨fun b => ∃ a, d.val a ∧ f a = b, by
    obtain ⟨a, ha⟩ := exists_pure d
    subst d
    refine ⟨f a, fun b => ?_⟩
    constructor
    · intro ⟨a', h, hf⟩; change a' = a at h; simpa only [h] using hf.symm
    · intro h; exact ⟨a, rfl, h.symm⟩⟩

theorem map_pure {A : Type u} {B : Type v} (f : A → B) (a : A) :
    map f (pure a) = pure (f a) := eq_pure _ ⟨a, rfl, rfl⟩

def join {A : Type u} (d : D (D A)) : D A :=
  ⟨fun a => ∃ p, d.val p ∧ p.val a, by
    obtain ⟨p, hp⟩ := exists_pure d
    obtain ⟨a, ha⟩ := exists_pure p
    subst d; subst p
    refine ⟨a, fun b => ?_⟩
    constructor
    · intro ⟨p, hp, hb⟩; change p = pure a at hp; subst p; exact hb
    · intro h; exact ⟨pure a, rfl, h⟩⟩

theorem join_pure {A : Type u} (d : D A) : join (pure d) = d := by
  obtain ⟨a, ha⟩ := exists_pure d
  subst d
  exact eq_pure _ ⟨pure a, rfl, rfl⟩

inductive WT (A : Type u) (B : A → Type v) : Type (max u v)
  | sup (a : A) (f : B a → WT A B)

namespace WT
variable {A : Type u} {B : A → Type v}

def head : WT A B → A | .sup a _ => a
def branch : (w : WT A B) → B w.head → WT A B | .sup _ f => f

theorem sup_congr {a b : A} {f : B a → WT A B} {g : B b → WT A B}
    (h : a = b) (hf : ∀ i, f i = g (h ▸ i)) : sup a f = sup b g := by
  cases h
  congr
  funext i
  exact hf i

variable (r : D A → A) (hr : ∀ a, r (pure a) = a)

def hd (d : D (WT A B)) : A := r (map head d)

include hr

theorem hd_pure (w : WT A B) : hd r (pure w) = w.head := by
  unfold hd
  rw [map_pure, hr]

theorem hd_eq (d : D (WT A B)) {w : WT A B} (h : d.val w) : hd r d = w.head := by
  rw [eq_pure d h, hd_pure r hr]

def ch (d : D (WT A B)) (i : B (hd r d)) : D (WT A B) :=
  ⟨fun t => ∃ w, ∃ h : d.val w, t = w.branch ((hd_eq r hr d h) ▸ i), by
    obtain ⟨w, hw⟩ := exists_pure d
    subst d
    refine ⟨w.branch ((hd_pure r hr w) ▸ i), fun t => ?_⟩
    constructor
    · intro ⟨w', h, ht⟩
      change w' = w at h
      subst w'
      exact ht
    · intro ht
      exact ⟨w, rfl, ht⟩⟩

theorem ch_pure (w : WT A B) (i : B (hd r (pure w))) :
    ch r hr (pure w) i = pure (w.branch ((hd_pure r hr w) ▸ i)) := by
  apply eq_pure
  exact ⟨w, rfl, rfl⟩

def rel (e d : D (WT A B)) : Prop := ∃ i, e = ch r hr d i

theorem wf : WellFounded (rel r hr (B := B)) := by
  constructor
  intro d
  obtain ⟨w, hw⟩ := exists_pure d
  subst d
  induction w with
  | sup a f ih =>
    apply Acc.intro
    intro e he
    obtain ⟨i, hi⟩ := he
    subst e
    rw [ch_pure]
    exact ih _

def retract (d : D (WT A B)) : WT A B :=
  WellFounded.fix (C := fun _ => WT A B) (wf r hr)
    (fun e f => WT.sup (hd r e) (fun i => f (ch r hr e i) ⟨i, rfl⟩)) d

theorem retract_eq (d : D (WT A B)) :
    retract r hr d = .sup (hd r d) (fun i => retract r hr (ch r hr d i)) :=
  WellFounded.fix_eq (wf r hr) _ d

theorem retract_pure (w : WT A B) : retract r hr (pure w) = w := by
  induction w with
  | sup a f ih =>
    rw [retract_eq]
    apply sup_congr (hd_pure r hr (WT.sup a f))
    intro i
    rw [ch_pure]
    exact ih _

theorem retract_spec (d : D (WT A B)) : d.val (retract r hr d) := by
  obtain ⟨w, hw⟩ := exists_pure d
  subst d
  rw [retract_pure r hr]
  rfl

end WT

/-- 实际标签宇宙；纤维允许位于同一大层，W 本身不再升层。 -/
abbrev U := D (Type u)
abbrev Point := D (Σ T : Type u, T)
def El (a : U.{u}) : Type (u+1) := {x : Point.{u} // map Sigma.fst x = a}
abbrev Tree := WT U.{u} El

def tree_desc (d : D Tree.{u}) : Tree.{u} :=
  WT.retract join join_pure d

theorem tree_desc_pure (w : Tree.{u}) : tree_desc (pure w) = w :=
  WT.retract_pure join join_pure w

theorem tree_desc_spec (d : D Tree.{u}) : d.val (tree_desc d) :=
  WT.retract_spec join join_pure d

def el_embed {T : Type u} (t : T) : El (pure T) :=
  ⟨pure (⟨T, t⟩ : Σ T : Type u, T),
    map_pure (fun x : (Σ T : Type u, T) => x.fst) ⟨T, t⟩⟩

theorem el_exists {T : Type u} (i : El (pure T)) : ∃ t, i = el_embed t := by
  obtain ⟨⟨S, s⟩, hs⟩ := exists_pure i.val
  have ht : S = T := pure_inj (by simpa only [hs, map_pure] using i.property)
  subst S
  exact ⟨s, Subtype.ext hs⟩

theorem el_inj {T : Type u} {s t : T} (h : el_embed s = el_embed t) : s = t := by
  have hs : (⟨T, s⟩ : Σ T : Type u, T) = ⟨T, t⟩ := pure_inj (congrArg Subtype.val h)
  cases hs
  rfl

def el_desc {T : Type u} (i : El (pure T)) : D T :=
  ⟨fun t => i = el_embed t, by
    obtain ⟨t, ht⟩ := el_exists i
    refine ⟨t, fun s => ?_⟩
    constructor
    · intro hs; exact el_inj (hs.symm.trans ht)
    · intro hs; exact hs ▸ ht⟩

theorem el_desc_embed {T : Type u} (t : T) : el_desc (el_embed t) = pure t :=
  eq_pure _ rfl

def small_root {I : Type u} (f : I → Tree.{u}) : Tree.{u} :=
  WT.sup (pure I) (fun i => tree_desc (map f (el_desc i)))

def Mem (x y : Tree.{u}) : Prop := ∃ i, x = y.branch i

theorem small_root_mem {I : Type u} (f : I → Tree.{u}) (x : Tree.{u}) :
    Mem x (small_root f) ↔ ∃ i, x = f i := by
  constructor
  · intro ⟨i, hi⟩
    obtain ⟨t, ht⟩ := el_exists i
    subst i
    exact ⟨t, by simpa only [small_root, WT.branch, el_desc_embed, map_pure,
      tree_desc_pure] using hi⟩
  · intro ⟨i, hi⟩
    refine ⟨el_embed i, ?_⟩
    simpa only [small_root, WT.branch, el_desc_embed, map_pure, tree_desc_pure] using hi

/-- 这里只承诺原类型等号的唯一性；不把双模拟唯一性混入前提。 -/
def replacement (G : Tree.{u}) (R : Tree.{u} → Tree.{u} → Prop)
    (h : ∀ x, Mem x G → ∃ y, ∀ z, R x z ↔ z = y) : Tree.{u} :=
  WT.sup G.head (fun i => tree_desc ⟨R (G.branch i), h _ ⟨i, rfl⟩⟩)

attribute [local implicit_reducible] Mem replacement

theorem replacement_mem (G : Tree.{u}) (R : Tree.{u} → Tree.{u} → Prop)
    (h : ∀ x, Mem x G → ∃ y, ∀ z, R x z ↔ z = y) (y : Tree.{u}) :
    Mem y (replacement G R h) ↔ ∃ x, Mem x G ∧ R x y := by
  constructor
  · intro ⟨i, hi⟩
    refine ⟨G.branch i, ⟨i, rfl⟩, ?_⟩
    rw [hi]
    exact tree_desc_spec ⟨R (G.branch i), h _ ⟨i, rfl⟩⟩
  · intro ⟨x, ⟨i, hi⟩, hxy⟩
    subst x
    refine ⟨i, ?_⟩
    change y = tree_desc ⟨R (G.branch i), h _ ⟨i, rfl⟩⟩
    rw [eq_pure (⟨R (G.branch i), h _ ⟨i, rfl⟩⟩ : D Tree) hxy, tree_desc_pure]

def identity_image (G : Tree.{u}) : Tree.{u} :=
  replacement G (fun x y => y = x) (fun x _ => ⟨x, fun _ => Iff.rfl⟩)

theorem identity_image_mem (G y : Tree.{u}) : Mem y (identity_image G) ↔ Mem y G := by
  rw [identity_image, replacement_mem]
  exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩

def empty : Tree.{u} := small_root (fun x : PEmpty.{u+1} => PEmpty.elim x)
def singleton_bool : Tree.{0} := small_root (fun _ : Bool => empty)
def singleton_unit : Tree.{0} := small_root (fun _ : PUnit => empty)

theorem singleton_same_members (x : Tree.{0}) : Mem x singleton_bool ↔ Mem x singleton_unit := by
  rw [singleton_bool, singleton_unit, small_root_mem, small_root_mem]
  exact ⟨fun ⟨_, h⟩ => ⟨PUnit.unit, h⟩, fun ⟨_, h⟩ => ⟨false, h⟩⟩

theorem singleton_distinct : singleton_bool ≠ singleton_unit := by
  intro h
  have ht : Bool = PUnit := pure_inj (congrArg WT.head h)
  have hs : Subsingleton Bool := ht.symm ▸ (inferInstance : Subsingleton PUnit)
  have he : false = true := hs.elim false true
  cases he

#print axioms join
#print axioms WT.wf
#print axioms WT.retract
#print axioms WT.retract_pure
#print axioms tree_desc
#print axioms tree_desc_pure
#print axioms tree_desc_spec
#print axioms small_root_mem
#print axioms replacement_mem
#print axioms identity_image_mem
#print axioms singleton_same_members
#print axioms singleton_distinct
end ZFDescription
