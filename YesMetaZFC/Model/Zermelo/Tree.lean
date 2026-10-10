import Init

/-! # 无附加公理的稳定集合树

载体保留小分支良基树；对象等号是逐层稳定双模拟，不取商。
存在与析取取双重否定解释。基础只消费稳定谓词的成员归纳，
不把它加强成稳定成员关系的 `Acc`，因此不引入替换所需的额外强度。
这一语义思路参见 Carneiro, arXiv:2609.23143, §8。
-/

namespace YesMetaZFC.Model.Zermelo
universe u v

/-- 稳定性只是一项已证明的逻辑闭包性质。 -/
class St (p : Prop) : Prop where
  elim : (¬¬p) → p

theorem nn_in {p : Prop} (h : p) : ¬¬p := fun n => n h

theorem st_use {p q : Prop} [St q] (h : ¬¬p) (f : p → q) : q :=
  St.elim (fun n => h (fun hp => n (f hp)))

instance st_false : St False := ⟨fun h => h id⟩
instance st_true : St True := ⟨fun _ => trivial⟩
instance st_imp {p q : Prop} [St q] : St (p → q) :=
  ⟨fun h hp => St.elim (fun n => h (fun f => n (f hp)))⟩
instance st_not {p : Prop} : St (¬p) :=
  ⟨fun h hp => h (fun n => n hp)⟩
instance st_all {α : Sort v} {p : α → Prop} [∀ x, St (p x)] : St (∀ x, p x) :=
  ⟨fun h x => St.elim (fun n => h (fun f => n (f x)))⟩
instance st_and {p q : Prop} [St p] [St q] : St (p ∧ q) :=
  ⟨fun h => ⟨st_use h And.left, st_use h And.right⟩⟩
instance st_iff {p q : Prop} [St p] [St q] : St (p ↔ q) :=
  ⟨fun h => ⟨st_use h Iff.mp, st_use h Iff.mpr⟩⟩

theorem st_cases {q : Prop} [St q] (p : Prop) (h : p → q) (k : ¬p → q) : q :=
  St.elim (fun n => n (k (fun hp => n (h hp))))

theorem nn_congr {p q : Prop} (h : p ↔ q) : (¬¬p) ↔ ¬¬q :=
  ⟨fun k => st_use k (fun hp => nn_in (h.mp hp)),
   fun k => st_use k (fun hq => nn_in (h.mpr hq))⟩

/-- 双条件的逐向组合，避免库中经命题等号运输的版本。 -/
theorem st_iff_congr {p p' q q' : Prop} (h : p ↔ p') (k : q ↔ q') :
    (p ↔ q) ↔ (p' ↔ q') :=
  ⟨fun e => h.symm.trans (e.trans k), fun e => h.trans (e.trans k.symm)⟩

/-- 一个宇宙内的小族，在下一宇宙组成集合树。 -/
inductive V : Type (u+1) where
  | sup (ι : Type u) (f : ι → V) : V

namespace V
def idx : V.{u} → Type u | .sup ι _ => ι
def elem : (a : V.{u}) → a.idx → V.{u} | .sup _ f => f

/-- 每一层的匹配均为稳定存在；不可与普通双模拟混用。 -/
def eq : V.{u} → V.{u} → Prop
  | .sup _ f, .sup _ g =>
      (∀ i, ¬¬∃ j, eq (f i) (g j)) ∧ (∀ j, ¬¬∃ i, eq (f i) (g j))

instance eq_st (a b : V.{u}) : St (eq a b) := by
  cases a; cases b; exact st_and

theorem eq_refl : ∀ a : V.{u}, eq a a
  | .sup _ f => ⟨fun i => nn_in ⟨i, eq_refl (f i)⟩,
                  fun i => nn_in ⟨i, eq_refl (f i)⟩⟩

theorem eq_symm : ∀ {a b : V.{u}}, eq a b → eq b a
  | .sup _ _, .sup _ _, h =>
      ⟨fun j => st_use (h.2 j) (fun ⟨i, e⟩ => nn_in ⟨i, eq_symm e⟩),
       fun i => st_use (h.1 i) (fun ⟨j, e⟩ => nn_in ⟨j, eq_symm e⟩)⟩

theorem eq_trans : ∀ {a b c : V.{u}}, eq a b → eq b c → eq a c
  | .sup _ _, .sup _ _, .sup _ _, h, k =>
      ⟨fun i => st_use (h.1 i) (fun ⟨j, e⟩ =>
        st_use (k.1 j) (fun ⟨l, d⟩ => nn_in ⟨l, eq_trans e d⟩)),
       fun l => st_use (k.2 l) (fun ⟨j, d⟩ =>
        st_use (h.2 j) (fun ⟨i, e⟩ => nn_in ⟨i, eq_trans e d⟩))⟩

def mem (a b : V.{u}) : Prop := ¬¬∃ i, eq a (b.elem i)
instance : Membership V.{u} V.{u} := ⟨fun b a => mem a b⟩
instance mem_st (a b : V.{u}) : St (a ∈ b) := st_not

theorem elem_mem (a : V.{u}) (i : a.idx) : a.elem i ∈ a := nn_in ⟨i, eq_refl _⟩

theorem mem_left {a b c : V.{u}} (e : eq a b) : a ∈ c ↔ b ∈ c :=
  ⟨fun h => st_use h (fun ⟨i, d⟩ => nn_in ⟨i, eq_trans (eq_symm e) d⟩),
   fun h => st_use h (fun ⟨i, d⟩ => nn_in ⟨i, eq_trans e d⟩)⟩

theorem mem_right {a b c : V.{u}} (e : eq b c) : a ∈ b ↔ a ∈ c := by
  cases b with | sup ι f =>
    cases c with | sup κ g =>
      exact ⟨fun h => st_use h (fun ⟨i, d⟩ =>
        st_use (e.1 i) (fun ⟨j, k⟩ => nn_in ⟨j, eq_trans d k⟩)),
        fun h => st_use h (fun ⟨j, d⟩ =>
        st_use (e.2 j) (fun ⟨i, k⟩ => nn_in ⟨i, eq_trans d (eq_symm k)⟩))⟩

theorem ext {a b : V.{u}} (h : ∀ x, x ∈ a ↔ x ∈ b) : eq a b := by
  cases a with | sup ι f =>
    cases b with | sup κ g =>
      exact ⟨fun i => (h (f i)).mp (elem_mem (.sup ι f) i),
        fun j => st_use ((h (g j)).mpr (elem_mem (.sup κ g) j))
          (fun ⟨i, e⟩ => nn_in ⟨i, eq_symm e⟩)⟩

theorem eq_iff (a b : V.{u}) : eq a b ↔ ∀ x, x ∈ a ↔ x ∈ b :=
  ⟨fun e _ => mem_right e, ext⟩

theorem eq_congr {a b c d : V.{u}} (h : eq a c) (k : eq b d) : eq a b ↔ eq c d :=
  ⟨fun e => eq_trans (eq_symm h) (eq_trans e k),
   fun e => eq_trans h (eq_trans e (eq_symm k))⟩

theorem mem_congr {a b c d : V.{u}} (h : eq a c) (k : eq b d) : a ∈ b ↔ c ∈ d :=
  (mem_left h).trans (mem_right k)

/-- 结构归纳运输到全部等价呈现；只消去稳定存在到稳定结论。 -/
theorem mem_ind {p : V.{u} → Prop} [∀ x, St (p x)]
    (h : ∀ x, (∀ y, y ∈ x → p y) → p x) (a : V.{u}) : p a := by
  have k : ∀ b c : V.{u}, eq c b → p c := by
    intro b
    induction b with
    | sup ι f ih =>
      intro c e
      exact h c (fun d hd => st_use ((mem_right e).mp hd)
        (fun ⟨i, di⟩ => ih i d di))
  exact k a a (eq_refl a)

/-- 基础的原经典极小元句子，不附加元层成员可访问性前提。 -/
theorem foundation (a : V.{u}) :
    (¬¬∃ x, x ∈ a) → ¬¬∃ x, x ∈ a ∧ ∀ y, y ∈ a → ¬ y ∈ x := by
  intro h n
  -- 若没有极小成员，成员归纳就逐层排除整个 a 的所有成员。
  have k : ∀ x : V.{u}, ¬ x ∈ a := mem_ind (fun x ih hx =>
    n ⟨x, hx, fun y hy hyx => ih y hyx hy⟩)
  exact h (fun ⟨x, hx⟩ => k x hx)

def empty : V.{u} := .sup PEmpty PEmpty.elim
theorem empty_mem (x : V.{u}) : ¬ x ∈ empty := fun h => h (fun ⟨i, _⟩ => i.elim)

def sep (a : V.{u}) (p : V.{u} → Prop) : V.{u} :=
  .sup {i : a.idx // p (a.elem i)} (fun i => a.elem i.val)

theorem sep_mem (a x : V.{u}) (p : V.{u} → Prop) [∀ x, St (p x)]
    (h : ∀ {x y}, eq x y → p x → p y) :
    x ∈ sep a p ↔ x ∈ a ∧ p x := by
  constructor
  · intro k
    exact st_use k (fun ⟨⟨i, hi⟩, e⟩ => ⟨nn_in ⟨i, e⟩, h (eq_symm e) hi⟩)
  · intro ⟨k, hx⟩
    exact st_use k (fun ⟨i, e⟩ => nn_in ⟨⟨i, h e hx⟩, e⟩)

def sub (a b : V.{u}) : Prop := ∀ x, x ∈ a → x ∈ b
instance sub_st (a b : V.{u}) : St (sub a b) := st_all

/-- 所有指标谓词直接组成小类型；无需枚举子集或选择呈现。 -/
def power (a : V.{u}) : V.{u} :=
  .sup (a.idx → Prop) (fun p => .sup {i : a.idx // p i} (fun i => a.elem i.val))

theorem power_mem (a x : V.{u}) : x ∈ power a ↔ sub x a := by
  constructor
  · intro h y hy
    apply st_use h
    intro ⟨p, e⟩
    exact st_use ((mem_right e).mp hy) (fun ⟨i, d⟩ => nn_in ⟨i.val, d⟩)
  · intro h
    apply nn_in
    -- 把 x 作为 a 的分离子集呈现；保留全部满足条件的指标，无需选代表。
    refine ⟨fun i => a.elem i ∈ x, ext (fun y => ?_)⟩
    change (y ∈ x) ↔ y ∈ sep a (fun z => z ∈ x)
    exact (Iff.intro (fun hy => ⟨h y hy, hy⟩) And.right).trans
      (sep_mem a y (fun z => z ∈ x) (fun e => (mem_left e).mp)).symm

def union (a : V.{u}) : V.{u} :=
  .sup ((i : a.idx) × (a.elem i).idx) (fun i => (a.elem i.1).elem i.2)

theorem union_mem (a x : V.{u}) : x ∈ union a ↔ ¬¬∃ y, y ∈ a ∧ x ∈ y := by
  constructor
  · intro h
    exact st_use h (fun ⟨⟨i, j⟩, e⟩ => nn_in ⟨a.elem i, elem_mem a i, nn_in ⟨j, e⟩⟩)
  · intro h
    apply st_use h
    intro ⟨y, hy, hx⟩
    exact st_use hy (fun ⟨i, e⟩ => st_use ((mem_right e).mp hx)
      (fun ⟨j, d⟩ => nn_in ⟨⟨i, j⟩, d⟩))

def pair (a b : V.{u}) : V.{u} :=
  .sup (ULift Bool) (fun i => match i.down with | false => a | true => b)

theorem pair_mem (a b x : V.{u}) : x ∈ pair a b ↔ ¬¬(eq x a ∨ eq x b) := by
  constructor
  · intro h
    apply st_use h
    intro ⟨⟨i⟩, e⟩
    cases i
    · exact nn_in (Or.inl e)
    · exact nn_in (Or.inr e)
  · intro h
    exact st_use h (fun k => k.elim (fun e => nn_in ⟨⟨false⟩, e⟩)
      (fun e => nn_in ⟨⟨true⟩, e⟩))

def succ (a : V.{u}) : V.{u} :=
  .sup (Sum a.idx PUnit) (fun i => match i with | .inl i => a.elem i | .inr _ => a)

theorem succ_mem (a x : V.{u}) : x ∈ succ a ↔ ¬¬(x ∈ a ∨ eq x a) := by
  constructor
  · intro h
    apply st_use h
    intro ⟨i, e⟩
    cases i with
    | inl i => exact nn_in (Or.inl (nn_in ⟨i, e⟩))
    | inr _ => exact nn_in (Or.inr e)
  · intro h
    apply st_use h
    intro k
    cases k with
    | inl hx => exact st_use hx (fun ⟨i, e⟩ => nn_in ⟨.inl i, e⟩)
    | inr e => exact nn_in ⟨.inr ⟨⟩, e⟩

theorem succ_eq {a b : V.{u}} (e : eq a b) : eq (succ a) (succ b) :=
  ext (fun x => (succ_mem a x).trans ((nn_congr
    ⟨fun h => h.elim (fun hx => Or.inl ((mem_right e).mp hx))
      (fun d => Or.inr (eq_trans d e)),
     fun h => h.elim (fun hx => Or.inl ((mem_right e).mpr hx))
      (fun d => Or.inr (eq_trans d (eq_symm e)))⟩).trans (succ_mem b x).symm))

def nat : Nat → V.{u} | 0 => empty | n+1 => succ (nat n)
def omega : V.{u} := .sup (ULift Nat) (fun i => nat i.down)

theorem omega_zero : empty ∈ omega.{u} := nn_in ⟨⟨0⟩, eq_refl _⟩
theorem omega_succ {a : V.{u}} (h : a ∈ omega) : succ a ∈ omega :=
  st_use h (fun ⟨⟨n⟩, e⟩ => nn_in ⟨⟨n+1⟩, succ_eq e⟩)

theorem nontrivial : ¬ eq empty.{u} (succ empty) := by
  intro h
  exact empty_mem empty ((mem_right h).mpr ((succ_mem _ _).mpr (nn_in (Or.inr (eq_refl _)))))

end V
end YesMetaZFC.Model.Zermelo
