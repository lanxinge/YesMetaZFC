import YesMetaZFC.Model.Boolean.Algebra

/-! # 布尔代数上的滤子和理想

基本运算显式给出。极大性与二择性质的等价只在命题证明中使用排中律；
这里不选取极大滤子，不使用选择来产生数据。
-/

namespace YesMetaZFC.Model.Boolean
universe u

structure Filter_l {B : Type u} (𝔹 : BA_alg B) where
  mem : B → Prop
  top_mem : mem 𝔹.top
  upward : ∀ {a b}, mem a → 𝔹.le a b → mem b
  meet_mem : ∀ {a b}, mem a → mem b → mem (𝔹.meet a b)

structure Ideal_l {B : Type u} (𝔹 : BA_alg B) where
  mem : B → Prop
  bot_mem : mem 𝔹.bot
  downward : ∀ {a b}, mem b → 𝔹.le a b → mem a
  join_mem : ∀ {a b}, mem a → mem b → mem (𝔹.join a b)

namespace Filter_l
variable {B : Type u} {𝔹 : BA_alg B}

def Proper_l (F : Filter_l 𝔹) : Prop := ¬ F.mem 𝔹.bot
def Extends_l (F G : Filter_l 𝔹) : Prop := ∀ a, F.mem a → G.mem a
def Maximal_l (F : Filter_l 𝔹) : Prop :=
  F.Proper_l ∧ ∀ G, F.Extends_l G → G.Proper_l → G.Extends_l F

theorem ext_l {F G : Filter_l 𝔹} (h : ∀ a, F.mem a ↔ G.mem a) : F = G := by
  cases F; cases G
  congr
  exact funext (fun a => propext (h a))

def principal_l (a : B) : Filter_l 𝔹 where
  mem b := 𝔹.le a b
  top_mem := 𝔹.le_top a
  upward h k := 𝔹.le_trans h k
  meet_mem := 𝔹.le_meet

theorem principal_proper_l (a : B) :
    (principal_l (𝔹 := 𝔹) a).Proper_l ↔ a ≠ 𝔹.bot :=
  ⟨fun h k => h (k ▸ 𝔹.le_refl _), fun h k => h (𝔹.le_antisymm k (𝔹.bot_le _))⟩

/-- 所有包含生成集的滤子的交；不要求生成集可枚举。 -/
def generated_l (S : B → Prop) : Filter_l 𝔹 where
  mem a := ∀ F : Filter_l 𝔹, (∀ b, S b → F.mem b) → F.mem a
  top_mem F _ := F.top_mem
  upward h k F hF := F.upward (h F hF) k
  meet_mem h k F hF := F.meet_mem (h F hF) (k F hF)

theorem mem_generated_l {S : B → Prop} {a : B} (h : S a) :
    (generated_l (𝔹 := 𝔹) S).mem a := fun _ k => k a h

theorem generated_le_l {S : B → Prop} (F : Filter_l 𝔹)
    (h : ∀ a, S a → F.mem a) : (generated_l S).Extends_l F := fun _ k => k F h

/-- 添入一个元素后的显式滤子；用于不依赖选择的极大性论证。 -/
def adjoin_l (F : Filter_l 𝔹) (a : B) : Filter_l 𝔹 where
  mem b := ∃ c, F.mem c ∧ 𝔹.le (𝔹.meet c a) b
  top_mem := ⟨𝔹.top, F.top_mem, 𝔹.le_top _⟩
  upward := fun ⟨c, hc, h⟩ k => ⟨c, hc, 𝔹.le_trans h k⟩
  meet_mem := by
    rintro b c ⟨d, hd, h⟩ ⟨e, he, k⟩
    exact ⟨𝔹.meet d e, F.meet_mem hd he, 𝔹.le_meet
      (𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_left _ _) (𝔹.le_refl _)) h)
      (𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_right _ _) (𝔹.le_refl _)) k)⟩

theorem le_adjoin_l (F : Filter_l 𝔹) (a : B) : F.Extends_l (F.adjoin_l a) :=
  fun b hb => ⟨b, hb, 𝔹.meet_le_left _ _⟩

theorem mem_adjoin_l (F : Filter_l 𝔹) (a : B) : (F.adjoin_l a).mem a :=
  ⟨𝔹.top, F.top_mem, 𝔹.meet_le_right _ _⟩

theorem adjoin_proper_l (F : Filter_l 𝔹) (a : B) :
    (F.adjoin_l a).Proper_l ↔ ¬ F.mem (𝔹.neg a) := by
  constructor
  · intro h k
    exact h ⟨𝔹.neg a, k, 𝔹.imp_elim _ _⟩
  · rintro h ⟨b, hb, k⟩
    exact h (F.upward hb ((𝔹.le_imp_iff _ _ _).mpr k))

theorem not_neg_l (F : Filter_l 𝔹) (h : F.Proper_l) {a : B}
    (k : F.mem a) : ¬ F.mem (𝔹.neg a) := by
  intro ha
  have hb := F.meet_mem k ha
  rw [𝔹.meet_neg] at hb
  exact h hb

theorem maximal_iff_l (F : Filter_l 𝔹) :
    F.Maximal_l ↔ F.Proper_l ∧ ∀ a, F.mem a ∨ F.mem (𝔹.neg a) := by
  constructor
  · rintro ⟨h, k⟩
    refine ⟨h, fun a => ?_⟩
    rcases Classical.em (F.mem (𝔹.neg a)) with ha | ha
    · exact Or.inr ha
    · exact Or.inl (k (F.adjoin_l a) (F.le_adjoin_l a)
        ((F.adjoin_proper_l a).mpr ha) a (F.mem_adjoin_l a))
  · rintro ⟨h, k⟩
    refine ⟨h, fun G hG h₁ a ha => ?_⟩
    rcases k a with h₂ | h₂
    · exact h₂
    · exact False.elim (G.not_neg_l h₁ ha (hG _ h₂))

def dual_l (F : Filter_l 𝔹) : Ideal_l 𝔹 where
  mem a := F.mem (𝔹.neg a)
  bot_mem := F.top_mem
  downward h k := F.upward h (𝔹.neg_antitone k)
  join_mem h k := by
    have ha := F.meet_mem h k
    simpa only [BA_alg.join, 𝔹.neg_neg] using ha

end Filter_l

namespace Ideal_l
variable {B : Type u} {𝔹 : BA_alg B}

def Proper_l (I : Ideal_l 𝔹) : Prop := ¬ I.mem 𝔹.top
def Prime_l (I : Ideal_l 𝔹) : Prop :=
  I.Proper_l ∧ ∀ a b, I.mem (𝔹.meet a b) → I.mem a ∨ I.mem b

def dual_l (I : Ideal_l 𝔹) : Filter_l 𝔹 where
  mem a := I.mem (𝔹.neg a)
  top_mem := by
    change I.mem (𝔹.neg (𝔹.neg 𝔹.bot))
    rw [𝔹.neg_neg]
    exact I.bot_mem
  upward h k := I.downward h (𝔹.neg_antitone k)
  meet_mem h k := by
    have ha := I.join_mem h k
    simpa only [BA_alg.join, 𝔹.neg_neg] using ha

theorem dual_proper_l (I : Ideal_l 𝔹) : I.dual_l.Proper_l ↔ I.Proper_l := Iff.rfl

theorem prime_iff_l (I : Ideal_l 𝔹) : I.Prime_l ↔ I.dual_l.Maximal_l := by
  rw [Filter_l.maximal_iff_l]
  constructor
  · rintro ⟨h, k⟩
    refine ⟨h, fun a => ?_⟩
    have ha := k a (𝔹.neg a) (by rw [𝔹.meet_neg]; exact I.bot_mem)
    rcases ha with ha | ha
    · exact Or.inr (by simpa only [dual_l, 𝔹.neg_neg] using ha)
    · exact Or.inl ha
  · rintro ⟨h, k⟩
    refine ⟨h, fun a b hab => ?_⟩
    rcases k a with ha | ha
    · right
      have h₁ := I.join_mem hab ha
      apply I.downward h₁
      apply 𝔹.case_use (a := a)
      · rw [𝔹.meet_comm]
        exact 𝔹.le_join_left _ _
      · exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.le_join_right _ _)
    · exact Or.inl (by simpa only [dual_l, 𝔹.neg_neg] using ha)

end Ideal_l
end YesMetaZFC.Model.Boolean
