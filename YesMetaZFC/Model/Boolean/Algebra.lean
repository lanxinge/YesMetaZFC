import YesMetaZFC.Model.Boolean.Order

/-! # 布尔代数及其完备扩展

有限逻辑只使用带双重否定律的剩余格；上确界另放在 `CB_alg` 中。
上确界按值域中的谓词取值，因此索引族本身可以处于任意 universe。
-/

namespace YesMetaZFC.Model.Boolean
universe u v

/-- 以偏序、交和剩余运算给出的布尔代数。 -/
structure BA_alg (B : Type u) extends PO_bot B where
  meet : B → B → B
  imp : B → B → B
  le_meet_iff : ∀ a b c, le a (meet b c) ↔ le a b ∧ le a c
  le_imp_iff : ∀ a b c, le a (imp b c) ↔ le (meet a b) c
  double_neg : ∀ a, imp (imp a bot) bot = a

/-- 完备性独立于有限布尔运算。 -/
structure CB_alg (B : Type u) extends BA_alg B, Sup_order B

namespace BA_alg
variable {B : Type u} (𝔹 : BA_alg B)

abbrev top : B := 𝔹.imp 𝔹.bot 𝔹.bot
abbrev neg (a : B) : B := 𝔹.imp a 𝔹.bot
abbrev join (a b : B) : B := 𝔹.neg (𝔹.meet (𝔹.neg a) (𝔹.neg b))
abbrev iff (a b : B) : B := 𝔹.meet (𝔹.imp a b) (𝔹.imp b a)

theorem le_meet {a b c : B} (h : 𝔹.le a b) (k : 𝔹.le a c) : 𝔹.le a (𝔹.meet b c) :=
  (𝔹.le_meet_iff _ _ _).mpr ⟨h, k⟩

theorem meet_le_left (a b : B) : 𝔹.le (𝔹.meet a b) a :=
  ((𝔹.le_meet_iff _ _ _).mp (𝔹.le_refl _)).1

theorem meet_le_right (a b : B) : 𝔹.le (𝔹.meet a b) b :=
  ((𝔹.le_meet_iff _ _ _).mp (𝔹.le_refl _)).2

theorem meet_mono {a b c d : B} (h : 𝔹.le a c) (k : 𝔹.le b d) :
    𝔹.le (𝔹.meet a b) (𝔹.meet c d) :=
  𝔹.le_meet (𝔹.le_trans (𝔹.meet_le_left _ _) h) (𝔹.le_trans (𝔹.meet_le_right _ _) k)

theorem meet_comm (a b : B) : 𝔹.meet a b = 𝔹.meet b a :=
  𝔹.le_antisymm (𝔹.le_meet (𝔹.meet_le_right _ _) (𝔹.meet_le_left _ _))
    (𝔹.le_meet (𝔹.meet_le_right _ _) (𝔹.meet_le_left _ _))

theorem meet_assoc (a b c : B) : 𝔹.meet (𝔹.meet a b) c = 𝔹.meet a (𝔹.meet b c) := by
  apply 𝔹.le_antisymm
  · exact 𝔹.le_meet (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _))
      (𝔹.le_meet (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) (𝔹.meet_le_right _ _))
  · exact 𝔹.le_meet
      (𝔹.le_meet (𝔹.meet_le_left _ _) (𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_left _ _)))
      (𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _))

theorem meet_left_comm (a b c : B) : 𝔹.meet a (𝔹.meet b c) = 𝔹.meet b (𝔹.meet a c) := by
  rw [← 𝔹.meet_assoc, 𝔹.meet_comm a b, 𝔹.meet_assoc]

@[simp] theorem meet_self (a : B) : 𝔹.meet a a = a :=
  𝔹.le_antisymm (𝔹.meet_le_left _ _) (𝔹.le_meet (𝔹.le_refl _) (𝔹.le_refl _))

theorem le_top (a : B) : 𝔹.le a 𝔹.top :=
  (𝔹.le_imp_iff _ _ _).mpr (𝔹.meet_le_right _ _)

theorem top_le_iff (a : B) : 𝔹.le 𝔹.top a ↔ a = 𝔹.top :=
  ⟨fun h => 𝔹.le_antisymm (𝔹.le_top _) h, fun h => h ▸ 𝔹.le_refl _⟩

@[simp] theorem meet_top (a : B) : 𝔹.meet a 𝔹.top = a :=
  𝔹.le_antisymm (𝔹.meet_le_left _ _) (𝔹.le_meet (𝔹.le_refl _) (𝔹.le_top _))

@[simp] theorem top_meet (a : B) : 𝔹.meet 𝔹.top a = a := by rw [𝔹.meet_comm, 𝔹.meet_top]

theorem valid_imp_iff (a b : B) : 𝔹.le 𝔹.top (𝔹.imp a b) ↔ 𝔹.le a b := by
  rw [𝔹.le_imp_iff, 𝔹.top_meet]

theorem valid_iff_iff (a b : B) : 𝔹.le 𝔹.top (𝔹.iff a b) ↔ a = b := by
  rw [iff, 𝔹.le_meet_iff, 𝔹.valid_imp_iff, 𝔹.valid_imp_iff]
  exact ⟨fun h => 𝔹.le_antisymm h.1 h.2, fun h => h ▸ ⟨𝔹.le_refl _, 𝔹.le_refl _⟩⟩

theorem le_imp_neg_iff (c a b : B) :
    𝔹.le c (𝔹.imp a (𝔹.neg b)) ↔ 𝔹.le c (𝔹.imp b (𝔹.neg a)) := by
  rw [𝔹.le_imp_iff, 𝔹.le_imp_iff, 𝔹.le_imp_iff, 𝔹.le_imp_iff,
    𝔹.meet_assoc c a b, 𝔹.meet_comm a b, ← 𝔹.meet_assoc]

@[simp] theorem meet_bot (a : B) : 𝔹.meet a 𝔹.bot = 𝔹.bot :=
  𝔹.le_antisymm (𝔹.meet_le_right _ _) (𝔹.bot_le _)

@[simp] theorem bot_meet (a : B) : 𝔹.meet 𝔹.bot a = 𝔹.bot := by rw [𝔹.meet_comm, 𝔹.meet_bot]

theorem imp_elim (a b : B) : 𝔹.le (𝔹.meet (𝔹.imp a b) a) b :=
  (𝔹.le_imp_iff _ _ _).mp (𝔹.le_refl _)

/-- 在共同布尔条件下应用蕴含。 -/
theorem imp_use {a b c : B} (h : 𝔹.le a (𝔹.imp b c)) (k : 𝔹.le a b) : 𝔹.le a c :=
  𝔹.le_trans (𝔹.le_meet h k) (𝔹.imp_elim _ _)

@[simp] theorem neg_neg (a : B) : 𝔹.neg (𝔹.neg a) = a := 𝔹.double_neg a

theorem neg_antitone {a b : B} (h : 𝔹.le a b) : 𝔹.le (𝔹.neg b) (𝔹.neg a) :=
  (𝔹.le_imp_iff _ _ _).mpr
    (𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) h) (𝔹.imp_elim _ _))

theorem neg_le_neg_iff (a b : B) : 𝔹.le (𝔹.neg a) (𝔹.neg b) ↔ 𝔹.le b a := by
  constructor
  · intro h; simpa only [𝔹.neg_neg] using 𝔹.neg_antitone h
  · exact 𝔹.neg_antitone

theorem neg_le_iff (a b : B) : 𝔹.le (𝔹.neg a) b ↔ 𝔹.le (𝔹.neg b) a := by
  simpa only [𝔹.neg_neg] using 𝔹.neg_le_neg_iff a (𝔹.neg b)

theorem le_iff_meet_neg (a b : B) : 𝔹.le a b ↔ 𝔹.le (𝔹.meet a (𝔹.neg b)) 𝔹.bot := by
  simpa only [𝔹.double_neg] using 𝔹.le_imp_iff a (𝔹.neg b) 𝔹.bot

@[simp] theorem meet_neg (a : B) : 𝔹.meet a (𝔹.neg a) = 𝔹.bot :=
  𝔹.le_antisymm ((𝔹.le_iff_meet_neg a a).mp (𝔹.le_refl a)) (𝔹.bot_le _)

theorem meet_eq_bot_of_bounds {a b c : B} (h : 𝔹.le a c) (k : 𝔹.le b (𝔹.neg c)) :
    𝔹.meet a b = 𝔹.bot := by
  apply 𝔹.le_antisymm _ (𝔹.bot_le _)
  simpa only [𝔹.meet_neg] using 𝔹.meet_mono h k

theorem join_le_iff (a b c : B) : 𝔹.le (𝔹.join a b) c ↔ 𝔹.le a c ∧ 𝔹.le b c := by
  rw [join, 𝔹.neg_le_iff, 𝔹.le_meet_iff, 𝔹.neg_le_neg_iff, 𝔹.neg_le_neg_iff]

theorem le_join_left (a b : B) : 𝔹.le a (𝔹.join a b) :=
  ((𝔹.join_le_iff _ _ _).mp (𝔹.le_refl _)).1

theorem le_join_right (a b : B) : 𝔹.le b (𝔹.join a b) :=
  ((𝔹.join_le_iff _ _ _).mp (𝔹.le_refl _)).2

@[simp] theorem join_neg (a : B) : 𝔹.join a (𝔹.neg a) = 𝔹.top := by
  rw [join, 𝔹.neg_neg, 𝔹.meet_comm, 𝔹.meet_neg]

theorem meet_join_le {c a b d : B} (h : 𝔹.le (𝔹.meet c a) d) (k : 𝔹.le (𝔹.meet c b) d) :
    𝔹.le (𝔹.meet c (𝔹.join a b)) d := by
  rw [𝔹.meet_comm, ← 𝔹.le_imp_iff, 𝔹.join_le_iff]
  constructor
  · apply (𝔹.le_imp_iff _ _ _).mpr; rwa [𝔹.meet_comm]
  · apply (𝔹.le_imp_iff _ _ _).mpr; rwa [𝔹.meet_comm]

theorem case_use {c a b : B} (h : 𝔹.le (𝔹.meet c a) b) (k : 𝔹.le (𝔹.meet c (𝔹.neg a)) b) :
    𝔹.le c b := by
  simpa only [𝔹.join_neg, 𝔹.meet_top] using 𝔹.meet_join_le h k

end BA_alg

namespace CB_alg
variable {B : Type u} (𝔹 : CB_alg B)

theorem meet_iSup {ι : Sort v} (b : B) (f : ι → B) :
    𝔹.meet b (𝔹.iSup f) = 𝔹.iSup (fun i => 𝔹.meet b (f i)) := by
  apply 𝔹.le_antisymm
  · rw [𝔹.meet_comm, ← 𝔹.le_imp_iff, 𝔹.iSup_le_iff]
    intro i
    rw [𝔹.le_imp_iff, 𝔹.meet_comm]
    exact 𝔹.le_iSup (fun j => 𝔹.meet b (f j)) i
  · exact (𝔹.iSup_le_iff _ _).mpr (fun i => 𝔹.meet_mono (𝔹.le_refl _) (𝔹.le_iSup f i))

end CB_alg

/-- 默认二值代数的实际完备实例；运算直接构造命题，经典性只用于双重否定律的证明。 -/
def prop_algebra : CB_alg Prop where
  toSup_order := prop_order
  meet := And
  imp p q := p → q
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩,
    fun ⟨h, k⟩ hp => ⟨h hp, k hp⟩⟩
  le_imp_iff _ _ _ := ⟨fun h ⟨hp, hq⟩ => h hp hq, fun h hp hq => h ⟨hp, hq⟩⟩
  double_neg _ := propext Classical.not_not

end YesMetaZFC.Model.Boolean
