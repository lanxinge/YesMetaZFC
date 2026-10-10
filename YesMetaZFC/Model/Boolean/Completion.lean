import YesMetaZFC.Model.Boolean.Filter

/-! # 布尔代数的 MacNeille 完备化

切割是对“全部上界的下界”封闭的子集。上确界取并的切割闭包，剩余运算
逐点定义；不使用超滤子、佐恩引理或代表元选择。此模块是代数层，内部集合
的存在性另须由对象理论的幂集和分离证明，不能把外部谓词域当作内部幂集。
-/

namespace YesMetaZFC.Model.Boolean
universe u

namespace BA_alg
variable {B : Type u} (𝔹 : BA_alg B)

/-- 下上切割闭包。 -/
def cut_l (S : B → Prop) (a : B) : Prop :=
  ∀ b, (∀ c, S c → 𝔹.le c b) → 𝔹.le a b

theorem subset_cut_l {S : B → Prop} {a : B} (h : S a) : 𝔹.cut_l S a :=
  fun _ k => k a h

theorem cut_mono_l {S T : B → Prop} (h : ∀ a, S a → T a) :
    ∀ a, 𝔹.cut_l S a → 𝔹.cut_l T a :=
  fun _ k b hb => k b (fun c hc => hb c (h c hc))

/-- 完备化的元素，不选择任何集合或商的代表元。 -/
structure Cut_l where
  mem : B → Prop
  closed : ∀ a, 𝔹.cut_l mem a → mem a

namespace Cut_l
variable {𝔹} (I J K : 𝔹.Cut_l)

theorem ext_l (h : ∀ a, I.mem a ↔ J.mem a) : I = J := by
  cases I; cases J
  congr
  exact funext (fun a => propext (h a))

theorem lower_l {a b : B} (h : 𝔹.le a b) (k : I.mem b) : I.mem a :=
  I.closed a (fun _ hc => 𝔹.le_trans h (hc b k))

theorem bot_mem_l : I.mem 𝔹.bot := I.closed _ (fun b _ => 𝔹.bot_le b)

/-- 切割同时是理想；完备化并非把所有理想误称为布尔代数。 -/
def ideal_l : Ideal_l 𝔹 where
  mem := I.mem
  bot_mem := I.bot_mem_l
  downward h k := I.lower_l k h
  join_mem := fun h k => I.closed _ (fun c hc =>
    (𝔹.join_le_iff _ _ c).mpr ⟨hc _ h, hc _ k⟩)

def principal_l (a : B) : 𝔹.Cut_l where
  mem b := 𝔹.le b a
  closed _ h := h a (fun _ k => k)

def closure_l (S : B → Prop) : 𝔹.Cut_l where
  mem := 𝔹.cut_l S
  closed _ h b hb := h b (fun _ k => k b hb)

def meet_l : 𝔹.Cut_l where
  mem a := I.mem a ∧ J.mem a
  closed a h := ⟨I.closed a (𝔹.cut_mono_l (fun _ k => k.1) a h),
    J.closed a (𝔹.cut_mono_l (fun _ k => k.2) a h)⟩

def imp_l : 𝔹.Cut_l where
  mem a := ∀ b, I.mem b → J.mem (𝔹.meet a b)
  closed a h b hb := J.closed _ (fun c hc =>
    (𝔹.le_imp_iff a b c).mp (h (𝔹.imp b c) (fun d hd =>
      (𝔹.le_imp_iff d b c).mpr (hc _ (hd b hb)))))

theorem residuation_l :
    (∀ a, I.mem a → (imp_l J K).mem a) ↔
      ∀ a, (meet_l I J).mem a → K.mem a := by
  constructor
  · intro h a ha
    have h₁ := h a ha.1 a ha.2
    simpa only [𝔹.meet_self] using h₁
  · intro h a ha b hb
    exact h _ ⟨I.lower_l (𝔹.meet_le_left _ _) ha,
      J.lower_l (𝔹.meet_le_right _ _) hb⟩

theorem double_neg_l :
    imp_l (imp_l I (principal_l 𝔹.bot)) (principal_l 𝔹.bot) = I := by
  apply ext_l
  intro a
  constructor
  · intro h
    apply I.closed
    intro b hb
    apply (𝔹.le_iff_meet_neg a b).mpr
    exact h (𝔹.neg b) (fun c hc => by
      rw [𝔹.meet_comm]
      exact 𝔹.le_trans (𝔹.meet_mono (hb c hc) (𝔹.le_refl _))
        (by rw [𝔹.meet_neg]; exact 𝔹.le_refl _))
  · intro h b hb
    have h₁ := hb a h
    rwa [𝔹.meet_comm] at h₁

/-- 完备布尔代数的实际运算与全部律。 -/
def algebra_l : CB_alg 𝔹.Cut_l where
  le I J := ∀ a, I.mem a → J.mem a
  bot := principal_l 𝔹.bot
  le_refl _ _ := id
  le_trans h k a ha := k a (h a ha)
  le_antisymm h k := ext_l _ _ (fun a => ⟨h a, k a⟩)
  bot_le I _ h := I.lower_l h I.bot_mem_l
  meet := meet_l
  imp := imp_l
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun a ha => (h a ha).1,
    fun a ha => (h a ha).2⟩, fun ⟨h, k⟩ a ha => ⟨h a ha, k a ha⟩⟩
  le_imp_iff := residuation_l
  double_neg := double_neg_l
  sup S := closure_l (fun a => ∃ I, S I ∧ I.mem a)
  sup_le_iff S I := by
    constructor
    · intro h J hJ a ha
      exact h a (𝔹.subset_cut_l ⟨J, hJ, ha⟩)
    · intro h a ha
      exact I.closed a (𝔹.cut_mono_l (fun b ⟨J, hJ, hb⟩ => h J hJ b hb) a ha)

theorem principal_order_l (a b : B) :
    (algebra_l (𝔹 := 𝔹)).le (principal_l a) (principal_l b) ↔ 𝔹.le a b :=
  ⟨fun h => h a (𝔹.le_refl a), fun h _ k => 𝔹.le_trans k h⟩

theorem principal_injective_l {a b : B}
    (h : principal_l (𝔹 := 𝔹) a = principal_l b) : a = b := by
  apply 𝔹.le_antisymm
  · exact (principal_order_l a b).mp (h ▸ (algebra_l (𝔹 := 𝔹)).le_refl _)
  · exact (principal_order_l b a).mp (h ▸ (algebra_l (𝔹 := 𝔹)).le_refl _)

theorem principal_meet_l (a b : B) :
    principal_l (𝔹 := 𝔹) (𝔹.meet a b) = meet_l (principal_l a) (principal_l b) :=
  ext_l _ _ (fun c => 𝔹.le_meet_iff c a b)

theorem principal_imp_l (a b : B) :
    principal_l (𝔹 := 𝔹) (𝔹.imp a b) = imp_l (principal_l a) (principal_l b) := by
  apply ext_l
  intro c
  constructor
  · intro h d hd
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) hd) ((𝔹.le_imp_iff _ _ _).mp h)
  · intro h
    exact (𝔹.le_imp_iff _ _ _).mpr (h a (𝔹.le_refl a))

theorem principal_neg_l (a : B) :
    principal_l (𝔹 := 𝔹) (𝔹.neg a) = (algebra_l (𝔹 := 𝔹)).neg (principal_l a) :=
  principal_imp_l a 𝔹.bot

theorem principal_join_l (a b : B) :
    principal_l (𝔹 := 𝔹) (𝔹.join a b) =
      (algebra_l (𝔹 := 𝔹)).join (principal_l a) (principal_l b) := by
  change principal_l (𝔹.neg (𝔹.meet (𝔹.neg a) (𝔹.neg b))) = _
  rw [principal_neg_l, principal_meet_l, principal_neg_l, principal_neg_l]
  rfl

/-- 原代数中已经存在的上确界在完备化中保持。 -/
theorem principal_sup_l (S : B → Prop) (a : B)
    (h : ∀ b, 𝔹.le a b ↔ ∀ c, S c → 𝔹.le c b) :
    closure_l (𝔹 := 𝔹) S = principal_l a := by
  apply ext_l
  intro b
  exact ⟨fun k => k a ((h a).mp (𝔹.le_refl a)),
    fun k c hc => 𝔹.le_trans k ((h c).mpr hc)⟩

/-- 每个切割都是其中主切割的上确界，给出完备化的稠密性。 -/
theorem dense_sup_l :
    (algebra_l (𝔹 := 𝔹)).sup (fun J => ∃ a, I.mem a ∧ J = principal_l a) = I := by
  apply ext_l
  intro a
  constructor
  · intro h
    apply I.closed a
    apply 𝔹.cut_mono_l _ a h
    rintro b ⟨J, ⟨c, hc, rfl⟩, hb⟩
    exact I.lower_l hb hc
  · intro h
    exact 𝔹.subset_cut_l ⟨principal_l a, ⟨a, h, rfl⟩, 𝔹.le_refl a⟩

end Cut_l
end BA_alg
end YesMetaZFC.Model.Boolean
