import Init.Classical

/-! # 上确界与链完备偏序

序论接口不要求布尔运算；链上的不动点论证只消费链完备性。
命题偏序给出实际实例，任意上确界均通过值域谓词在原 universe 中形成。
-/

namespace YesMetaZFC.Model.Boolean
universe u v w

structure PO_bot (B : Type u) where
  le : B → B → Prop
  bot : B
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  bot_le : ∀ a, le bot a

def PO_bot.Chain {B : Type u} (𝔹 : PO_bot B) (p : B → Prop) : Prop :=
  ∀ a b, p a → p b → 𝔹.le a b ∨ 𝔹.le b a

/-- 每条链都有上确界；不假定任意集合已有上确界。 -/
structure CS_order (B : Type u) extends PO_bot B where
  sup : (p : B → Prop) → toPO_bot.Chain p → B
  le_sup : ∀ p h b, p b → le b (sup p h)
  sup_le : ∀ p h b, (∀ c, p c → le c b) → le (sup p h) b

structure Sup_order (B : Type u) extends PO_bot B where
  sup : (B → Prop) → B
  sup_le_iff : ∀ p a, le (sup p) a ↔ ∀ b, p b → le b a

namespace Sup_order
variable {B : Type u} (𝔹 : Sup_order B)

def toCS : CS_order B where
  toPO_bot := 𝔹.toPO_bot
  sup p _ := 𝔹.sup p
  le_sup _ _ b h := (𝔹.sup_le_iff _ _).mp (𝔹.le_refl _) b h
  sup_le p _ b h := (𝔹.sup_le_iff p b).mpr h

/-- 通过值域谓词取上确界，不提升值的 universe。 -/
def iSup {ι : Sort v} (f : ι → B) : B := 𝔹.sup (fun b => ∃ i, f i = b)
def iInf {ι : Sort v} (f : ι → B) : B := 𝔹.sup (fun b => ∀ i, 𝔹.le b (f i))

theorem le_sup {p : B → Prop} {b : B} (h : p b) : 𝔹.le b (𝔹.sup p) :=
  (𝔹.sup_le_iff _ _).mp (𝔹.le_refl _) _ h

theorem iSup_le_iff {ι : Sort v} (f : ι → B) (b : B) :
    𝔹.le (𝔹.iSup f) b ↔ ∀ i, 𝔹.le (f i) b := by
  rw [iSup, 𝔹.sup_le_iff]
  exact ⟨fun h i => h (f i) ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

theorem le_iSup {ι : Sort v} (f : ι → B) (i : ι) : 𝔹.le (f i) (𝔹.iSup f) :=
  𝔹.le_sup (p := fun b => ∃ j, f j = b) (b := f i) ⟨i, rfl⟩

theorem iInf_le {ι : Sort v} (f : ι → B) (i : ι) : 𝔹.le (𝔹.iInf f) (f i) :=
  (𝔹.sup_le_iff _ _).mpr (fun _ h => h i)

theorem le_iInf_iff {ι : Sort v} (f : ι → B) (b : B) :
    𝔹.le b (𝔹.iInf f) ↔ ∀ i, 𝔹.le b (f i) :=
  ⟨fun h i => 𝔹.le_trans h (𝔹.iInf_le f i), fun h => 𝔹.le_sup h⟩

theorem iSup_proof {p : Prop} (h : p) (f : p → B) : 𝔹.iSup f = f h :=
  𝔹.le_antisymm ((𝔹.iSup_le_iff _ _).mpr (fun _ => 𝔹.le_refl _)) (𝔹.le_iSup f h)

theorem iSup_sigma {ι : Type v} {κ : ι → Type w} (f : (i : ι) → κ i → B) :
    𝔹.iSup (fun a : Σ i, κ i => f a.1 a.2) = 𝔹.iSup (fun i => 𝔹.iSup (f i)) := by
  apply 𝔹.le_antisymm
  · exact (𝔹.iSup_le_iff _ _).mpr (fun a => 𝔹.le_trans (𝔹.le_iSup (f a.1) a.2)
      (𝔹.le_iSup (fun i => 𝔹.iSup (f i)) a.1))
  · exact (𝔹.iSup_le_iff _ _).mpr (fun i => (𝔹.iSup_le_iff _ _).mpr
      (fun j => 𝔹.le_iSup (fun a : Σ i, κ i => f a.1 a.2) ⟨i, j⟩))

/-- 函数偏序逐点取上确界，索引与值都保持原 universe。 -/
def pi (ι : Type v) : Sup_order (ι → B) where
  le f g := ∀ i, 𝔹.le (f i) (g i)
  bot _ := 𝔹.bot
  le_refl _ _ := 𝔹.le_refl _
  le_trans h k i := 𝔹.le_trans (h i) (k i)
  le_antisymm h k := funext (fun i => 𝔹.le_antisymm (h i) (k i))
  bot_le _ _ := 𝔹.bot_le _
  sup p i := 𝔹.iSup (fun f : {f // p f} => f.1 i)
  sup_le_iff p _ := ⟨fun h f hf i =>
    𝔹.le_trans (𝔹.le_iSup (fun g : {g // p g} => g.1 i) ⟨f, hf⟩) (h i),
    fun h i => (𝔹.iSup_le_iff _ _).mpr (fun f => h f.1 f.2 i)⟩

end Sup_order

/-- 任意命题族的上确界由存在量词直接给出。 -/
def prop_order : Sup_order Prop where
  le p q := p → q
  bot := False
  le_refl _ := id
  le_trans h k := k ∘ h
  le_antisymm h k := propext ⟨h, k⟩
  bot_le _ := False.elim
  sup p := ∃ q, p q ∧ q
  sup_le_iff _ _ := ⟨fun h q hq hq' => h ⟨q, hq, hq'⟩,
    fun h ⟨q, hq, hq'⟩ => h q hq hq'⟩

end YesMetaZFC.Model.Boolean
