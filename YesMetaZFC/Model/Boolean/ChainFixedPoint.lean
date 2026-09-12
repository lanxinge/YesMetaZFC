import YesMetaZFC.Model.Boolean.Order

/-! # 链完备偏序中的递增不动点

从底元开始，对递增函数和链上确界闭包。先证明每个生成点的严格前驱在一步后仍不越过
该点，再证明所有生成点成链，最后取这条链的上确界。无需先构造序数或假定 Zorn 引理。
-/

namespace YesMetaZFC.Model.Boolean
universe u
variable {B : Type u}

/-- 底元、一步扩张及链极限所生成的最小闭包。 -/
inductive FP_stage (R : CS_order B) (f : B → B) : B → Prop where
  | bot : FP_stage R f R.bot
  | step {a} : FP_stage R f a → FP_stage R f (f a)
  | sup (p : B → Prop) (hp : ∀ a, p a → FP_stage R f a) (hc : R.Chain p) :
      FP_stage R f (R.sup p hc)

def FP_extreme (R : CS_order B) (f : B → B) (a : B) : Prop :=
  ∀ b, FP_stage R f b → R.le b a → b ≠ a → R.le (f b) a

namespace CS_order
variable (R : CS_order B) (f : B → B) (hf : ∀ a, R.le a (f a))
include hf

/-- 极端点和它的一步像之间不存在其他生成点。 -/
theorem stage_gap {a b : B} (ha : FP_extreme R f a) (hb : FP_stage R f b) :
    R.le b a ∨ R.le (f a) b := by
  classical
  induction hb with
  | bot => exact Or.inl (R.bot_le a)
  | @step b hb ih =>
      rcases ih with h | h
      · by_cases k : b = a
        · exact Or.inr (k ▸ R.le_refl _)
        · exact Or.inl (ha b hb h k)
      · exact Or.inr (R.le_trans h (hf b))
  | sup p hp hc ih =>
      by_cases h : ∃ b, p b ∧ R.le (f a) b
      · obtain ⟨b, hb, hab⟩ := h
        exact Or.inr (R.le_trans hab (R.le_sup p hc b hb))
      · apply Or.inl
        apply R.sup_le p hc a
        intro b hb
        rcases ih b hb with k | k
        · exact k
        · exact False.elim (h ⟨b, hb, k⟩)

/-- 每个生成点的严格前驱在下一步仍落在该点之下。 -/
theorem stage_extreme {a : B} (ha : FP_stage R f a) : FP_extreme R f a := by
  classical
  induction ha with
  | bot =>
      intro b _ hb hne
      exact False.elim (hne (R.le_antisymm hb (R.bot_le b)))
  | @step a ha ih =>
      intro b hb hba hne
      rcases R.stage_gap f hf ih hb with h | h
      · by_cases k : b = a
        · exact k ▸ R.le_refl _
        · exact R.le_trans (ih b hb h k) (hf a)
      · exact False.elim (hne (R.le_antisymm hba h))
  | sup p hp hc ih =>
      intro b hb hba hne
      by_cases h : ∀ a, p a → R.le a b
      · exact False.elim (hne (R.le_antisymm hba (R.sup_le p hc b h)))
      · have hex : ∃ a, p a ∧ ¬ R.le a b := by
          apply Classical.byContradiction
          intro k
          apply h
          intro a ha
          apply Classical.byContradiction
          exact fun hn => k ⟨a, ha, hn⟩
        obtain ⟨a, ha, hna⟩ := hex
        have hba' : R.le b a := by
          rcases R.stage_gap f hf (ih a ha) hb with k | k
          · exact k
          · exact False.elim (hna (R.le_trans (hf a) k))
        have hne' : b ≠ a := by
          intro k
          apply hna
          rw [k]
          exact R.le_refl _
        exact R.le_trans (ih a ha b hb hba' hne') (R.le_sup p hc a ha)

theorem stage_chain : R.Chain (FP_stage R f) := by
  intro a b ha hb
  rcases R.stage_gap f hf (R.stage_extreme f hf ha) hb with h | h
  · exact Or.inr h
  · exact Or.inl (R.le_trans (hf a) h)

/-- 生成链的最大元是实际不动点；保留生成性供后续不交细化归纳。 -/
theorem stage_max : ∃ a, FP_stage R f a ∧ f a = a ∧ ∀ b, FP_stage R f b → R.le b a := by
  let p := FP_stage R f
  let hc := R.stage_chain f hf
  let a := R.sup p hc
  have ha : FP_stage R f a := .sup p (fun _ h => h) hc
  exact ⟨a, ha, R.le_antisymm (R.le_sup p hc (f a) (.step ha)) (hf a),
    fun b hb => R.le_sup p hc b hb⟩

end CS_order
end YesMetaZFC.Model.Boolean
