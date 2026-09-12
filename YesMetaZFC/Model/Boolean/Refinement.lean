import YesMetaZFC.Model.Boolean.Algebra
import YesMetaZFC.Model.Boolean.ChainFixedPoint

/-! # 完备布尔代数中的不交细化

对尚未覆盖的布尔部分选一个非零增量，以链不动点取到完整覆盖。
生成链的各个增量两两不交；选择只出现在存在性证明内部。
-/

namespace YesMetaZFC.Model.Boolean
universe u
namespace CB_alg
variable {B : Type u} (𝔹 : CB_alg B)

/-- 任意布尔族都有保持上确界的不交细化，指标仍是原布尔值域的子集。 -/
theorem disjoint_refinement (p : B → Prop) :
    ∃ q : B → Prop,
      (∀ b, q b → b ≠ 𝔹.bot ∧ ∃ c, p c ∧ 𝔹.le b c) ∧
      (∀ b c, q b → q c → b ≠ c → 𝔹.meet b c = 𝔹.bot) ∧
      𝔹.sup q = 𝔹.sup p := by
  classical
  have step (b : B) : ∃ c, 𝔹.le c (𝔹.neg b) ∧
      (c = 𝔹.bot ∨ ∃ d, p d ∧ 𝔹.le c d) ∧ (c = 𝔹.bot → 𝔹.le (𝔹.sup p) b) := by
    by_cases h : 𝔹.le (𝔹.sup p) b
    · exact ⟨𝔹.bot, 𝔹.bot_le _, Or.inl rfl, fun _ => h⟩
    · have hex : ∃ d, p d ∧ ¬ 𝔹.le d b := by
        apply Classical.byContradiction
        intro k
        apply h
        apply (𝔹.sup_le_iff p b).mpr
        intro d hd
        apply Classical.byContradiction
        exact fun hn => k ⟨d, hd, hn⟩
      obtain ⟨d, hd, hn⟩ := hex
      refine ⟨𝔹.meet d (𝔹.neg b), 𝔹.meet_le_right _ _,
        Or.inr ⟨d, hd, 𝔹.meet_le_left _ _⟩, fun hz => ?_⟩
      apply False.elim
      apply hn
      apply (𝔹.le_iff_meet_neg d b).mpr
      rw [hz]
      exact 𝔹.le_refl _
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice step
  let R := 𝔹.toCS
  let f (b : B) := 𝔹.join b (g b)
  have hf (b : B) : R.le b (f b) := 𝔹.le_join_left _ _
  let q (c : B) := c ≠ 𝔹.bot ∧ ∃ b, FP_stage R f b ∧ c = g b
  have hq (c : B) (hc : q c) : c ≠ 𝔹.bot ∧ ∃ d, p d ∧ 𝔹.le c d := by
    obtain ⟨hne, b, _, rfl⟩ := hc
    rcases (hg b).2.1 with h | h
    · exact False.elim (hne h)
    · exact ⟨hne, h⟩
  refine ⟨q, hq, ?_, ?_⟩
  · intro c d hc hd hne
    obtain ⟨_, b, hb, rfl⟩ := hc
    obtain ⟨_, a, ha, rfl⟩ := hd
    have hba : b ≠ a := fun h => hne (congrArg g h)
    rcases R.stage_chain f hf b a hb ha with h | h
    · exact 𝔹.meet_eq_bot_of_bounds
        (𝔹.le_trans (𝔹.le_join_right _ _) (R.stage_extreme f hf ha b hb h hba)) (hg a).1
    · rw [𝔹.meet_comm]
      exact 𝔹.meet_eq_bot_of_bounds
        (𝔹.le_trans (𝔹.le_join_right _ _) (R.stage_extreme f hf hb a ha h (Ne.symm hba))) (hg b).1
  · apply 𝔹.le_antisymm
    · apply (𝔹.sup_le_iff _ _).mpr
      intro c hc
      obtain ⟨d, hd, hcd⟩ := (hq c hc).2
      exact 𝔹.le_trans hcd (𝔹.le_sup hd)
    · have hgq (b : B) (hb : FP_stage R f b) : 𝔹.le (g b) (𝔹.sup q) := by
        by_cases h : g b = 𝔹.bot
        · rw [h]; exact 𝔹.bot_le _
        · exact 𝔹.le_sup ⟨h, b, hb, rfl⟩
      have hstage (b : B) (hb : FP_stage R f b) : 𝔹.le b (𝔹.sup q) := by
        induction hb with
        | bot => exact 𝔹.bot_le _
        | @step b hb ih => exact (𝔹.join_le_iff _ _ _).mpr ⟨ih, hgq b hb⟩
        | sup p hp hc ih => exact R.sup_le p hc _ ih
      obtain ⟨b, hb, hfb, _⟩ := R.stage_max f hf
      have hgb : 𝔹.le (g b) b := by
        have h : 𝔹.le (g b) (f b) := 𝔹.le_join_right _ _
        rwa [hfb] at h
      have hz : g b = 𝔹.bot := by
        apply 𝔹.le_antisymm _ (𝔹.bot_le _)
        have h := 𝔹.le_meet hgb (hg b).1
        simpa only [𝔹.meet_neg] using h
      exact 𝔹.le_trans ((hg b).2.2 hz) (hstage b hb)

end CB_alg
end YesMetaZFC.Model.Boolean
