import YesMetaZFC.Model.SmallGraph.Closure

/-! # 基础公理与选择集

基础公理由已经证明的商成员良基性给出。选择只用于原生存在性证明：
先对实际族成员选值，再沿小呈现收集，重复的图呈现不会产生不同的选择。
-/

namespace YesMetaZFC.Model.SmallGraph.SG_set
universe u

theorem foundation (x : SG_set.{u}) (h : ∃ a, a ∈ x) :
    ∃ a, a ∈ x ∧ ∀ b, b ∈ x → ¬ b ∈ a := by
  classical
  obtain ⟨a, ha⟩ := h
  have hmin (a : SG_set.{u}) : a ∈ x → ∃ b, b ∈ x ∧ ∀ c, c ∈ x → ¬ c ∈ b := by
    apply mem_wf.induction a
    intro a ih ha
    by_cases h : ∃ b, b ∈ x ∧ b ∈ a
    · obtain ⟨b, hb, hba⟩ := h
      exact ih b hba hb
    · exact ⟨a, ha, fun b hb hba => h ⟨b, hb, hba⟩⟩
  exact hmin a ha

/-- 对两两不交的非空集合族构造原选择公理要求的选择集。 -/
theorem choice (x : SG_set.{u})
    (hne : ∀ a, a ∈ x → ∃ b, b ∈ a)
    (hdis : ∀ a, a ∈ x → ∀ b, b ∈ x → a ≠ b → ¬ ∃ z, z ∈ a ∧ z ∈ b) :
    ∃ c : SG_set.{u}, ∀ a, a ∈ x →
      ∃ b, (b ∈ c ∧ b ∈ a) ∧ ∀ d, (d ∈ c ∧ d ∈ a) → d = b := by
  classical
  let A := {a : SG_set.{u} // a ∈ x}
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun a : A => hne a.1 a.2)
  obtain ⟨ι, f, hf⟩ := small_presentation x
  let e (i : ι) : A := ⟨f i, (hf _).mpr ⟨i, rfl⟩⟩
  obtain ⟨c, hc⟩ := small_collect (fun i => g (e i))
  refine ⟨c, fun a ha => ⟨g ⟨a, ha⟩, ?_, ?_⟩⟩
  · constructor
    · obtain ⟨i, hi⟩ := (hf a).mp ha
      exact (hc _).mpr ⟨i, congrArg g (Subtype.ext hi)⟩
    · exact hg ⟨a, ha⟩
  · rintro d ⟨hdc, hda⟩
    obtain ⟨i, rfl⟩ := (hc d).mp hdc
    have h : f i = a := by
      apply Classical.byContradiction
      intro h
      exact hdis (f i) (e i).2 a ha h ⟨g (e i), hg (e i), hda⟩
    exact congrArg g (Subtype.ext h)

end YesMetaZFC.Model.SmallGraph.SG_set
