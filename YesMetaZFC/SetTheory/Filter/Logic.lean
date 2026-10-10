import YesMetaZFC.SetTheory.Filter

/-! # 超滤上的命题运算

经典推理只在 Prop 内使用；不构造超滤子或选择函数。
-/

namespace YesMetaZFC.SetTheory.Filter
universe u
variable {I : Type u} (U : Filter I)

theorem congr_l {p q : I → Prop} (h : U.sets (fun i => p i ↔ q i)) :
    U.sets p ↔ U.sets q :=
  ⟨fun hp => U.upward (U.inter_mem hp h) (fun _ hi => hi.2.mp hi.1),
    fun hq => U.upward (U.inter_mem hq h) (fun _ hi => hi.2.mpr hi.1)⟩

theorem pointwise_l {p q : I → Prop} (h : ∀ i, p i ↔ q i) : U.sets p ↔ U.sets q :=
  U.congr_l (U.upward U.univ_mem (fun i _ => h i))

theorem and_iff_l (p q : I → Prop) :
    U.sets (fun i => p i ∧ q i) ↔ U.sets p ∧ U.sets q :=
  ⟨fun h => ⟨U.upward h (fun _ => And.left), U.upward h (fun _ => And.right)⟩,
    fun h => U.inter_mem h.1 h.2⟩

theorem const_iff_l (hU : U.Proper) (p : Prop) : U.sets (fun _ => p) ↔ p := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hp
    exact hU (U.upward h (fun _ hi => hp hi))
  · intro hp
    exact U.upward U.univ_mem (fun _ _ => hp)

theorem neg_iff_l (hU : U.IsUltrafilter) (p : I → Prop) :
    U.sets (fun i => ¬ p i) ↔ ¬ U.sets p := by
  constructor
  · intro h hp
    exact not_complement_mem_of_proper_l hU.1 hp h
  · intro hp
    rcases ultrafilter_decides_l hU p with h | h
    · exact False.elim (hp h)
    · exact h

theorem or_iff_l (hU : U.IsUltrafilter) (p q : I → Prop) :
    U.sets (fun i => p i ∨ q i) ↔ U.sets p ∨ U.sets q := by
  constructor
  · intro h
    rcases ultrafilter_decides_l hU p with hp | hp
    · exact Or.inl hp
    · exact Or.inr (U.upward (U.inter_mem h hp) (fun _ hi => hi.1.resolve_left hi.2))
  · rintro (h | h)
    · exact U.upward h (fun _ => Or.inl)
    · exact U.upward h (fun _ => Or.inr)

theorem imp_iff_l (hU : U.IsUltrafilter) (p q : I → Prop) :
    U.sets (fun i => p i → q i) ↔ (U.sets p → U.sets q) := by
  constructor
  · intro h hp
    exact U.upward (U.inter_mem h hp) (fun _ hi => hi.1 hi.2)
  · intro h
    rcases ultrafilter_decides_l hU p with hp | hp
    · exact U.upward (h hp) (fun _ hi _ => hi)
    · exact U.upward hp (fun _ hi ha => False.elim (hi ha))

theorem iff_iff_l (hU : U.IsUltrafilter) (p q : I → Prop) :
    U.sets (fun i => p i ↔ q i) ↔ (U.sets p ↔ U.sets q) :=
  (U.pointwise_l (fun _ => iff_def)).trans
    ((U.and_iff_l _ _).trans ((and_congr (U.imp_iff_l hU p q)
      (U.imp_iff_l hU q p)).trans iff_def.symm))

/-- 指定点上的主超滤；点由调用者给定，不从非空性选择。 -/
def point_l (i : I) : Filter I := principal (fun j => j = i)

theorem point_mem_l (i : I) (p : I → Prop) : (point_l i).sets p ↔ p i :=
  ⟨fun h => h rfl, fun h _ hi => hi ▸ h⟩

theorem point_proper_l (i : I) : (point_l i).Proper := fun h => h rfl

theorem point_ultra_l (i : I) : (point_l i).IsUltrafilter := by
  refine ⟨point_proper_l i, ?_⟩
  intro F hF hp p h
  apply (point_mem_l i p).mpr
  apply Classical.byContradiction
  intro hn
  exact not_complement_mem_of_proper_l hp h
    (hF _ ((point_mem_l i _).mpr hn))

end YesMetaZFC.SetTheory.Filter
