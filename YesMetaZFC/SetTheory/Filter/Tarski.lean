import YesMetaZFC.SetTheory.Filter
import YesMetaZFC.Model.Boolean.ChainFixedPoint

/-!
# Tarski 滤子扩张定理

每个真滤子都能扩张到极大真滤子。证明使用仓库已有的链完备偏序固定点定理，
只在构造严格扩张函数时对一个存在性命题取见证；不引入全局 Zorn 公理。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Filter

universe u

private theorem exists_strict_extension_of_not_maximal_l {α : Type u}
    (F : Filter α) (hF : Proper F) (hMax : ¬ IsMaximalProper F) :
    ∃ G : Filter α, Proper G ∧ Extends F G ∧ ¬ Extends G F :=
  Classical.byContradiction fun hNoStrict => hMax ⟨hF, fun G hFG hG s hs =>
    Classical.byContradiction fun hNotMem =>
      hNoStrict ⟨G, hG, hFG, fun hGF => hNotMem (hGF s hs)⟩⟩

/-- 每个真滤子都可扩张到极大真滤子；选择仅用于局部选取严格扩张。 -/
theorem tarski_filter_extension_l {α : Type u}
    (F : Filter α) (hF : Proper F) :
    ∃ U : Filter α, IsUltrafilter U ∧ Extends F U := by
  classical
  let P : Filter α → Prop := fun G => Proper G ∧ Extends F G
  let B := {G : Filter α // P G}
  let R : YesMetaZFC.Model.Boolean.CS_order B := {
    toPO_bot := {
      le := fun G H => Extends G.val H.val
      bot := ⟨F, hF, fun _ hs => hs⟩
      le_refl := fun G _ hs => hs
      le_trans := fun hGH hHK s hs => hHK s (hGH s hs)
      le_antisymm := by
        intro G H hGH hHG
        apply Subtype.ext
        apply ext_l
        intro s
        exact ⟨hGH s, hHG s⟩
      bot_le := fun G s hs => G.property.2 s hs
    }
    sup := fun C hC => by
      let U : Filter α := {
        sets := fun s => F.sets s ∨ ∃ G : B, C G ∧ G.val.sets s
        univ_mem := Or.inl F.univ_mem
        upward := by
          intro s t hs hst
          rcases hs with hsF | ⟨G, hG, hsG⟩
          · exact Or.inl (F.upward hsF hst)
          · exact Or.inr ⟨G, hG, G.val.upward hsG hst⟩
        inter_mem := by
          intro s t hs ht
          rcases hs with hsF | ⟨G, hG, hsG⟩
          · rcases ht with htF | ⟨H, hH, htH⟩
            · exact Or.inl (F.inter_mem hsF htF)
            · exact Or.inr ⟨H, hH, H.val.inter_mem (H.property.2 s hsF) htH⟩
          · rcases ht with htF | ⟨H, hH, htH⟩
            · exact Or.inr ⟨G, hG, G.val.inter_mem hsG (G.property.2 t htF)⟩
            · rcases hC G H hG hH with hGH | hHG
              · exact Or.inr ⟨H, hH, H.val.inter_mem (hGH s hsG) htH⟩
              · exact Or.inr ⟨G, hG, G.val.inter_mem hsG (hHG t htH)⟩
      }
      have hU : Proper U := by
        intro hEmpty
        rcases hEmpty with hEmptyF | ⟨G, hG, hEmptyG⟩
        · exact hF hEmptyF
        · exact G.property.1 hEmptyG
      exact ⟨U, hU, fun s hs => Or.inl hs⟩
    le_sup := by
      intro C hC G hG s hs
      exact Or.inr ⟨G, hG, hs⟩
    sup_le := by
      intro C hC G hG s hs
      rcases hs with hsF | ⟨K, hK, hsK⟩
      · exact G.property.2 s hsF
      · exact hG K hK s hsK
  }
  let f : B → B := fun G =>
    if hMax : IsMaximalProper G.val then G
    else
      let hStrict := exists_strict_extension_of_not_maximal_l G.val G.property.1 hMax
      let H := Classical.choose hStrict
      ⟨H, ⟨(Classical.choose_spec hStrict).1,
        fun s hs => (Classical.choose_spec hStrict).2.1 s (G.property.2 s hs)⟩⟩
  have hf : ∀ G, R.le G (f G) := by
    intro G
    by_cases hMax : IsMaximalProper G.val
    · simp only [f, dif_pos hMax]
      intro s hs
      exact hs
    · simp only [f, dif_neg hMax]
      change Extends G.val (Classical.choose
        (exists_strict_extension_of_not_maximal_l G.val G.property.1 hMax))
      exact (Classical.choose_spec
        (exists_strict_extension_of_not_maximal_l G.val G.property.1 hMax)).2.1
  obtain ⟨M, _, hFix, _⟩ := R.stage_max f hf
  have hMax : IsMaximalProper M.val :=
    Classical.byContradiction fun hNotMax => by
    let hStrict := exists_strict_extension_of_not_maximal_l M.val M.property.1 hNotMax
    have hSpec := Classical.choose_spec hStrict
    have hEq : Classical.choose hStrict = M.val := by
      calc
        Classical.choose hStrict = (f M).val := by simp [f, hNotMax]
        _ = M.val := congrArg Subtype.val hFix
    exact hSpec.2.2 (by
      intro s hs
      simpa [hEq] using hs)
  exact ⟨M.val, hMax, M.property.2⟩

end Filter
end SetTheory
end YesMetaZFC
