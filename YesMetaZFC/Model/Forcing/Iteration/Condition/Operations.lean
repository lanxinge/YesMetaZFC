import YesMetaZFC.Model.Forcing.Iteration.Condition.Basic

/-! # 迭代条件的后继追加与原样限制

省略顶坐标后，限制到旧索引集精确恢复原条件，且新条件唯一确定旧条件和
新坐标名称。由此可把实际二步条件无损地改写为部分函数条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_append_row_l {α β t p s q} (hα : ¬ M.mem α α) (hp : Row_d M α p) (hβ : M.SuccessorOf β α)
    (h : Row_append_d M α t p s q) : Row_d M β q := by
  have hn v (hv : Entry_d M α v p) : False := hα (hp.domain α v hv)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases h with ⟨_, rfl⟩ | ⟨_, a, ha, hq⟩
    · exact hp.graph v hv
    · rcases (hq v).mp hv with hv | rfl
      · exact hp.graph v hv
      · exact ⟨α, s, ha⟩
  · intro i u v hu hv
    rcases (row_append_entry_l M h i u).mp hu with hu | ⟨_, hui, hus⟩ <;>
      rcases (row_append_entry_l M h i v).mp hv with hv | ⟨_, hvi, hvs⟩
    · exact hp.functional i u v hu hv
    · exact False.elim (hn u (hvi ▸ hu))
    · exact False.elim (hn v (hui ▸ hv))
    · exact hus.trans hvs.symm
  · intro i v hv
    rcases (row_append_entry_l M h i v).mp hv with hv | ⟨_, rfl, _⟩
    · exact (hβ i).mpr (Or.inl (hp.domain i v hv))
    · exact hβ.predecessor_mem

/-- 后继条件限制到旧索引集时，恢复原条件图本身。 -/
theorem row_append_prefix_l {α t p s q} (hα : ¬ M.mem α α) (hp : Row_d M α p)
    (h : Row_append_d M α t p s q) (i v) : Entry_d M i v p ↔ M.mem i α ∧ Entry_d M i v q := by
  constructor
  · intro hv
    exact ⟨hp.domain i v hv, (row_append_entry_l M h i v).mpr (Or.inl hv)⟩
  · rintro ⟨hi, hv⟩
    rcases (row_append_entry_l M h i v).mp hv with hv | ⟨_, rfl, _⟩
    · exact hv
    · exact False.elim (hα hi)

theorem row_ext_l (hE : Extensional M) {α β p q} (hp : Row_d M α p) (hq : Row_d M β q)
    (h : ∀ i s, Entry_d M i s p ↔ Entry_d M i s q) : p = q := entry_ext_l M hE hp.graph hq.graph h

/-- 追加编码同时反射原条件和坐标名称，包括省略顶坐标的分支。 -/
theorem row_append_injective_l (hE : Extensional M) {α t p p' s s' q}
    (hα : ¬ M.mem α α) (hp : Row_d M α p) (hp' : Row_d M α p')
    (h : Row_append_d M α t p s q) (h' : Row_append_d M α t p' s' q) : p = p' ∧ s = s' := by
  have eqp : p = p' := row_ext_l hE hp hp' (fun i v =>
    (row_append_prefix_l hα hp h i v).trans (row_append_prefix_l hα hp' h' i v).symm)
  have hn v (hv : Entry_d M α v p) : False := hα (hp.domain α v hv)
  have hn' v (hv : Entry_d M α v p') : False := hα (hp'.domain α v hv)
  refine ⟨eqp, ?_⟩
  classical
  by_cases hs : s = t
  · by_cases hs' : s' = t
    · exact hs.trans hs'.symm
    · have hv := (row_append_entry_l M h' α s').mpr (Or.inr ⟨hs', rfl, rfl⟩)
      exact False.elim (((row_append_entry_l M h α s').mp hv).elim (hn s') (fun hh => hh.1 hs))
  · have hv := (row_append_entry_l M h α s).mpr (Or.inr ⟨hs, rfl, rfl⟩)
    exact ((row_append_entry_l M h' α s).mp hv).elim (fun hh => False.elim (hn' s hh)) (fun hh => hh.2.2)

/-- 限制到任意模型内索引集，直接返回实际函数图及其条目证书。 -/
theorem row_restrict_l (hZF : M.Models ZF) {α p} (hp : Row_d M α p) (β : M.Domain) :
    ∃ q, Row_d M β q ∧ M.IsRestrictionOf
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) q p β := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨q, hq⟩ := ZF.exists_restriction hZF I p β
  exact ⟨q, ⟨hq.1, fun i s t hs ht => hp.functional i s t ((hq.2 i s).mp hs).2 ((hq.2 i t).mp ht).2,
    fun i s hs => ((hq.2 i s).mp hs).1⟩, hq⟩

end YesMetaZFC.Model.Forcing.Internal
