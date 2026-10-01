import YesMetaZFC.Model.Forcing.Iteration.Stage.Successor
import YesMetaZFC.Model.Forcing.TwoStep.Presentation

/-! # 名称后继的确定构造式

混合闭名称库先唯一确定二步条件集和序关系，再由省略顶坐标的编码唯一确定
部分函数阶段。构造式本身是原公式，后续内部递归可以直接消费。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

structure Row_repr_d (α t C S D V : M.Domain) : Prop where
  conditions : ∀ p, M.mem p D ↔ ∃ c, M.mem c C ∧ Row_code_d M α t c p
  graph : ∀ v, M.mem v V → ∃ p q, KPair_d M v p q
  relation : ∀ p q, Entry_d M p q V ↔ ∃ c d, M.mem c C ∧ M.mem d C ∧
    Row_code_d M α t c p ∧ Row_code_d M α t d q ∧ Entry_d M c d S

def Row_next_d (α B R e A T t D V : M.Domain) : Prop := ∃ W C S,
  Name_pool_d M B A t W ∧ Two_step_d M B R B e A T W C S ∧ Row_repr_d M α t C S D V

def row_repr_m {n} (α t C S D V : Term n) : Formula 1 n :=
  .conj (.forallE (.iff (.mem .newest D.weaken) (.existsE (.conj (.mem .newest C.weaken.weaken)
    (row_code_m α.weaken.weaken t.weaken.weaken .newest (.bound 1))))))
    (.conj (Formula.isRelation kpair_convention_l V)
      (.forallE (.forallE (.iff (entry_m (.bound 1) .newest V.weaken.weaken)
        (.existsE (.existsE (.conj (.mem (.bound 1) C.weaken.weaken.weaken.weaken)
          (.conj (.mem .newest C.weaken.weaken.weaken.weaken)
            (.conj (row_code_m α.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken (.bound 1) (.bound 3))
              (.conj (row_code_m α.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken .newest (.bound 2))
                (entry_m (.bound 1) .newest S.weaken.weaken.weaken.weaken)))))))))))
derive_free_closed row_repr_m

def row_next_m {n} (α B R e A T t D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj
    (name_pool_m B.weaken.weaken.weaken A.weaken.weaken.weaken t.weaken.weaken.weaken (.bound 2))
    (.conj (two_step_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken
      e.weaken.weaken.weaken A.weaken.weaken.weaken T.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
      (row_repr_m α.weaken.weaken.weaken t.weaken.weaken.weaken (.bound 1) .newest D.weaken.weaken.weaken V.weaken.weaken.weaken)))))
derive_free_closed row_next_m

theorem row_repr_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α t C S D V : Term n) :
    Formula.satisfies ρ (row_repr_m α t C S D V) ↔
      Row_repr_d M (α.eval ρ) (t.eval ρ) (C.eval ρ) (S.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_repr_m, Formula.isRelation, kpair_convention_l, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, row_code_sat_l hE, kpair_sat_l M hE,
    entry_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.conditions, h.graph, h.relation⟩⟩

theorem row_next_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R e A T t D V : Term n) :
    Formula.satisfies ρ (row_next_m α B R e A T t D V) ↔
      Row_next_d M (α.eval ρ) (B.eval ρ) (R.eval ρ) (e.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_next_m, Row_next_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    name_pool_sat_l M hE, two_step_sat_l hE, row_repr_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_repr_unique_l (hE : Extensional M) {α t C S D V D' V'}
    (h : Row_repr_d M α t C S D V) (h' : Row_repr_d M α t C S D' V') : D = D' ∧ V = V' :=
  ⟨hE.eq_of_same_members D D' (fun p => (h.conditions p).trans (h'.conditions p).symm),
    entry_ext_l M hE h.graph h'.graph (fun p q => (h.relation p q).trans (h'.relation p q).symm)⟩

/-- 给定具体迭代名称后，整个后继偏序是唯一的模型内对象。 -/
theorem row_next_unique_l (hE : Extensional M) {α B R e A T t D V D' V'}
    (h : Row_next_d M α B R e A T t D V) (h' : Row_next_d M α B R e A T t D' V') : D = D' ∧ V = V' := by
  obtain ⟨W, C, S, hW, hS, h⟩ := h
  obtain ⟨W', C', S', hW', hS', h'⟩ := h'
  obtain ⟨hw, hc, hs⟩ := two_step_pool_unique_l hE hW hW' hS hS'
  subst W'
  subst C'
  subst S'
  exact row_repr_unique_l M hE h h'

end YesMetaZFC.Model.Forcing.Internal
