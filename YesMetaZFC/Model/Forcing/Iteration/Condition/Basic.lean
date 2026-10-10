import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction
import YesMetaZFC.SetTheory.Card.Finite
import YesMetaZFC.SetTheory.Card.Omega

/-! # 支撑迭代的内部部分函数条件

条件是定义域包含于内部索引集的集合函数图。后继坐标等于指定顶名称时省略，
其余情况只添加一个条目；支撑集合始终是模型中的实际定义域。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

structure Row_d (α p : M.Domain) : Prop where
  graph : ∀ v, M.mem v p → ∃ i s, KPair_d M v i s
  functional : ∀ i s t, Entry_d M i s p → Entry_d M i t p → s = t
  domain : ∀ i s, Entry_d M i s p → M.mem i α

def Coord_d (p D : M.Domain) : Prop := ∀ i, M.mem i D ↔ ∃ s, Entry_d M i s p

def Row_append_d (α t p s q : M.Domain) : Prop :=
  (s = t ∧ q = p) ∨ (s ≠ t ∧ ∃ v, KPair_d M v α s ∧ ∀ w, M.mem w q ↔ M.mem w p ∨ w = v)

def row_m {n} (α p : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l p) (.conj
    (.forallE (.forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) p.weaken.weaken.weaken)
      (.imp (entry_m (.bound 2) .newest p.weaken.weaken.weaken) (Formula.extensionalEq (.bound 1) .newest))))))
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest p.weaken.weaken) (.mem (.bound 1) α.weaken.weaken)))))
derive_free_closed row_m

def coord_m {n} (p D : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest D.weaken) (.existsE (entry_m (.bound 1) .newest p.weaken.weaken)))
derive_free_closed coord_m

def row_append_m {n} (α t p s q : Term n) : Formula 1 n :=
  .disj (.conj (Formula.extensionalEq s t) (Formula.extensionalEq q p))
    (.conj (.neg (Formula.extensionalEq s t)) (.existsE (.conj (kpair_m .newest α.weaken s.weaken)
      (.forallE (.iff (.mem .newest q.weaken.weaken)
        (.disj (.mem .newest p.weaken.weaken) (Formula.extensionalEq .newest (.bound 1))))))))
derive_free_closed row_append_m

theorem row_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α p : Term n) :
    Formula.satisfies ρ (row_m α p) ↔ Row_d M (α.eval ρ) (p.eval ρ) := by
  simp only [row_m, Formula.isRelation, kpair_convention_l, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, kpair_sat_l M hE, entry_sat_l M hE, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩, fun hh => ⟨hh.graph, hh.functional, hh.domain⟩⟩

theorem coord_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p D : Term n) :
    Formula.satisfies ρ (coord_m p D) ↔ Coord_d M (p.eval ρ) (D.eval ρ) := by
  simp only [coord_m, Coord_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_append_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α t p s q : Term n) :
    Formula.satisfies ρ (row_append_m α t p s q) ↔
      Row_append_d M (α.eval ρ) (t.eval ρ) (p.eval ρ) (s.eval ρ) (q.eval ρ) := by
  simp only [row_append_m, Row_append_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    kpair_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_empty_l {α e} (he : ∀ x, ¬ M.mem x e) : Row_d M α e where
  graph v hv := False.elim (he v hv)
  functional _ _ _ hh := False.elim (hh.elim fun v hv => he v hv.2)
  domain _ _ hh := False.elim (hh.elim fun v hv => he v hv.2)

/-- 定义域与名称条目左坐标集合共用同一实际集合构造。 -/
theorem coord_exists_l (hZF : M.Models ZF) (p : M.Domain) : ∃ D, Coord_d M p D := entry_domain_l M hZF p

theorem coord_unique_l (hE : Extensional M) {p D E} (hD : Coord_d M p D) (hE' : Coord_d M p E) : D = E :=
  hE.eq_of_same_members D E (fun i => (hD i).trans (hE' i).symm)

/-- 原 KP 内实际构造后继坐标追加；指定顶名称保留原条件图。 -/
theorem row_append_exists_l (hKP : M.Models KP) (α t p s : M.Domain) : ∃ q, Row_append_d M α t p s q := by
  classical
  by_cases hs : s = t
  · exact ⟨p, Or.inl ⟨hs, rfl⟩⟩
  · obtain ⟨v, hv⟩ := (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)).total α s
    obtain ⟨q, hq⟩ := KP.exists_insert hKP p v
    exact ⟨q, Or.inr ⟨hs, v, hv, hq⟩⟩

theorem row_append_unique_l (hE : Extensional M) {α t p s q r}
    (hq : Row_append_d M α t p s q) (hr : Row_append_d M α t p s r) : q = r := by
  rcases hq with ⟨hs, rfl⟩ | ⟨hs, v, hv, hq⟩ <;> rcases hr with ⟨hs', rfl⟩ | ⟨hs', w, hw, hr⟩
  · rfl
  · exact False.elim (hs' hs)
  · exact False.elim (hs hs')
  · have he := kpair_unique_l M hE hv hw
    subst w
    exact hE.eq_of_same_members q r (fun x => (hq x).trans (hr x).symm)

theorem row_append_entry_l {α t p s q} (h : Row_append_d M α t p s q) (i v) :
    Entry_d M i v q ↔ Entry_d M i v p ∨ (s ≠ t ∧ i = α ∧ v = s) := by
  rcases h with ⟨hs, rfl⟩ | ⟨hs, a, ha, hq⟩
  · exact ⟨Or.inl, fun hh => hh.elim id (fun hn => False.elim (hn.1 hs))⟩
  · constructor
    · rintro ⟨w, hw, hwq⟩
      rcases (hq w).mp hwq with hwp | rfl
      · exact Or.inl ⟨w, hw, hwp⟩
      · exact Or.inr ⟨hs, kpair_injective_l M hw ha⟩
    · rintro (⟨w, hw, hwp⟩ | ⟨_, rfl, rfl⟩)
      · exact ⟨w, hw, (hq w).mpr (Or.inl hwp)⟩
      · exact ⟨a, ha, (hq a).mpr (Or.inr rfl)⟩

end YesMetaZFC.Model.Forcing.Internal
