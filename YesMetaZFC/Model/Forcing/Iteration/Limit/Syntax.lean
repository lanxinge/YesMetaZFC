import YesMetaZFC.Model.Forcing.Iteration.Stage.System

/-! # 支撑极限的原公式

极限条件的每个阶段限制都是真实旧条件。序关系逐阶段比较这些实际限制，
有限或可数性施加于模型内的坐标定义域；量词均由原 Project 公式表达。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Row_lim_d (k : Bool) (ω σ F p : M.Domain) : Prop :=
  Row_d M σ p ∧ Row_supp_d I k ω p ∧ ∀ α B, Entry_d M α B F →
    ∃ a, M.mem a B ∧ M.IsRestrictionOf I a p α

def Row_lim_le_d (H p q : M.Domain) : Prop := ∀ α R, Entry_d M α R H →
  ∀ a b, M.IsRestrictionOf I a p α → M.IsRestrictionOf I b q α → Entry_d M a b R

structure Row_limit_d (k : Bool) (ω δ F H σ D V : M.Domain) : Prop where
  sup : M.IsUnionOf σ δ
  conditions : ∀ p, M.mem p D ↔ Row_lim_d I k ω σ F p
  graph : ∀ v, M.mem v V → ∃ p q, KPair_d M v p q
  relation : ∀ p q, Entry_d M p q V ↔ M.mem p D ∧ M.mem q D ∧ Row_lim_le_d I H p q

def row_lim_m (k : Bool) {n} (ω σ F p : Term n) : Formula 1 n :=
  .conj (row_m σ p) (.conj (row_supp_m kpair_convention_l k ω p)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest F.weaken.weaken)
      (.existsE (.conj (.mem .newest (.bound 1))
        (Formula.isRestriction kpair_convention_l .newest p.weaken.weaken.weaken (.bound 2))))))))
derive_free_closed row_lim_m

def row_lim_le_m {n} (H p q : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest H.weaken.weaken)
    (.forallE (.forallE (.imp
      (Formula.isRestriction kpair_convention_l (.bound 1) p.weaken.weaken.weaken.weaken (.bound 3))
      (.imp (Formula.isRestriction kpair_convention_l .newest q.weaken.weaken.weaken.weaken (.bound 3))
        (entry_m (.bound 1) .newest (.bound 2))))))))
derive_free_closed row_lim_le_m

def row_limit_m (k : Bool) {n} (ω δ F H σ D V : Term n) : Formula 1 n :=
  .conj (Formula.isUnion σ δ) (.conj
    (.forallE (.iff (.mem .newest D.weaken) (row_lim_m k ω.weaken σ.weaken F.weaken .newest)))
    (.conj (Formula.isRelation kpair_convention_l V) (.forallE (.forallE
      (.iff (entry_m (.bound 1) .newest V.weaken.weaken)
        (.conj (.mem (.bound 1) D.weaken.weaken) (.conj (.mem .newest D.weaken.weaken)
          (row_lim_le_m H.weaken.weaken (.bound 1) .newest))))))))
derive_free_closed row_limit_m

theorem row_lim_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (ω σ F p : Term n) :
    Formula.satisfies ρ (row_lim_m k ω σ F p) ↔
      Row_lim_d I k (ω.eval ρ) (σ.eval ρ) (F.eval ρ) (p.eval ρ) := by
  simp only [row_lim_m, Row_lim_d, Formula.satisfies_conj_iff, row_sat_l M hE,
    row_supp_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, entry_sat_l M hE,
    Formula.satisfies_isRestriction_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_lim_le_sat_l (hE : Extensional M) {n} (ρ : Env M n) (H p q : Term n) :
    Formula.satisfies ρ (row_lim_le_m H p q) ↔ Row_lim_le_d I (H.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [row_lim_le_m, Row_lim_le_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, Formula.satisfies_isRestriction_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_limit_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (ω δ F H σ D V : Term n) :
    Formula.satisfies ρ (row_limit_m k ω δ F H σ D V) ↔
      Row_limit_d I k (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (H.eval ρ) (σ.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_limit_m, Formula.isRelation, kpair_convention_l, Formula.satisfies_conj_iff,
    Formula.satisfies_isUnion_iff, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    row_lim_sat_l I hE, row_lim_le_sat_l I hE, entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.sup, h.conditions, h.graph, h.relation⟩⟩

/-- 极限的坐标域、条件集及完整关系图都由阶段序列唯一确定。 -/
theorem row_limit_unique_l (hE : Extensional M) {k ω δ F H σ D V σ' D' V'}
    (h : Row_limit_d I k ω δ F H σ D V) (h' : Row_limit_d I k ω δ F H σ' D' V') :
    σ = σ' ∧ D = D' ∧ V = V' := by
  have hσ := h.sup.eq hE h'.sup
  subst σ'
  have hD := hE.eq_of_same_members D D' (fun p => (h.conditions p).trans (h'.conditions p).symm)
  subst D'
  exact ⟨rfl, rfl, entry_ext_l M hE h.graph h'.graph (fun p q => (h.relation p q).trans (h'.relation p q).symm)⟩

/-- 极限条件在任一阶段的实际限制属于该阶段；与限制见证的选择无关。 -/
theorem row_lim_prefix_l (hE : Extensional M) {k ω σ F p α B a} (hp : Row_lim_d I k ω σ F p)
    (hB : Entry_d M α B F) (ha : M.IsRestrictionOf I a p α) : M.mem a B := by
  obtain ⟨b, hb, hbp⟩ := hp.2.2 α B hB
  exact (ha.eq hE hbp).symm ▸ hb

end YesMetaZFC.Model.Forcing.Internal
