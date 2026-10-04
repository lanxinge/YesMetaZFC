import YesMetaZFC.SetTheory.LargeCardinal.SupportProjection
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd

/-! # 扩展器正规性的坐标图

把 f 的值作为有限列的末坐标。该图是有界公式，故可直接沿原初等嵌入传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}}

def En_graph_d (n κ D f s : M.Domain) : Prop := ∃ t, M.mem t D ∧ M.MemberSubset t s ∧
  ∃ x, M.mem x κ ∧ Rd_entry_d t x f ∧ Rd_entry_d n x s

def en_graph_m {d} (n κ D f s : Term d) : Formula 1 d := Formula.existsMem D
  (.conj (Formula.subset .newest s.weaken) (Formula.existsMem κ.weaken (.conj
    (rd_entry0_m (.bound 1) .newest f.weaken.weaken) (rd_entry0_m n.weaken.weaken .newest s.weaken.weaken))))
derive_free_closed en_graph_m

theorem en_graph_delta_l {d} (n κ D f s : Term d) : (en_graph_m n κ D f s).IsDelta0 :=
  .existsMem _ (.conj (.atom _ _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))

theorem en_graph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n κ D f s : Term d) :
    Formula.satisfies ρ (en_graph_m n κ D f s) ↔
      En_graph_d (n.eval ρ) (κ.eval ρ) (D.eval ρ) (f.eval ρ) (s.eval ρ) := by
  simp only [en_graph_m, En_graph_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 正规性允许在原坐标列末尾加入一个较小坐标；原列中的重复与排列均保留。 -/
def En_normal_d (ω κ L F : M.Domain) : Prop := ∀ n a U D f i α A,
  M.mem n ω → Fn0_d n L a → Rd_entry_d a U F → (∀ s, M.mem s D ↔ Fn0_d n κ s) →
  Fn0_d D κ f → Rd_entry_d i α a → M.mem A U →
  (∀ s, M.mem s A → ∀ x y, Rd_entry_d s x f → Rd_entry_d i y s → M.mem x y) →
  ∃ m b V β B, M.mem m ω ∧ M.SuccessorOf m n ∧ Fn0_d m L b ∧ M.MemberSubset a b ∧
    Rd_entry_d n β b ∧ M.mem β α ∧ Rd_entry_d b V F ∧ M.mem B V ∧
    ∀ s, M.mem s B → En_graph_d n κ A f s

end YesMetaZFC.SetTheory.LargeCardinal
