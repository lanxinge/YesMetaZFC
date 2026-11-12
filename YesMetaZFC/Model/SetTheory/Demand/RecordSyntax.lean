import YesMetaZFC.Model.SetTheory.Demand.NodeScope
import YesMetaZFC.Model.SetTheory.Demand.Reply

/-! # 完整双图回合记录的一阶表示

按原记录逐字段编码。分组截止于 q，全部旧标签与 pending 的值域截止于 h；
两者不混用，也不删去原元组的有限性、根位置或任一完整值域方向。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def td_record_m {l} (ω e k X S a b p α d q h m r : Term l) : Formula 1 l := set[l] ⟪
  ⌜(Formula.isOrdinalAddition kpair_convention_l)⌝ₚ(⌜d⌝ₛ,⌜k⌝ₛ,⌜k⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜q⌝ₛ,⌜d⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜h⌝ₛ,⌜q⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜m⌝ₛ,⌜h⌝ₛ) ∧ ⌜m⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜m⌝ₛ,⌜X⌝ₛ,⌜r⌝ₛ) ∧
  ⌜e⌝ₛ ∈ ⌜q⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ,⌜S⌝ₛ,⌜r⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜q⌝ₛ,⌜p⌝ₛ,⌜r⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜h⌝ₛ,⌜α⌝ₛ,⌜r⌝ₛ) ∧
  ⌜td_groups_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,⌜q⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜b⌝ₛ) ∧
  (∀ v, (v ∈ ⌜a⌝ₛ ∨ v ∈ ⌜b⌝ₛ ∨ v = ⌜p⌝ₛ) ↔
    ∃ i, i ∈ ⌜h⌝ₛ ∧ ¬ (i = ⌜e⌝ₛ) ∧ ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(i,v,⌜r⌝ₛ))⟫
derive_free_closed td_record_m

theorem td_record_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {l} (ρ : Env M l) (ω e k X S a b p α d q h m r : Term l) :
    Formula.satisfies ρ (td_record_m ω e k X S a b p α d q h m r) ↔
      Td_record_d I (ω.eval ρ) (e.eval ρ) (k.eval ρ) (X.eval ρ) (S.eval ρ)
        (a.eval ρ) (b.eval ρ) (p.eval ρ) (α.eval ρ) (d.eval ρ) (q.eval ρ)
        (h.eval ρ) (m.eval ρ) (r.eval ρ) := by
  simp only [td_record_m,Formula.satisfies_conj_iff,Formula.satisfies_isOrdinalAddition_iff I hE,
    Formula.satisfies_isSuccessor_iff,Formula.satisfies_mem_iff,fn0_sat_l hE,rd_entry0_sat_l hE,
    td_groups_sat_l I hE,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff,Formula.satisfies_neg_iff,Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩,
    fun r => ⟨r.twice,r.labels_end,r.pending_end,r.height_end,r.finite,r.tuple,
      r.root_before,r.root,r.pending,r.height,r.groups,r.values⟩⟩

end YesMetaZFC.SetTheory.Internal
