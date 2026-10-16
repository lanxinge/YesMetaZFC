import YesMetaZFC.SetTheory.LargeCardinal.IterationNice
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax

/-! # 实际扩展器列的统一临界点下界

只检查列中真正的短扩展器记录。恒等填充没有此类记录；后继保留全部旧项，
新增项的下界由同一次超幂构造给出的原 κ 取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_critical_bound_d (γ E : M.Domain) : Prop := ∀ i p κ L F,
  Rd_entry_d i p E → It_payload_d p κ L F → M.MemberSubset γ κ

def it_critical_bound_m {d} (γ E : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p κ L F, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p, κ, L, F) → ⌜γ⌝ₛ ⊆ κ⟫
derive_free_closed it_critical_bound_m

theorem it_critical_bound_sat_l (hE : Extensional M) {d} (ρ : Env M d) (γ E : Term d) :
    Formula.satisfies ρ (it_critical_bound_m γ E) ↔ It_critical_bound_d (γ.eval ρ) (E.eval ρ) := by
  simp only [it_critical_bound_m, It_critical_bound_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hE, it_payload_sat_l hE,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem It_critical_bound_d.empty_l {γ E : M.Domain} (empty : ∀ x, ¬ M.mem x E) :
    It_critical_bound_d γ E := fun _ _ _ _ _ ⟨p, _, hp⟩ => (empty p hp).elim

/-- 同一操作条目的临界点由二元组编码唯一确定。 -/
theorem it_payload_bound_l (hKP : M.Models KP) {γ E i p κ L F : M.Domain}
    (function : M.IsSetFunction (kp_pair_l hKP) E) (entry : Rd_entry_d i p E)
    (payload : It_payload_d p κ L F) (lower : M.MemberSubset γ κ) :
    ∀ q μ ρ H, Rd_entry_d i q E → It_payload_d q μ ρ H → M.MemberSubset γ μ := by
  intro q μ ρ H hq pay
  have eq := function.2 i q p hq entry
  subst q
  exact (payload.unique_l pay).1 ▸ lower

theorem It_extension_d.critical_bound_l {γ α ξ k T Q G E β U Q' G' E' : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β U Q' G' E') (old : It_critical_bound_d γ E)
    (new : ∀ p κ L F, Rd_entry_d ξ p E' → It_payload_d p κ L F → M.MemberSubset γ κ) :
    It_critical_bound_d γ E' := by
  classical
  intro i p κ L F entry payload
  by_cases eq : i = ξ
  · exact new p κ L F (eq ▸ entry) payload
  · exact old i p κ L F ((extension.2.2.2.2.2 i p eq).mp entry) payload

end YesMetaZFC.SetTheory.LargeCardinal
