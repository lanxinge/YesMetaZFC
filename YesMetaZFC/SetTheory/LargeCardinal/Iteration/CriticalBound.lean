import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.Model.SetTheory.Relations.Parity

/-! # 原关系模型内的统一临界点下界

背景下界通过完整序数层解释进入扩展器的真实所属模型，再在其原关系中
与 κ 比较。列中同时记录实际所属结点，不能把 κ 的对象码当作背景序数。
后继沿同一模型列保存旧证书，新增证书由本次实际扩展器产生。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def It_lower_d (γ X R κ : M.Domain) : Prop := ∃ b z,
  Rr_layer_d I γ X R b z ∧ ∀ x, M.PairMember I x b R → M.PairMember I x κ R

def it_lower_m {d} (γ X R κ : Term d) : Formula 1 d := set[d] ⟪∃ b z,
  ⌜rr_layer_m⌝ₚ(⌜γ⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, b, z) ∧
  (∀ x, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, b, ⌜R⌝ₛ) →
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, ⌜κ⌝ₛ, ⌜R⌝ₛ))⟫
derive_free_closed it_lower_m

theorem it_lower_sat_l (hE : Extensional M) {d} (ρ : Env M d) (γ X R κ : Term d) :
    Formula.satisfies ρ (it_lower_m γ X R κ) ↔
      It_lower_d I (γ.eval ρ) (X.eval ρ) (R.eval ρ) (κ.eval ρ) := by
  simp only [it_lower_m, It_lower_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rr_layer_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

/-- 真实隶属表示中的下界给出同一个原关系证书；只用该表示已有的传递性。 -/
theorem It_lower_d.mem_l (hZF : M.Models ZF) {γ c X R κ : M.Domain}
    (model : Smem_d I c X R) (trans : M.TransitiveSet X) (hγ : M.mem γ X)
    (ord : M.IsOrdinal γ) (hκ : M.mem κ X) (lower : M.MemberSubset γ κ) :
    It_lower_d I γ X R κ := by
  obtain ⟨z, layer, _⟩ := rr_layer_mem_l I hZF model trans hγ ord.transitive
  exact ⟨γ, z, layer, fun x hx => (model.2 x κ).mpr
    ⟨((model.2 x γ).mp hx).1, hκ, lower x ((model.2 x γ).mp hx).2.2⟩⟩

def It_critical_bound_d (γ Q E : M.Domain) : Prop := ∀ i p κ L F,
  Rd_entry_d i p E → It_payload_d p κ L F →
    ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R ∧ It_lower_d I γ X R κ

def it_critical_bound_m {d} (γ Q E : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p κ L F, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p, κ, L, F) →
    ∃ c X R, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧
      ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) ∧ ⌜it_lower_m⌝ₚ(⌜γ⌝ₛ, X, R, κ)⟫
derive_free_closed it_critical_bound_m

theorem it_critical_bound_sat_l (hE : Extensional M) {d} (ρ : Env M d) (γ Q E : Term d) :
    Formula.satisfies ρ (it_critical_bound_m γ Q E) ↔
      It_critical_bound_d I (γ.eval ρ) (Q.eval ρ) (E.eval ρ) := by
  simp only [it_critical_bound_m, It_critical_bound_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hE, it_payload_sat_l hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, smdl_sat_l I,
    it_lower_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem It_critical_bound_d.empty_l {γ Q E : M.Domain} (empty : ∀ x, ¬ M.mem x E) :
    It_critical_bound_d I γ Q E := fun _ _ _ _ _ ⟨p, _, hp⟩ => (empty p hp).elim

/-- 操作码唯一性把实际所属模型的证书交给该列中的同一扩展器。 -/
theorem it_payload_bound_l (hKP : M.Models KP) {γ Q E i p κ L F c X R : M.Domain}
    (function : M.IsSetFunction (kp_pair_l hKP) E) (entry : Rd_entry_d i p E)
    (payload : It_payload_d p κ L F) (node : Rd_entry_d i c Q) (model : Smdl_d I c X R)
    (lower : It_lower_d I γ X R κ) :
    ∀ q μ ρ H, Rd_entry_d i q E → It_payload_d q μ ρ H →
      ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R ∧ It_lower_d I γ X R μ := by
  intro q μ ρ H hq pay
  have eq := function.2 i q p hq entry
  subst q
  exact ⟨c, X, R, node, model, (payload.unique_l pay).1 ▸ lower⟩

theorem It_extension_d.critical_bound_l {γ α ξ k T Q G E β U Q' G' E' : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β U Q' G' E')
    (old : It_critical_bound_d I γ Q E)
    (new : ∀ p κ L F, Rd_entry_d ξ p E' → It_payload_d p κ L F →
      ∃ c X R, Rd_entry_d ξ c Q' ∧ Smdl_d I c X R ∧ It_lower_d I γ X R κ) :
    It_critical_bound_d I γ Q' E' := by
  classical
  intro i p κ L F entry payload
  by_cases eq : i = ξ
  · exact eq ▸ new p κ L F (eq ▸ entry) payload
  · obtain ⟨c, X, R, node, model, lower⟩ := old i p κ L F
      ((extension.2.2.2.2.2 i p eq).mp entry) payload
    exact ⟨c, X, R, extension.2.2.1 i c node, model, lower⟩

end YesMetaZFC.SetTheory.LargeCardinal
