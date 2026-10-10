import YesMetaZFC.SetTheory.Axioms.DependentChoice
import YesMetaZFC.SetTheory.DependentChoice

/-! # DC 的语义与已有 ZFC 模型实例

一般消费者只传当前内部 ω 的 DC；ZF＋DC 的原公理和原 ZFC 均自动提供它。
这里不从模型外部选择构造内部序列。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Dc_chain_d (ω X R a g : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I g ω X ∧
    (∀ e, (∀ x, ¬ M.mem x e) → M.PairMember I e a g) ∧
    ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x g → M.PairMember I j y g →
      M.PairMember I x y R

def Dc_d (ω : M.Domain) : Prop := ∀ X R a, M.mem a X →
  (∀ x, M.mem x X → ∃ y, M.mem y X ∧ M.PairMember I x y R) →
    ∃ g, Dc_chain_d I ω X R a g

theorem dc_chain_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R a g : Term d) :
    Formula.satisfies ρ (dc_chain_m 𝒞 ω X R a g) ↔
      Dc_chain_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (g.eval ρ) := by
  simp only [dc_chain_m, Dc_chain_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  rfl

theorem dc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω : Term d) :
    Formula.satisfies ρ (dc_m 𝒞 ω) ↔ Dc_d I (ω.eval ρ) := by
  simp only [dc_m, Dc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, dc_chain_sat_l I hE,
    Definitional.Term.eval_weaken]
  rfl

theorem ZFC.dc_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω) : Dc_d I ω :=
  fun _ _ _ ha ht => dependent_choice_l I hZFC hω ha ht

theorem dc_axiom_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) :
    M.SatisfiesSentence Axioms.dc_axiom ↔ ∀ ω, M.IsOmega ω → Dc_d I ω := by
  rw [Structure.satisfiesSentence_iff]
  simp only [Axioms.dc_axiom, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff, dc_sat_l I hE,
    Definitional.Term.eval_newest]
  exact ⟨fun h ω => h (fun _ => ω) ω, fun h _ => h⟩

theorem ZFDC.models_zf_l (h : M.Models ZFDC) : M.Models ZF :=
  ⟨h.1, fun s hs => h.2 s (.zf hs)⟩

theorem ZFDC.dc_l (h : M.Models ZFDC) {ω} (hω : M.IsOmega ω) :
    Dc_d (kpair_interpretation_l M h.1 (KP.exists_pair (ZF.modelsKP (models_zf_l h)))) ω :=
  (dc_axiom_sat_l _ h.1).mp (h.2 _ .dc) ω hω

/-- 已有 ZFC 模型直接实现全部新公理，包含原有的具体小图模型。 -/
theorem ZFC.models_zfdc_l (h : M.Models ZFC) : M.Models ZFDC := by
  refine ⟨h.1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact (models_zf_l h).2 s hs
  | dc =>
    exact (dc_axiom_sat_l (kpair_interpretation_l M h.1 (KP.exists_pair (ZF.modelsKP (models_zf_l h)))) h.1).mpr
      (fun _ hω => dc_l _ h hω)

end YesMetaZFC.SetTheory
