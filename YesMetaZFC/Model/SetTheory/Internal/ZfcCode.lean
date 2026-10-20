import YesMetaZFC.Model.SetTheory.Internal.RelationEvaluation
import YesMetaZFC.Model.SetTheory.Internal.BinaryTruth
import YesMetaZFC.Model.SetTheory.Internal.RelationSeparation
import YesMetaZFC.SetTheory.Notation

/-! # 背景内部的完整 ZFC 模型证书

固定公理与两个模式均由一个背景公式读取。模式量化全部内部程序和赋值，
不把外部标准 AST 的逐条满足误作内部 ZFC。收集只断言存在集合界，尚未选择函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def zc_base_m : Formula 1 0 :=
  .conj Axioms.extensionality.formula (.conj Axioms.emptySet.formula
    (.conj Axioms.pairing.formula (.conj Axioms.union.formula
      (.conj Axioms.powerSet.formula (.conj Axioms.infinity.formula
        (.conj Axioms.foundation.formula Axioms.choice.formula))))))

theorem zc_base_closed_l : zc_base_m.FreeClosed :=
  ⟨Axioms.extensionality.freeClosed, Axioms.emptySet.freeClosed, Axioms.pairing.freeClosed,
    Axioms.union.freeClosed, Axioms.powerSet.freeClosed, Axioms.infinity.freeClosed,
    Axioms.foundation.freeClosed, Axioms.choice.freeClosed⟩

structure Zc_schemas_d (ω X R : M.Domain) : Prop where
  separation : ∀ E F n r i f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem f E → M.mem D X → ∃ A, M.mem A X ∧ Sr_sep_d I X R E F n r i f D A
  collection : ∀ E F n r i j f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem D X →
    (∀ x, M.mem x X → M.PairMember I x D R → ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) →
    ∃ C, M.mem C X ∧ ∀ x, M.mem x X → M.PairMember I x D R →
      ∃ y, M.mem y X ∧ M.PairMember I y C R ∧ Sbin_d I X R E F n r i j f x y

structure Zc_model_d (ω c X R : M.Domain) : Prop where
  model : Smdl_d I c X R
  ext : Rf_ext_d I X R
  base : ∀ ρ : Env (smdl_structure_l I (R := R) model.2.1) 0, Formula.satisfies ρ zc_base_m
  schemas : Zc_schemas_d I ω X R

@[simp] private theorem zc_space_closed_l {d} (E ω X : Term d)
    (he : E.freeSupport = []) (hw : ω.freeSupport = []) (hx : X.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l E ω X).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace, Definitional.Formula.FreeClosed, he, hw, hx]

def zc_separation_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → f ∈ E → D ∈ ⌜X⌝ₛ → ∃ A ∈ ⌜X⌝ₛ,
      ∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, A, ⌜R⌝ₛ) ↔
        ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) ∧ (∃ g,
          ⌜senv_update_m (𝒞 := kpair_convention_l)⌝ₚ(f, i, x, g) ∧
          ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, g))⟫
derive_free_closed zc_separation_m

def zc_collection_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i j f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → j ∈ ⌜ω⌝ₛ → i ≠ j → f ∈ E → D ∈ ⌜X⌝ₛ →
    (∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) → ∃ y ∈ ⌜X⌝ₛ,
      ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)) →
    ∃ C ∈ ⌜X⌝ₛ, ∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) →
      ∃ y ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, C, ⌜R⌝ₛ) ∧
        ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)⟫
derive_free_closed zc_collection_m

def zc_model_m {d} (ω c X R : Term d) : Formula 1 d :=
  .conj (smdl_m (𝒞 := kpair_convention_l) c X R)
    (.conj (rf_ext_m (𝒞 := kpair_convention_l) X R)
      (.conj (rr_rel_m kpair_convention_l zc_base_m X R Fin.elim0)
        (.conj (zc_separation_m ω X R) (zc_collection_m ω X R))))

@[simp] theorem zc_model_closed_l {d} (ω c X R : Term d) (hω : ω.freeSupport = [])
    (hc : c.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (zc_model_m ω c X R).FreeClosed := by
  simp only [zc_model_m, Definitional.Formula.FreeClosed]
  exact ⟨smdl_m_freeClosed c X R hc hX hR, rf_ext_m_freeClosed X R hX hR,
    rr_rel_closed_l _ _ zc_base_closed_l X R Fin.elim0 hX hR (fun i => Fin.elim0 i),
    zc_separation_m_freeClosed ω X R hω hX hR, zc_collection_m_freeClosed ω X R hω hX hR⟩

/-- 解码保留内部非标准程序；没有额外的模型闭包前提。 -/
theorem zc_model_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X R : Term d) :
    Formula.satisfies ρ (zc_model_m ω c X R) ↔
      Zc_model_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have sep : Formula.satisfies ρ (zc_separation_m ω X R) ↔
      ∀ E F n r i f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem f E → M.mem D (X.eval ρ) →
          ∃ A, M.mem A (X.eval ρ) ∧ Sr_sep_d I (X.eval ρ) (R.eval ρ) E F n r i f D A := by
    simp only [zc_separation_m, Sr_sep_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionSpace_iff I hE,
      sfm_sat_l I hE, senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl
  have collect : Formula.satisfies ρ (zc_collection_m ω X R) ↔
      ∀ E F n r i j f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem j (ω.eval ρ) → i ≠ j → M.mem f E → M.mem D (X.eval ρ) →
        (∀ x, M.mem x (X.eval ρ) → M.PairMember I x D (R.eval ρ) →
          ∃ y, M.mem y (X.eval ρ) ∧ Sbin_d I (X.eval ρ) (R.eval ρ) E F n r i j f x y) →
        ∃ C, M.mem C (X.eval ρ) ∧ ∀ x, M.mem x (X.eval ρ) → M.PairMember I x D (R.eval ρ) →
          ∃ y, M.mem y (X.eval ρ) ∧ M.PairMember I y C (R.eval ρ) ∧
            Sbin_d I (X.eval ρ) (R.eval ρ) E F n r i j f x y := by
    simp only [zc_collection_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_isFunctionSpace_iff I hE, sfm_sat_l I hE, sbin_sat_l I hE,
      Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
      Definitional.Term.eval_weaken]; rfl
  simp only [zc_model_m, Formula.satisfies_conj_iff, smdl_sat_l I, rf_ext_sat_l I hE, sep, collect]
  constructor
  · rintro ⟨hm, ext, base, hs, hc⟩
    exact ⟨hm, ext, fun η => (rr_rel_sat_l I hm.2.1 _ zc_base_closed_l η ρ X R Fin.elim0
      rfl rfl (fun i => Fin.elim0 i)).mp base, hs, hc⟩
  · intro h
    obtain ⟨x, hx⟩ := h.model.2.1
    let η : Env (smdl_structure_l I (R := R.eval ρ) h.model.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
    exact ⟨h.model, h.ext, (rr_rel_sat_l I h.model.2.1 _ zc_base_closed_l η ρ X R Fin.elim0
      rfl rfl (fun i => Fin.elim0 i)).mpr (h.base η), h.schemas.separation, h.schemas.collection⟩

end YesMetaZFC.SetTheory.Internal
