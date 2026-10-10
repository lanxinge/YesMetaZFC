import YesMetaZFC.SetTheory.Descriptive.RealArrayEncode

/-! # 仅对内部实数使用的可数选择

可数交的见证交换只需要 AC_ω(B)，并不要求模型满足整个选择公理。
下方从已有 ZFC 集合关系单值化给出实际实例，所有输出仍是模型内函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 仅在当前指标集上选择实数；有限指标实例由 ZF 直接构造。 -/
def Cc_d (D B : M.Domain) : Prop := ∀ R,
  (∀ i, M.mem i D → ∃ x, M.mem x B ∧ M.PairMember I i x R) →
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → M.PairMember I i x R
def Fcc_d (B H : M.Domain) : Prop := ∀ D, M.IsDomainOf I D H → Cc_d I D B

def cc_m {d} (D B : Term d) : Formula 1 d := .forallE (.imp
  (Formula.forallMem D.weaken (Formula.existsMem B.weaken.weaken
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))))
  (.existsE (.conj (Formula.isFunctionFromTo 𝒞 .newest D.weaken.weaken B.weaken.weaken)
    (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))))
derive_free_closed cc_m
theorem cc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D B : Term d) :
    Formula.satisfies ρ (cc_m (𝒞 := 𝒞) D B) ↔ Cc_d I (D.eval ρ) (B.eval ρ) := by
  simp only [cc_m, Cc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Definitional.Term.eval_weaken]; rfl
def fcc_m {d} (B H : Term d) : Formula 1 d := .forallE (.imp (Formula.isDomain 𝒞 .newest H.weaken)
  (cc_m (𝒞 := 𝒞) .newest B.weaken))
derive_free_closed fcc_m
theorem fcc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B H : Term d) :
    Formula.satisfies ρ (fcc_m (𝒞 := 𝒞) B H) ↔ Fcc_d I (B.eval ρ) (H.eval ρ) := by
  simp only [fcc_m, Fcc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isDomain_iff I, cc_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Rcc_d (ω B : M.Domain) : Prop := ∀ D R, M.MemberSubset D ω →
  (∀ i, M.mem i D → ∃ x, M.mem x B ∧ M.PairMember I i x R) →
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → M.PairMember I i x R
def rcc_m {d} (ω B : Term d) : Formula 1 d := .forallE (.forallE
  (.imp (Formula.subset (.bound 1) ω.weaken.weaken) (.imp
    (Formula.forallMem (.bound 1) (Formula.existsMem B.weaken.weaken.weaken (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))))
    (.existsE (.conj (Formula.isFunctionFromTo 𝒞 .newest (.bound 2) B.weaken.weaken.weaken)
      (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))))))
derive_free_closed rcc_m
theorem rcc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B : Term d) :
    Formula.satisfies ρ (rcc_m (𝒞 := 𝒞) ω B) ↔ Rcc_d I (ω.eval ρ) (B.eval ρ) := by
  simp only [rcc_m, Rcc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Definitional.Term.eval_weaken]; rfl

theorem rcc_zfc_l (hZFC : M.Models ZFC) (ω B : M.Domain) : Rcc_d I ω B :=
  fun _ _ _ ht => ZFC.uniformize_l I hZFC ht

theorem cc_schema_l (hZF : M.Models ZF) {B D} (h : Cc_d I D B)
    {d} (φ : BinarySchema d) (ρ : Env M d)
    (ht : ∀ i, M.mem i D → ∃ x, M.mem x B ∧ φ.denote ρ i x) :
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → φ.denote ρ i x := by
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D B
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  obtain ⟨F, hf, he⟩ := h R (fun i hi => (ht i hi).elim fun x hx =>
    ⟨x, hx.1, (hr i x).mpr ⟨(hW i).mpr (Or.inl hi), (hW x).mpr (Or.inr hx.1), hx.2⟩⟩)
  exact ⟨F, hf, fun i x hx => ((hr i x).mp (he i x hx)).2.2⟩

theorem fcc_real_l {ω B H} (h : Rcc_d I ω B) (hH : ∀ i p, M.PairMember I i p H → M.mem i ω) : Fcc_d I B H :=
  fun D hd R ht => h D R (fun i hi => ((hd i).mp hi).elim fun p hp => hH i p hp) ht

end YesMetaZFC.SetTheory.Descriptive
