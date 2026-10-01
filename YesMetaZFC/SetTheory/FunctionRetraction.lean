import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 单射的带默认值反向函数

单射像上的原像唯一；像外返回指定点。该构造只需 ZF，不从满射任意选取截面。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem injection_retract_l (hZF : M.Models ZF) {G X Y Z a}
    (hG : M.IsSetInjectionFromTo I G X Y) (hXZ : M.MemberSubset X Z) (ha : M.mem a Z) :
    ∃ F, M.IsSetFunctionFromTo I F Y Z ∧ ∀ x i, M.PairMember I x i G → M.PairMember I i x F := by
  classical
  let ρ : Env M 2 := (⟨fun _ => G, fun _ => G⟩ : Env M 1).push a
  let φ : BinarySchema 2 := {
    body := .disj (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))
      (.conj (.neg (.existsE (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))))
        (Formula.extensionalEq .newest (.bound 2))) }
  have hφ i x : φ.denote ρ i x ↔ M.PairMember I x i G ∨ ((¬ ∃ y, M.PairMember I y i G) ∧ x = a) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨F, hF, hf⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := Z) (by
    intro i _
    by_cases h : ∃ y, M.PairMember I y i G
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, (hφ i y).mpr (Or.inl hy)⟩
    · exact ⟨a, (hφ i a).mpr (Or.inr ⟨h, rfl⟩)⟩) (by
    intro i _ x y hx hy
    rcases (hφ i x).mp hx with hx | hx <;> rcases (hφ i y).mp hy with hy | hy
    · exact hG.2 x y i hx hy
    · exact (hy.1 ⟨x, hx⟩).elim
    · exact (hx.1 ⟨y, hy⟩).elim
    · exact hx.2.trans hy.2.symm) (by
    intro i x _ hx
    exact ((hφ i x).mp hx).elim (fun hx => hXZ x (hG.1.input_mem_of_pairMember hx)) (fun hx => hx.2.symm ▸ ha))
  exact ⟨F, hF, fun x i hxi => (hf i x).mpr
    ⟨hG.1.output_mem_of_pairMember hxi, (hφ i x).mpr (Or.inl hxi)⟩⟩

end YesMetaZFC.SetTheory.ZF
