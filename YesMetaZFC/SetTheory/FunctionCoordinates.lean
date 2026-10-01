import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 集合函数图的逐项坐标分解

输入值实际编码为有序对时，替代分别取得两张坐标函数图。只需 ZF 与给定配对解释。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem function_coords_l (hZF : M.Models ZF) {X C Y Z F}
    (hF : M.IsSetFunctionFromTo I F X C)
    (hC : ∀ c, M.mem c C → ∃ y z, M.mem y Y ∧ M.mem z Z ∧ I.Codes c y z) :
    ∃ G H, M.IsSetFunctionFromTo I G X Y ∧ M.IsSetFunctionFromTo I H X Z ∧
      ∀ i c y z, M.PairMember I i c F → I.Codes c y z → M.PairMember I i y G ∧ M.PairMember I i z H := by
  have project (k : Bool) : ∃ G, M.IsSetFunctionFromTo I G X (if k then Z else Y) ∧
      ∀ i c y z, M.PairMember I i c F → I.Codes c y z → M.PairMember I i (if k then z else y) G := by
    let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
    let ψ : BinarySchema 1 := {
      body := .existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 2) (.bound 5))
        (.conj (𝒞.code (.bound 2) (.bound 1) .newest)
          (Formula.extensionalEq (.bound 3) (if k then .newest else .bound 1))))))
      freeClosed := by cases k <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
    have hψ i v : ψ.denote ρ i v ↔ ∃ c y z, M.PairMember I i c F ∧ I.Codes c y z ∧ v = (if k then z else y) := by
      cases k <;> simp only [ψ, BinarySchema.denote, Bool.false_eq_true, ↓reduceIte,
        Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I,
        I.realizes, Formula.satisfies_extensionalEq_iff_eq hZF.1] <;> rfl
    obtain ⟨G, hG, hg⟩ := exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := X)
      (target := if k then Z else Y) (by
        intro i hi
        obtain ⟨c, hc, hic⟩ := hF.2.2 i hi
        obtain ⟨y, z, _, _, hcy⟩ := hC c hc
        exact ⟨if k then z else y, (hψ i _).mpr ⟨c, y, z, hic, hcy, rfl⟩⟩) (by
        intro i _ a b ha hb
        obtain ⟨c, y, z, hic, hc, rfl⟩ := (hψ i a).mp ha
        obtain ⟨c', y', z', hic', hc', rfl⟩ := (hψ i b).mp hb
        have he := hF.1.2 i c c' hic hic'
        subst c'
        obtain ⟨rfl, rfl⟩ := I.injective hc hc'
        rfl) (by
        intro i v _ hv
        obtain ⟨c, y, z, hic, hc, rfl⟩ := (hψ i v).mp hv
        obtain ⟨y', z', hy, hz, hc'⟩ := hC c (hF.output_mem_of_pairMember hic)
        obtain ⟨rfl, rfl⟩ := I.injective hc hc'
        cases k <;> assumption)
    exact ⟨G, hG, fun i c y z hic hc => (hg i _).mpr
      ⟨hF.input_mem_of_pairMember hic, (hψ i _).mpr ⟨c, y, z, hic, hc, rfl⟩⟩⟩
  obtain ⟨G, hG, hg⟩ := project false
  obtain ⟨H, hH, hh⟩ := project true
  exact ⟨G, H, hG, hH, fun i c y z hic hc => ⟨hg i c y z hic hc, hh i c y z hic hc⟩⟩

end YesMetaZFC.SetTheory.ZF
