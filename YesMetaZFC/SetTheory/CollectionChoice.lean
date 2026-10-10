import YesMetaZFC.SetTheory.DependentChoice

/-! # 集合指标上的无先验值域界选择

原收集公理先给出实际见证集合，原选择公理再把其中的关系单值化。
输出是模型中的函数图，不把外部选择函数当作模型内对象。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem collect_choice_l (hZFC : M.Models ZFC) {n} (φ : BinarySchema n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.denote ρ x y) :
    ∃ Y F, M.IsSetFunctionFromTo I F X Y ∧ ∀ x y, M.PairMember I x y F → φ.denote ρ x y := by
  obtain ⟨Y, hY⟩ := ZF.collection_exists_d (models_zf_l hZFC) φ ρ X ht
  obtain ⟨F, hF, hf⟩ := uniformize_formula_l I hZFC φ ρ hY
  exact ⟨Y, F, hF, hf⟩

end YesMetaZFC.SetTheory.ZFC
