import YesMetaZFC.Model.SetTheory.Internal.EmbeddingSource
import YesMetaZFC.Model.SetTheory.ProjectEmbedding

/-! # 原内部初等图的实际模型映射

从已实现的全内部初等图读取逐点映射，并由原编译器得到所有 Project
公式的初等性。选择只位于存在命题中，不导出不可计算数据实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_d.project_l (hZF : M.Models ZF) {ω c d X Y R S j : M.Domain} (hw : M.IsOmega ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y j) :
    ∃ f : (smdl_structure_l I (R := R) mx.2.1).Domain → (smdl_structure_l I (R := S) my.2.1).Domain,
      Pe_d f ∧ ∀ x, M.PairMember I x.val (f x).val j := by
  have values (x : (smdl_structure_l I (R := R) mx.2.1).Domain) :
      ∃ y : (smdl_structure_l I (R := S) my.2.1).Domain, M.PairMember I x.val y.val j := by
    obtain ⟨y, hy, xy⟩ := map.1.1.2.2 x.val x.property
    exact ⟨⟨y, hy⟩, xy⟩
  obtain ⟨f, values⟩ := Classical.axiomOfChoice values
  exact ⟨f, fun φ hc ρ => smap_source_l I hZF hw mx my map φ hc ρ (image_env_l f ρ)
    (fun i => values (ρ.bound i)), values⟩

end YesMetaZFC.SetTheory.Internal
