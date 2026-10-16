import YesMetaZFC.Model.SetTheory.Internal.UniversalClosure
import YesMetaZFC.Model.SetTheory.Internal.Uniformization
import YesMetaZFC.Model.SetTheory.Internal.SourceSmall

/-! # 已实现源理论中的小定义域收集性质

定义从原收集模块移到共同依赖层；正则 Hχ、正则 Vδ 及原后继实例继续使用同一性质。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_uniform_d (ω X R D : M.Domain) : Prop :=
  ∀ E F n r i j f A, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem A X → M.MemberSubset A D →
    Scollect_d I X R E F n r i j f A X →
      ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f A C B

def Sc_collection_d (ω X R : M.Domain) : Prop :=
  ∀ D, M.mem D X → Sc_small_d X D → Sc_uniform_d I ω X R D

end YesMetaZFC.SetTheory.Internal
