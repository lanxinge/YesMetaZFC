import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode

/-! # 任意集合列的逐项复合结合律 -/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Fseq_recode_d.comp_l {f g h p q r : M.Domain}
    (first : Fseq_recode_d I f p q) (next : Fseq_recode_d I g q r) (comp : Fseq_recode_d I g f h) :
    Fseq_recode_d I h p r := by
  refine ⟨next.1,fun i z => ⟨?_,?_⟩⟩
  · intro iz
    obtain ⟨y,iy,yz⟩ := (next.2 i z).mp iz
    obtain ⟨x,ix,xy⟩ := (first.2 i y).mp iy
    exact ⟨x,ix,(comp.2 x z).mpr ⟨y,xy,yz⟩⟩
  · rintro ⟨x,ix,xz⟩
    obtain ⟨y,xy,yz⟩ := (comp.2 x z).mp xz
    exact (next.2 i z).mpr ⟨y,(first.2 i y).mpr ⟨x,ix,xy⟩,yz⟩

end YesMetaZFC.SetTheory
