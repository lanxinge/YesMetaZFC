import YesMetaZFC.SetTheory.LargeCardinal.IterationStep

/-! # 指定扩展器的实际类型伸展

先取同一实际超幂中的集合像，再按目标查询域投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Et_stretch_d (hZF : M.Models ZF) (ω κ L F X R t D v : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ b d N S i t', Smem_d I b X R ∧ Smem_d I d N S ∧ It_ultra_d hZF ω κ L F b d i ∧
    Rd_entry_d t t' i ∧ ∀ p, M.mem p v ↔ M.mem p D ∧ M.mem p t'

end YesMetaZFC.SetTheory.LargeCardinal
