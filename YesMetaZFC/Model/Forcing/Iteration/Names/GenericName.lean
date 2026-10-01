import YesMetaZFC.Model.Forcing.Iteration.Names.Inclusion
import YesMetaZFC.Model.Forcing.Iteration.Names.Generic

/-! # 沿阶段包含保持名称被泛型接受

早期滤子名称只使用旧条件权重，因而是后期滤子名称的实际子名称。
原成员力迫的阶段传输给出任意后期加强上的接受力迫。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_gname_force_l (hZF : M.Models ZF) {α B R D V b γ δ p q τ}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hp : M.mem p B) (hq : Below_d M D V D q p)
    (hγ : Gname_d (M := M) B b γ) (hδ : Gname_d (M := M) D b δ)
    (hτ : Name_d M B τ) (hf : Mem_force_d M B R B p τ γ) : Mem_force_d M D V D q τ δ := by
  have hh := (regular_mem_l L τ γ).1 p q (k.mem p hp) hq
    ((row_mem_force_l hZF O L k hp hτ hγ.1).mp hf)
  refine ⟨hq.1, fun r hr => ?_⟩
  obtain ⟨s, t, a, hsr, hta, hsa, he⟩ := hh.2 r hr
  obtain ⟨ha, hat⟩ := (hγ.2 t a).mp hta
  exact ⟨s, t, a, hsr, (hδ.2 t a).mpr ⟨k.mem a ha, hat⟩, hsa, he⟩

end YesMetaZFC.Model.Forcing.Internal
