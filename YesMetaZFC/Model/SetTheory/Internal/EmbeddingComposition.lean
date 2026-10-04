import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding

/-! # 实际内部初等映射的复合

复合图由替代构造，中间赋值由图复合构造；两次读取同一个内部公式码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smap_comp_l (hZF : M.Models ZF) {ω c d e X Y Z j k : M.Domain}
    (h : Smap_d I ω c d X Y j) (g : Smap_d I ω d e Y Z k) : ∃ l, Smap_d I ω c e X Z l ∧
      ∀ x z, M.PairMember I x z l ↔ M.mem x X ∧ ∃ y, M.PairMember I x y j ∧ M.PairMember I y z k := by
  obtain ⟨l, hl, spec⟩ := ZF.exists_compositionFunction hZF I h.1.1 g.1.1
  have inj x y z (hx : M.PairMember I x z l) (hy : M.PairMember I y z l) : x = y := by
    obtain ⟨_, a, hxa, haz⟩ := (spec x z).mp hx
    obtain ⟨_, b, hyb, hbz⟩ := (spec y z).mp hy
    have eq := g.1.2 a b z haz hbz
    exact h.1.2 x y b (eq ▸ hxa) hyb
  obtain ⟨C, hC, read⟩ := h.2
  obtain ⟨D, hD, next⟩ := g.2
  refine ⟨l, ⟨⟨hl, inj⟩, C, hC, fun a f u ha hf hu hfu => ?_⟩, spec⟩
  obtain ⟨v, hv, assign⟩ := smap_assign_exists_l I hZF h.1.1 hf
  have compose : Smap_assign_d I ω k v u := by
    intro i hi y z hiy hyz
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨y', _, hxy⟩ := h.1.1.2.2 x hx
    have eq := hv.1.2 i y' y (assign i hi x y' hix hxy) hiy
    exact hfu i hi x z hix ((spec x z).mpr ⟨hx, y, eq ▸ hxy, hyz⟩)
  exact (read a f v ha hf hv assign).trans (next a v u ((hD a).mpr ((hC a).mp ha)) hv hu compose)

end YesMetaZFC.SetTheory.Internal
