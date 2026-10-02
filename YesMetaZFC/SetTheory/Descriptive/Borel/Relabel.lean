import YesMetaZFC.SetTheory.Descriptive.Borel.Operations

/-! # Borel 码的内部叶标签映射

沿实际标签函数图复合旧叶函数，保留原来的良基运算树。求值对应直接复用
同一个真值集；本接口用于下面的实数对角嵌入。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_relabel_l (hZF : M.Models ZF) {ω A S Q c H}
    (hH : M.IsSetFunctionFromTo I H S Q) (hc : Bcode_d I ω A S c) :
    ∃ d, Bcode_d I ω A Q d ∧ ∀ x y,
      (∀ s t, M.mem s S → M.PairMember I s t H → (M.MemberSubset t y ↔ M.MemberSubset s x)) →
      (Bsat_d I ω A Q d y ↔ Bsat_d I ω A S c x) := by
  obtain ⟨T, R, N, F, hp, hc⟩ := hc
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) T Q
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 4))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have hφ a t : φ.denote ρ a t ↔ ∃ s, M.PairMember I a s F ∧ M.PairMember I s t H := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨G, hG, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair a t : M.PairMember I a t G ↔ ∃ s, M.PairMember I a s F ∧ M.PairMember I s t H := by
    refine ((he a t).trans (and_congr_right fun _ => and_congr_right fun _ => hφ a t)).trans
      ⟨fun h => h.2.2, fun ⟨s, hs, ht⟩ => ?_⟩
    exact ⟨(hW a).mpr (Or.inl (hc.leaf a s hs).1), (hW t).mpr (Or.inr (hH.output_mem_of_pairMember ht)), s, hs, ht⟩
  have fn : M.IsSetFunction I G := by
    refine ⟨hG.1, fun a t u ht hu => ?_⟩
    obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
    obtain ⟨r, hr, hu⟩ := (pair a u).mp hu
    exact hH.1.2 s t u ht (hc.leaf_fn.2 a r s hr hs ▸ hu)
  have dom a : (∃ t, M.PairMember I a t G) ↔ ∃ s, M.PairMember I a s F := by
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨s, hs, _⟩ := (pair a t).mp ht
      exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨t, _, ht⟩ := hH.2.2 s (hc.leaf a s hs).2.1
      exact ⟨t, (pair a t).mpr ⟨s, hs, ht⟩⟩
  have hg : Btree_d I ω A Q T R N G := by
    refine ⟨hc.tree, hc.edges, hc.wf, hc.root, hc.neg_sub, fn, ?_, hc.neg⟩
    intro a t ht
    obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
    have leaf := hc.leaf a s hs
    exact ⟨leaf.1, hH.output_mem_of_pairMember ht, leaf.2.2⟩
  obtain ⟨d, hd⟩ := bpack_exists_l I T R N G
  refine ⟨d, ⟨T, R, N, G, hd, hg⟩, fun x y map => ?_⟩
  have lit a : Blit_d I G y a ↔ Blit_d I F x a := by
    constructor
    · rintro ⟨t, ht, hty⟩
      obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
      exact ⟨s, hs, (map s t (hc.leaf a s hs).2.1 ht).mp hty⟩
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨t, _, ht⟩ := hH.2.2 s (hc.leaf a s hs).2.1
      exact ⟨t, (pair a t).mpr ⟨s, hs, ht⟩, (map s t (hc.leaf a s hs).2.1 ht).mpr hsx⟩
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have hv' : Bsem_d I T R N G y V := by
    obtain ⟨L, U, hL, hU, hV⟩ := hv
    exact ⟨L, U, fun a => (hL a).trans (and_congr_right fun _ => (lit a).symm),
      fun a => (hU a).trans (and_congr_right fun _ =>
        and_congr Iff.rfl (not_congr (dom a).symm)), hV⟩
  obtain ⟨z, hz, _⟩ := hc.root
  exact (bsat_root_l I hZF hd hg hv' hz).trans (bsat_root_l I hZF hp hc hv hz).symm

end YesMetaZFC.SetTheory.Descriptive
