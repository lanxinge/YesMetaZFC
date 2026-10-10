import YesMetaZFC.SetTheory.Descriptive.Space
import YesMetaZFC.Model.SetTheory.Internal.FiniteAssignment

/-! # 内部有限前缀与无限延拓

限制和延拓均为集合编码图。常值尾部复用已有赋值延拓，故不对外部长度递归，
也不选择逐项的宿主函数。图包含给出后续柱集的有界成员公式。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 函数图包含等价于在小函数定义域上的精确限制。 -/
theorem ds_restrict_iff_l {s f n X : M.Domain} (hs : M.IsSetFunctionFromTo I s n X)
    (hf : M.IsSetFunction I f) : M.IsRestrictionOf I s f n ↔ M.MemberSubset s f := by
  constructor
  · intro h p hp
    obtain ⟨i, x, hc⟩ := hs.1.1 p hp
    obtain ⟨q, hq, hqf⟩ := ((h.2 i x).mp ⟨p, hc, hp⟩).2
    exact (I.unique hc hq).symm ▸ hqf
  · intro h
    refine ⟨hs.1.1, fun i x => ⟨fun hx => ?_, fun ⟨hi, hx⟩ => ?_⟩⟩
    · exact ⟨hs.input_mem_of_pairMember hx, hx.elim fun p hp => ⟨p, hp.1, h p hp.2⟩⟩
    · obtain ⟨y, _, hy⟩ := hs.2.2 i hi
      have hyf : M.PairMember I i y f := hy.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
      exact hf.2 i y x hyf hx ▸ hy

/-- 每个内部自然数长度的前缀存在且唯一，并仍在原字母表内。 -/
theorem ds_prefix_l (hZF : M.Models ZF) {ω X f n} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hn : M.mem n ω) :
    ∃ s, M.IsSetFunctionFromTo I s n X ∧ M.IsRestrictionOf I s f n ∧
      ∀ t, M.IsRestrictionOf I t f n → t = s := by
  obtain ⟨s, hs⟩ := ZF.exists_restriction hZF I f n
  exact ⟨s, hs.isSetFunctionFromTo hf (hω.transitive hZF n hn), hs,
    fun t ht => ht.eq hZF.1 hs⟩

/-- 把有限列延拓为无限列；第一处新坐标可指定为任意字母。 -/
theorem ds_extend_l (hZF : M.Models ZF) {ω X s n a} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ M.IsRestrictionOf I s f n ∧ M.PairMember I n a f := by
  obtain ⟨f, he, hf⟩ := Internal.senv_fill_exists_l I hZF (ω := ω) hs ha
  have hr : M.IsRestrictionOf I s f n := by
    refine ⟨hs.1.1, fun i x => ⟨fun hx => ?_, fun ⟨hi, hx⟩ => ?_⟩⟩
    · have hi := hs.input_mem_of_pairMember hx
      exact ⟨hi, (he.2 i x).mpr ⟨hω.transitive hZF n hn i hi, Or.inl ⟨hi, hx⟩⟩⟩
    · exact ((he.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)
  exact ⟨f, hf, hr, (he.2 n a).mpr ⟨hn, Or.inr ⟨KP.mem_irrefl_d (ZF.modelsKP hZF) n, rfl⟩⟩⟩

/-- 两个不同的同域函数在某个内部坐标有不同值。 -/
theorem ds_differ_l (hE : Extensional M) {D X f g : M.Domain}
    (hf : M.IsSetFunctionFromTo I f D X) (hg : M.IsSetFunctionFromTo I g D X) (hne : f ≠ g) :
    ∃ i x y, M.mem i D ∧ M.PairMember I i x f ∧ M.PairMember I i y g ∧ x ≠ y := by
  apply Classical.byContradiction
  intro h
  apply hne
  apply hf.1.1.eq_of_pairMember_iff hE hg.1.1
  intro i x
  constructor
  · intro hx
    have hi := hf.input_mem_of_pairMember hx
    obtain ⟨y, _, hy⟩ := hg.2.2 i hi
    have e : x = y := Classical.byContradiction (fun e => h ⟨i, x, y, hi, hx, hy, e⟩)
    exact e.symm ▸ hy
  · intro hx
    have hi := hg.input_mem_of_pairMember hx
    obtain ⟨y, _, hy⟩ := hf.2.2 i hi
    have e : y = x := Classical.byContradiction (fun e => h ⟨i, y, x, hi, hy, hx, e⟩)
    exact e ▸ hy

/-- 同一无限列的较短前缀包含于较长前缀。 -/
theorem ds_prefix_mono_l {f s t n m X : M.Domain} (hs : M.IsSetFunctionFromTo I s n X)
    (ht : M.IsSetFunction I t) (hsf : M.IsRestrictionOf I s f n)
    (htf : M.IsRestrictionOf I t f m) (hnm : M.MemberSubset n m) : M.MemberSubset s t :=
  (ds_restrict_iff_l I hs ht).mp (htf.trans hsf hnm)

/-- 两个字母已足以使任意有限前缀具有两个不同的无限延拓。 -/
theorem ds_split_l (hZF : M.Models ZF) {ω X s n a b} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X)
    (ha : M.mem a X) (hb : M.mem b X) (hab : a ≠ b) :
    ∃ f g, M.IsSetFunctionFromTo I f ω X ∧ M.IsSetFunctionFromTo I g ω X ∧
      M.MemberSubset s f ∧ M.MemberSubset s g ∧ f ≠ g := by
  obtain ⟨f, hf, hsf, hfa⟩ := ds_extend_l I hZF hω hn hs ha
  obtain ⟨g, hg, hsg, hgb⟩ := ds_extend_l I hZF hω hn hs hb
  refine ⟨f, g, hf, hg, (ds_restrict_iff_l I hs hf.1).mp hsf,
    (ds_restrict_iff_l I hs hg.1).mp hsg, ?_⟩
  intro e
  subst g
  exact hab (hf.1.2 n a b hfa hgb)

end YesMetaZFC.SetTheory.Descriptive
