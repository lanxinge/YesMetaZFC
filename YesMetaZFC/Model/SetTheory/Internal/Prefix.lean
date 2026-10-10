import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 公式程序扩张与真值前缀

追加指令不改变旧行的真值。证明直接限制实际递归表，并用每步只读取当前
指令的性质搬运递归方程；不对外部可解码的程序另设一套求值。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_prefix_subset_l {ω n F m G} (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G)
    (h : M.IsRestrictionOf I F G n) : M.MemberSubset n m := by
  intro i hi
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 i).mp hi
  exact (hG.2.1.2.2 i).mpr ⟨c, ((h.2 i c).mp hc).2⟩

theorem sfm_append_prefix_l (hZF : M.Models ZF) {ω n F c G} (hF : Sfm_d I ω n F)
    (h : ∀ i a, M.PairMember I i a G ↔ M.PairMember I i a F ∨ (i = n ∧ a = c)) :
    M.IsRestrictionOf I F G n := by
  refine ⟨hF.2.1.2.1.1, fun i a => ?_⟩
  constructor
  · exact fun hi => ⟨(hF.2.1.2.2 i).mpr ⟨a, hi⟩, (h i a).mpr (Or.inl hi)⟩
  · rintro ⟨hi, ha⟩
    rcases (h i a).mp ha with ha | ⟨rfl, _⟩
    · exact ha
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) _ hi).elim

theorem seval_prefix_l (hE : Extensional M) {ω X R E n F m G H P}
    (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G) (hFG : M.IsRestrictionOf I F G n)
    (hH : Seval_d I X R E G m H) (hP : M.IsRestrictionOf I P H n) : Seval_d I X R E F n P := by
  have hnm := sfm_prefix_subset_l I hF hG hFG
  refine ⟨⟨hF.2.1.1, hP.isSetFunction hH.1.2.1, hP.isDomainOf hH.1.2.2 hnm⟩, ?_⟩
  intro i hi Y hY
  obtain ⟨Q, hQ, hStep⟩ := hH.2 i (hnm i hi) Y (((hP.2 i Y).mp hY).2)
  have hd := (hH.restriction (hnm i hi) hQ).1.2.2
  refine ⟨Q, hP.trans hQ (hF.2.1.1.transitive i hi), fun f => (hStep f).trans ?_⟩
  apply and_congr_right
  intro _
  have he : ∀ j c, M.IsDomainOf I j Q → (M.PairMember I j c G ↔ M.PairMember I j c F) := by
    intro j c hj
    have hj := hj.eq hE hd
    subst j
    exact ⟨fun hc => (hFG.2 i c).mpr ⟨hi, hc⟩, fun hc => ((hFG.2 i c).mp hc).2⟩
  exact exists_congr fun j => exists_congr fun c => and_congr_right fun hj =>
    and_congr (he j c hj) Iff.rfl

/-- 旧公式在任意合法程序扩张中的满足关系逐赋值不变。 -/
theorem ssat_prefix_l (hZF : M.Models ZF) {ω X R E n F m G k}
    (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G) (hFG : M.IsRestrictionOf I F G n)
    (hk : M.mem k n) (f : M.Domain) : Ssat_d I X R E F n k f ↔ Ssat_d I X R E G m k f := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G hG.2.1.1
  obtain ⟨P, hP⟩ := ZF.exists_restriction hZF I H n
  have hp := seval_prefix_l I hZF.1 hF hG hFG hH hP
  obtain ⟨Y, hY⟩ := (hp.1.2.2 k).mp hk
  exact (ssat_value_l I hZF hp hY f).trans
    (ssat_value_l I hZF hH (((hP.2 k Y).mp hY).2) f).symm

end YesMetaZFC.SetTheory.Internal
