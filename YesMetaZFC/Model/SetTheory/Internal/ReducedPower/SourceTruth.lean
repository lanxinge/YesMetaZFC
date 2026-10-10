import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSyntax
import YesMetaZFC.Model.SetTheory.Internal.PointwiseTruth

/-! # 源内真值逆像的超滤读取

只对实际容许的真值集合使用向上封闭与二择。逻辑或非由三个真值集合的
精确成员方程给出，不把背景中的任意真值逆像当作源中集合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_holds_member_l {b D X R E F n r U a P A} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hs : ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p) :
    M.mem A U ↔ Pe_holds_d I b D X R E F n r U a := by
  refine ⟨fun h => ⟨A, h, fun p hp => ((hs p).mp hp).2⟩, ?_⟩
  rintro ⟨B, hB, hb⟩
  exact hU.upward B A hB hA (fun p hp => (hs p).mpr ⟨hU.base.bounds B hB p hp, hb p hp⟩)

theorem pe_holds_nor_l {b D X R E F n r i j U a P A B C} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hB : M.mem B P) (hC : M.mem C P)
    (hsA : ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n i a p)
    (hsB : ∀ p, M.mem p B ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n j a p)
    (hsC : ∀ p, M.mem p C ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p)
    (h : ∀ p, M.mem p D → (Pe_sat_d I b D X R E F n r a p ↔
      ¬ (Pe_sat_d I b D X R E F n i a p ∨ Pe_sat_d I b D X R E F n j a p))) :
    Pe_holds_d I b D X R E F n r U a ↔ ¬ (Pe_holds_d I b D X R E F n i U a ∨ Pe_holds_d I b D X R E F n j U a) := by
  have spec p : M.mem p C ↔ M.mem p D ∧ ¬ (M.mem p A ∨ M.mem p B) := by
    by_cases hp : M.mem p D
    · simpa only [hsC p, hsA p, hsB p, hp, true_and] using h p hp
    · simp only [hsC p, hp, false_and]
  exact (pe_holds_member_l I hU hC hsC).symm.trans ((hU.nor_l hA hB hC spec).trans
    (not_congr (or_congr (pe_holds_member_l I hU hA hsA) (pe_holds_member_l I hU hB hsB))))

end YesMetaZFC.SetTheory.Internal
