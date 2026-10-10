import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Assignment

/-! # 原子真值与商关系的精确对应 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_holds_rel_l {D Q E U V R i j f g Z} (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (hV : M.IsSetFunctionFromTo I V D E) (hf : Fn0_d D Q f) (hg : Fn0_d D Q g)
    (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V j g)
    (hZ : ∀ v, M.mem v Z ↔ M.mem v E ∧ ∃ x y, M.PairMember I i x v ∧ M.PairMember I j y v ∧ M.PairMember I x y R) :
    Rp_holds_d I U V Z ↔ Rp_rel_d I Q U R f g := by
  constructor
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hv, hvZ⟩ := hA d hd
    obtain ⟨_, x, y, hx, hy, hxy⟩ := (hZ v).mp hvZ
    have hdx := (hF d (hU A hAU d hd) v hv x).mpr hx
    have hdy := (hG d (hU A hAU d hd) v hv y).mpr hy
    exact ⟨x, (hf.bound_l hdx).2, y, (hg.bound_l hdy).2, hdx, hdy, hxy⟩
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hvE, hv⟩ := hV.2.2 d (hU A hAU d hd)
    obtain ⟨x, _, y, _, hx, hy, hxy⟩ := hA d hd
    exact ⟨v, hv, (hZ v).mpr ⟨hvE, x, y, (hF d (hU A hAU d hd) v hv x).mp hx,
      (hG d (hU A hAU d hd) v hv y).mp hy, hxy⟩⟩

theorem rp_holds_eq_l {D Q E U V i j f g Z} (hU : ∀ A, M.mem A U → M.MemberSubset A D)
    (hV : M.IsSetFunctionFromTo I V D E) (hf : Fn0_d D Q f)
    (hF : Rp_column_d I D V i f) (hG : Rp_column_d I D V j g)
    (hZ : ∀ v, M.mem v Z ↔ M.mem v E ∧ ∃ x, M.PairMember I i x v ∧ M.PairMember I j x v) :
    Rp_holds_d I U V Z ↔ Rp_eq_d Q U f g := by
  constructor
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hv, hvZ⟩ := hA d hd
    obtain ⟨_, x, hx, hy⟩ := (hZ v).mp hvZ
    have hdx := (hF d (hU A hAU d hd) v hv x).mpr hx
    exact ⟨x, (hf.bound_l hdx).2, hdx, (hG d (hU A hAU d hd) v hv x).mpr hy⟩
  · rintro ⟨A, hAU, hA⟩
    refine ⟨A, hAU, fun d hd => ?_⟩
    obtain ⟨v, hvE, hv⟩ := hV.2.2 d (hU A hAU d hd)
    obtain ⟨x, _, hx, hy⟩ := hA d hd
    exact ⟨v, hv, (hZ v).mpr ⟨hvE, x, (hF d (hU A hAU d hd) v hv x).mp hx,
      (hG d (hU A hAU d hd) v hv x).mp hy⟩⟩

end YesMetaZFC.SetTheory.Internal
