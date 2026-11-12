import YesMetaZFC.SetTheory.FlatPairing.Functions

/-! # 平坦递归图的定义域与限制在秩层中绝对

所有图坐标均由已经拥有的图回收；不增加源模型公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem rt_fp_domain_l (A F : (N).Domain) :
    (N).IsDomainOf J A F ↔ M.IsDomainOf K A.val F.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have trans := v_transitive_l I hW
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨y, hxy⟩ := (h ⟨x, trans A.val A.property x hx⟩).mp hx
      exact ⟨y.val, (entry _ y F).mp hxy⟩
    · rintro ⟨y, hxy⟩
      have xy := rt_fp_coordinates_l I hZF hω hW F.property hxy
      exact (h ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, (entry _ _ F).mpr hxy⟩
  · intro h x
    constructor
    · intro hx
      obtain ⟨y, hxy⟩ := (h x.val).mp hx
      exact ⟨⟨y, (rt_fp_coordinates_l I hZF hω hW F.property hxy).2⟩, (entry _ _ F).mpr hxy⟩
    · rintro ⟨y, hxy⟩
      exact (h x.val).mpr ⟨y.val, (entry x y F).mp hxy⟩

theorem rt_fp_restriction_l (P F A : (N).Domain) :
    (N).IsRestrictionOf J P F A ↔ M.IsRestrictionOf K P.val F.val A.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  constructor
  · rintro ⟨rel, cut⟩
    refine ⟨(rt_fp_relation_l I hZF hω hW hωY P).mp rel, fun x y => ⟨?_, ?_⟩⟩
    · intro hxy
      have xy := rt_fp_coordinates_l I hZF hω hW P.property hxy
      obtain ⟨hx, he⟩ := (cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((entry _ _ P).mpr hxy)
      exact ⟨hx, (entry _ _ F).mp he⟩
    · rintro ⟨hx, hxy⟩
      have xy := rt_fp_coordinates_l I hZF hω hW F.property hxy
      exact (entry _ _ P).mp ((cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mpr ⟨hx, (entry _ _ F).mpr hxy⟩)
  · rintro ⟨rel, cut⟩
    exact ⟨(rt_fp_relation_l I hZF hω hW hωY P).mpr rel, fun x y =>
      (entry x y P).trans ((cut x.val y.val).trans (and_congr_right fun _ => (entry x y F).symm))⟩

end YesMetaZFC.SetTheory.Internal
