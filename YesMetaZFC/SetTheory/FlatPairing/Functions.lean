import YesMetaZFC.SetTheory.FlatPairing.Source

/-! # 平坦函数图在秩初段中的绝对性

图成员的两个坐标由平坦配对的逆向秩界回收。于是函数性、精确定义域及值域
在实际秩初段内外一致，不对初段额外假设分离、替换或配对公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω ν X : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hωX : M.mem ω X)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l X (Nonempty.intro (Subtype.mk ω hωX))
local notation "J" => fp_rank_interpretation_l I hZF hω hV hωX
include hω hV

theorem rt_fp_coordinates_l {a b f : M.Domain} (hf : M.mem f X) (h : M.PairMember K a b f) :
    M.mem a X ∧ M.mem b X := by
  obtain ⟨p, code, hp⟩ := h
  exact ((fp_fixed_l hZF.1 hω).mp code).inverse_rank_l I hZF hω.1 hV
    (v_transitive_l I hV f hf p hp)

theorem rt_fp_entry_l (a b f : (N).Domain) :
    (N).PairMember J a b f ↔ M.PairMember K a.val b.val f.val := by
  constructor
  · rintro ⟨p, code, hp⟩
    exact ⟨p.val, (fp_fixed_l hZF.1 hω).mpr code, hp⟩
  · rintro ⟨p, code, hp⟩
    exact ⟨⟨p, v_transitive_l I hV f.val f.property p hp⟩, (fp_fixed_l hZF.1 hω).mp code, hp⟩

theorem rt_fp_relation_l (R : (N).Domain) : (N).IsSetRelation J R ↔ M.IsSetRelation K R.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, code⟩ := h ⟨p, v_transitive_l I hV R.val R.property p hp⟩ hp
    exact ⟨a.val, b.val, (fp_fixed_l hZF.1 hω).mpr code⟩
  · intro h p hp
    obtain ⟨a, b, code⟩ := h p.val hp
    have ab := ((fp_fixed_l hZF.1 hω).mp code).inverse_rank_l I hZF hω.1 hV p.property
    exact ⟨⟨a, ab.1⟩, ⟨b, ab.2⟩, (fp_fixed_l hZF.1 hω).mp code⟩

theorem rt_fp_function_l (f : (N).Domain) : (N).IsSetFunction J f ↔ M.IsSetFunction K f.val := by
  have entry := rt_fp_entry_l I hZF hω hV hωX
  constructor
  · rintro ⟨relation, functional⟩
    refine ⟨(rt_fp_relation_l I hZF hω hV hωX f).mp relation, fun a b c hab hac => ?_⟩
    have ab := rt_fp_coordinates_l I hZF hω hV f.property hab
    have ac := rt_fp_coordinates_l I hZF hω hV f.property hac
    exact congrArg Subtype.val (functional ⟨a, ab.1⟩ ⟨b, ab.2⟩ ⟨c, ac.2⟩
      ((entry _ _ f).mpr hab) ((entry _ _ f).mpr hac))
  · rintro ⟨relation, functional⟩
    exact ⟨(rt_fp_relation_l I hZF hω hV hωX f).mpr relation, fun a b c hab hac =>
      Subtype.ext (functional a.val b.val c.val ((entry a b f).mp hab) ((entry a c f).mp hac))⟩

theorem rt_fp_function_from_l (f A B : (N).Domain) :
    (N).IsSetFunctionFromTo J f A B ↔ M.IsSetFunctionFromTo K f.val A.val B.val := by
  have entry := rt_fp_entry_l I hZF hω hV hωX
  have trans := v_transitive_l I hV
  constructor
  · rintro ⟨hf, domain, total⟩
    refine ⟨(rt_fp_function_l I hZF hω hV hωX f).mp hf, fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
    · intro hx
      obtain ⟨y, hxy⟩ := (domain ⟨x, trans A.val A.property x hx⟩).mp hx
      exact ⟨y.val, (entry _ y f).mp hxy⟩
    · rintro ⟨y, hxy⟩
      have xy := rt_fp_coordinates_l I hZF hω hV f.property hxy
      exact (domain ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, (entry _ _ f).mpr hxy⟩
    · obtain ⟨y, hy, hxy⟩ := total ⟨x, trans A.val A.property x hx⟩ hx
      exact ⟨y.val, hy, (entry _ _ f).mp hxy⟩
  · rintro ⟨hf, domain, total⟩
    refine ⟨(rt_fp_function_l I hZF hω hV hωX f).mpr hf, fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
    · intro hx
      obtain ⟨y, hxy⟩ := (domain x.val).mp hx
      exact ⟨⟨y, (rt_fp_coordinates_l I hZF hω hV f.property hxy).2⟩, (entry _ _ f).mpr hxy⟩
    · rintro ⟨y, hxy⟩
      exact (domain x.val).mpr ⟨y.val, (entry _ _ f).mp hxy⟩
    · obtain ⟨y, hy, hxy⟩ := total x.val hx
      exact ⟨⟨y, trans B.val B.property y hy⟩, hy, (entry _ _ f).mpr hxy⟩

end YesMetaZFC.SetTheory.Internal
