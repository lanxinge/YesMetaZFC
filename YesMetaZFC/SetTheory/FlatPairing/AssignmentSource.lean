import YesMetaZFC.SetTheory.FlatPairing.SequenceSource

/-! # 平坦赋值更新的源内解释

更新方程只引用旧图、新图和指定坐标；所有实际相关对象均由这两张图回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω ν X : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hωX : M.mem ω X)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l X (Nonempty.intro (Subtype.mk ω hωX))
local notation "J" => fp_rank_interpretation_l I hZF hω hV hωX

theorem rt_fp_update_l (f i x g : (N).Domain) :
    Senv_update_d J f i x g ↔ Senv_update_d K f.val i.val x.val g.val := by
  have entry := rt_fp_entry_l I hZF hω hV hωX
  have eq (a b : (N).Domain) : a.val = b.val ↔ a = b := ⟨Subtype.ext, congrArg Subtype.val⟩
  constructor
  · rintro ⟨rel, update⟩
    refine ⟨(rt_fp_relation_l I hZF hω hV hωX g).mp rel, fun j y => ⟨?_, ?_⟩⟩
    · intro h
      have jy := rt_fp_coordinates_l I hZF hω hV g.property h
      let j' : (N).Domain := ⟨j, jy.1⟩
      let y' : (N).Domain := ⟨y, jy.2⟩
      rcases (update j' y').mp ((entry j' y' g).mpr h) with ⟨ji, yx⟩ | ⟨ji, h⟩
      · exact Or.inl ⟨congrArg Subtype.val ji, congrArg Subtype.val yx⟩
      · exact Or.inr ⟨fun h => ji (Subtype.ext h), (entry j' y' f).mp h⟩
    · rintro (⟨rfl, rfl⟩ | ⟨ji, h⟩)
      · exact (entry i x g).mp ((update i x).mpr (Or.inl ⟨rfl, rfl⟩))
      · have jy := rt_fp_coordinates_l I hZF hω hV f.property h
        let j' : (N).Domain := ⟨j, jy.1⟩
        let y' : (N).Domain := ⟨y, jy.2⟩
        exact (entry j' y' g).mp ((update j' y').mpr
          (Or.inr ⟨fun e => ji (congrArg Subtype.val e), (entry j' y' f).mpr h⟩))
  · rintro ⟨rel, update⟩
    refine ⟨(rt_fp_relation_l I hZF hω hV hωX g).mpr rel, fun j y => ?_⟩
    exact (entry j y g).trans ((update j.val y.val).trans (or_congr
      (and_congr (eq j i) (eq y x)) (and_congr (not_congr (eq j i)) (entry j y f).symm)))

end YesMetaZFC.SetTheory.Internal
