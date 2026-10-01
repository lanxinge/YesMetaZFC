import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive
import YesMetaZFC.Model.Forcing.Iteration.Stage.Successor

/-! # 坐标追加与二步编码的传递绝对性

追加产生的唯一新有序对属于结果图；二步条件的两个坐标则由原有序对所界。
所有存在见证因此均在传递环境中，不需要该环境满足替换或幂集公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c H T : M.Domain} (hM : Smdl_d I c H T)
  (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y) (hH : M.TransitiveSet H)
local notation "L" => smdl_structure_l I (R := T) (And.left (And.right hM))
include hT hH

theorem smem_row_append_l (α t p s q : (L).Domain) :
    Row_append_d L α t p s q ↔ Row_append_d M α.val t.val p.val s.val q.val := by
  constructor
  · rintro (⟨hs, hq⟩ | ⟨hs, v, hv, hq⟩)
    · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val hq⟩
    · refine Or.inr ⟨(fun h => hs (Subtype.ext h)), v.val, (smem_kpair_l I hM hT hH v α s).mp hv, fun w => ?_⟩
      constructor
      · intro hw
        let w' : (L).Domain := ⟨w, hH q.val q.property w hw⟩
        exact ((hq w').mp ((smem_member_l I hM hT w' q).mpr hw)).elim
          (fun h => Or.inl ((smem_member_l I hM hT w' p).mp h)) (fun h => Or.inr (congrArg Subtype.val h))
      · rintro (hw | rfl)
        · let w' : (L).Domain := ⟨w, hH p.val p.property w hw⟩
          exact (smem_member_l I hM hT w' q).mp ((hq w').mpr (Or.inl ((smem_member_l I hM hT w' p).mpr hw)))
        · exact (smem_member_l I hM hT v q).mp ((hq v).mpr (Or.inr rfl))
  · rintro (⟨hs, hq⟩ | ⟨hs, v, hv, hq⟩)
    · exact Or.inl ⟨Subtype.ext hs, Subtype.ext hq⟩
    · let v' : (L).Domain := ⟨v, hH q.val q.property v ((hq v).mpr (Or.inr rfl))⟩
      refine Or.inr ⟨(fun h => hs (congrArg Subtype.val h)), v', (smem_kpair_l I hM hT hH v' α s).mpr hv, fun w => ?_⟩
      rw [smem_member_l I hM hT w q, smem_member_l I hM hT w p, hq w.val]
      exact or_congr Iff.rfl ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩

theorem smem_row_code_l (α t a q : (L).Domain) :
    Row_code_d L α t a q ↔ Row_code_d M α.val t.val a.val q.val := by
  constructor
  · rintro ⟨p, s, hps, hq⟩
    exact ⟨p.val, s.val, (smem_kpair_l I hM hT hH a p s).mp hps,
      (smem_row_append_l I hM hT hH α t p s q).mp hq⟩
  · rintro ⟨p, s, hps, hq⟩
    have hp := trans_kpair_l hH a.property hps
    let p' : (L).Domain := ⟨p, hp.1⟩
    let s' : (L).Domain := ⟨s, hp.2⟩
    exact ⟨p', s', (smem_kpair_l I hM hT hH a p' s').mpr hps,
      (smem_row_append_l I hM hT hH α t p' s' q).mpr hq⟩

end YesMetaZFC.Model.Forcing.Internal
