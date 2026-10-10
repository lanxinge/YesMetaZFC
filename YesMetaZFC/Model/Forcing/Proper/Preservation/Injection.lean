import YesMetaZFC.Model.Forcing.Proper.Preservation.Cover

/-! # proper 力迫中的旧集合单射反射

将旧集合的规范名称送入通用可数覆盖构造。正条件下的规范名称覆盖反射为
真实旧集合的包含关系，因而直接取得地模型中的可数性见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 旧集合到旧 ω 的实际单射力迫，必已由地模型中的可数性见证实现。 -/
theorem proper_injection_reflect_l {ω b X t w f p} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z)
    (hb : M.mem b B) (hp : Below_d M B R z p b) (ht : Check_d M b X t) (hw : Check_d M b ω w)
    (hf : Inj_name_d M B R z p t w f) : M.CardinalLessOrEqual I X ω := by
  obtain ⟨q, hqp, A, s, _, ha, hs, h⟩ := proper_name_cover_l O hZFC hω hPr hb hp ht hw hf
  have hXA := check_cover_reflect_l O hZF hb ht hs (below_trans_l O hb hqp hp) h
  obtain ⟨g, hg⟩ := ZF.exists_inclusionInjection hZF I hXA
  obtain ⟨j, hj⟩ := ha
  exact ZF.exists_compositionInjection hZF I hg hj

end YesMetaZFC.Model.Forcing.Internal
