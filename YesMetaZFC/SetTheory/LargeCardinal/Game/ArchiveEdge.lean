import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax

/-! # 原奇数边上的实际存档延伸

先读取两端真实存档，再沿同一原边搬运树、长度和三张图。
新长度及图的延伸方程在目标模型自己的关系中解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_archive_step_d (I : kpair_convention_l.Interpretation M)
    (s t : Tg_archive_row_d M.Domain) (j : M.Domain) : Prop :=
  ∃ v w : Fin 54 → M.Domain,
    Tg_saved_code_d s.X s.R s.w s.U s.q v ∧ Tg_saved_code_d t.X t.R t.w t.U t.q w ∧
    ∃ a : Fin 5 → M.Domain,
      (∀ i, M.PairMember I (v ([19,22,40,41,42].get i)) (a i) j) ∧
      Tg_restart_link_d I t.X t.R a w

def Tg_archive_reset_d (I : kpair_convention_l.Interpretation M)
    (t : Tg_archive_row_d M.Domain) (S j : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d t.X t.R t.w t.U t.q v ∧
    M.PairMember I S (v 19) j ∧ v 22 = v 17 ∧ v 40 = v 17 ∧ v 41 = v 17 ∧ v 42 = v 17

end YesMetaZFC.SetTheory.LargeCardinal
