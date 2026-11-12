import YesMetaZFC.SetTheory.LargeCardinal.Game.RawArchive
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax

/-! # 十一项原档案上的实际父边几何

两端保存码仍属于各自原模型。继续边只搬运同一旧树、旧长度及三图，
再读取新模型中的实际重启方程；重置边在保存轮自己的空集处重新开始。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_raw_archive_step_d (I : kpair_convention_l.Interpretation M)
    (s t : Tg_raw_archive_row_d M.Domain) (j : M.Domain) : Prop :=
  ∃ v w : Fin 54 → M.Domain,
    Tg_saved_code_d s.X s.R s.w s.U s.q v ∧ Tg_saved_code_d t.X t.R t.w t.U t.q w ∧
    ∃ a : Fin 5 → M.Domain,
      (∀ i, M.PairMember I (v ([19,22,40,41,42].get i)) (a i) j) ∧
      Tg_restart_link_d I t.X t.R a w

def Tg_raw_archive_reset_d (I : kpair_convention_l.Interpretation M)
    (s : Tg_raw_archive_row_d M.Domain) (S j : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d s.X s.R s.w s.U s.q v ∧
    M.PairMember I S (v 19) j ∧ v 22 = v 17 ∧ v 40 = v 17 ∧ v 41 = v 17 ∧ v 42 = v 17

end YesMetaZFC.SetTheory.LargeCardinal
