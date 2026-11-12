import YesMetaZFC.SetTheory.CumulativeRelative

/-! # 子集封闭切片中的秩历史完整读取

相对历史已经给出全部递归见证。切片之外的对象既不能属于已有层值，
也不能成为已有层值的子集，故同一历史满足全称证书；这里只使用 KP。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Vr_d.absolute_l (hKP : M.Models KP) {Z α V : M.Domain}
    (trans : M.TransitiveSet Z) (member : M.mem V Z)
    (closed : ∀ A B, M.mem A Z → M.MemberSubset B A → M.mem B Z)
    (rank : Vr_d Z α V) : V_d (kp_pair_l hKP) α V := by
  obtain ⟨B,F,hB,_,cert⟩ := rank
  have base := cert V member
  apply vc_sound_l hKP (B := B) (F := F)
  intro t
  by_cases ht : M.mem t Z
  · exact cert t ht
  · have outside β W (hW : M.mem W Z) : Vc_step_d β B F W t := by
      refine iff_of_false (fun hx => ht (trans W hW t hx)) ?_
      rintro ⟨γ,_,U,hU,_,sub⟩
      exact ht (closed U t (trans B hB U hU) sub)
    exact ⟨base.1,base.2.1,fun β _ W hW _ => outside β W (trans B hB W hW),outside α V member⟩

end YesMetaZFC.SetTheory
