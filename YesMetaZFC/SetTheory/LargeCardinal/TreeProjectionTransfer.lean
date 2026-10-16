import YesMetaZFC.SetTheory.LargeCardinal.TreeProjection
import YesMetaZFC.Model.Forcing.Internal.Ground.TreePullback
import YesMetaZFC.Model.Forcing.Internal.Ground.HistoryTree
import YesMetaZFC.Model.Forcing.Internal.Ground.TreeRank

/-! # 旧实数的投影成员关系回传

固定旧 x，实际构造 T 的 x 截面。若地面没有见证，该树有序数秩；
秩与截面构造都沿成员满嵌入保持，故外模型也不可能给同一个 x 添加见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tp_left_d.image_l {Y A d : M.Domain} (left : Tp_left_d I Y A d) :
    Tp_left_d J (e Y) (e A) (e d) := by
  refine ⟨image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he left.1,
    fun v a => ⟨?_, ?_⟩⟩
  · intro va
    obtain ⟨p, x, px, rfl, rfl⟩ := (image_entries_l e he left.1.1.1 v a).mp va
    obtain ⟨hp, z, code⟩ := (left.2 p x).mp px
    exact ⟨(image_member_l e hi he).mpr hp, e z, image_kpair_l e he code⟩
  · rintro ⟨hv, z, code⟩
    obtain ⟨p, hp, rfl⟩ := (he Y v).mp hv
    obtain ⟨x, _, px⟩ := left.1.2.2 p hp
    obtain ⟨_, w, code'⟩ := (left.2 p x).mp px
    have eq := ((J).injective (image_kpair_l e he code') code).1
    exact eq ▸ (image_entries_l e he left.1.1.1 (e p) (e x)).mpr ⟨p, x, px, rfl, rfl⟩

theorem Tp_filter_d.image_l {ω Y A d F T K C : M.Domain}
    (left : Tp_left_d I Y A d) (space : Fseq_space_d I ω Y F) (filter : Tp_filter_d I d F T K C) :
    Tp_filter_d J (e d) (e F) (e T) (e K) (e C) := by
  obtain ⟨S, pull, inter⟩ := filter
  refine ⟨e S, image_tree_pullback_l hM hN e hi he left.1 space pull, fun s => ⟨?_, ?_⟩⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he C s).mp hs
    exact ⟨(image_member_l e hi he).mpr ((inter t).mp ht).1,
      (image_member_l e hi he).mpr ((inter t).mp ht).2⟩
  · rintro ⟨ht, hs⟩
    obtain ⟨t, hg, rfl⟩ := (he T s).mp ht
    exact (image_member_l e hi he).mpr ((inter t).mpr ⟨hg, (image_member_l e hi he).mp hs⟩)

theorem tp_projection_reflect_l {ω A Γ Y F T x : M.Domain} (hw : M.IsOmega ω)
    (hwN : N.IsOmega (e ω)) (dc : Dc_d I ω) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) (fx : M.IsSetFunctionFromTo I x ω A)
    (project : Tp_projection_d J (e ω) (e A) (e Y) (e F) (e T) (e x)) : Tp_projection_d I ω A Y F T x := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨H, hist⟩ := ZF.fseq_space_exists_l I hM hw A
  obtain ⟨d, left⟩ := tp_left_l I hM pair
  obtain ⟨K, cut⟩ := hg_section_exists_l hM H x
  obtain ⟨C, filter⟩ := tp_filter_l I hM d F T K
  have treeC := filter.tree_l I hM left space hist tree (hg_section_tree_l cut)
  obtain ⟨α, R, rank⟩ := tree_rank_l hM hw dc space treeC (by
    intro q fq branch
    obtain ⟨y, fy, qy⟩ := ZF.fseq_compose_l I hM left.1 fq
    have proj := (left.projection_l I hM fq).mp qy
    obtain ⟨bt, bk⟩ := (filter.branch_l I hM hw left space hist fq proj).mp branch
    have eq := (hg_section_branch_l hM hw hist cut fx fy).mp bk
    exact no ⟨q, fq, bt, eq ▸ proj⟩)
  have spaceN := image_fseq_l hM hN e hi he hw hwN space
  have histN := image_fseq_l hM hN e hi he hw hwN hist
  obtain ⟨q, fq, branch, proj⟩ := project
  have fxN := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fx
  have bk := (hg_section_branch_l hN hwN histN (image_hg_section_l e hi he cut) fxN fxN).mpr rfl
  have bc := ((filter.image_l hM hN e hi he left space).branch_l J hN hwN
    (left.image_l hM hN e hi he) spaceN histN fq proj).mpr ⟨branch, bk⟩
  exact (image_tree_rank_l hM hN e hi he rank).no_branch_l hN hwN spaceN
    (image_tree_l e hi he treeC) fq bc

end YesMetaZFC.SetTheory.LargeCardinal
