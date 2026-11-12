import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement

/-! # 下降递归的前驱一致性

两张图同时保留原支撑秩段、像支撑秩段和支撑端点。严格递增的支撑使
较早的一致性经过下一步继续成立；有限幂的一致性直接由这些实际秩段推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Pn_agree_d (X Y π N Z σ ρ φ : M.Domain) : Prop where
  source_left : M.TransitiveSet X
  target_left : M.TransitiveSet Y
  source_right : M.TransitiveSet N
  target_right : M.TransitiveSet Z
  source_limit : M.IsLimitOrdinal ρ
  target_limit : M.IsLimitOrdinal φ
  source_rank : ∃ W, M.mem W X ∧ M.mem W N ∧ Vr_d X ρ W ∧ Vr_d N ρ W ∧
    ∀ x y, M.mem x W → (Rd_entry_d x y π ↔ Rd_entry_d x y σ)
  target_rank : ∃ V, M.mem V Y ∧ M.mem V Z ∧ Vr_d Y φ V ∧ Vr_d Z φ V
  left_end : Rd_entry_d ρ φ π
  right_end : Rd_entry_d ρ φ σ

variable (hZF : M.Models ZF)
include hZF

/-- 相邻步提供的同一实际秩段，可传给每一个严格较早的前驱。 -/
theorem Pn_agree_d.trans_l {X Y π N Z σ D P τ ρ φ μ ψ : M.Domain}
    (a : Pn_agree_d X Y π N Z σ ρ φ) (b : Pn_agree_d N Z σ D P τ μ ψ)
    (hρ : M.mem ρ μ) (hφ : M.mem φ ψ) : Pn_agree_d X Y π D P τ ρ φ := by
  have transfer {A B L C α W} (hA : M.TransitiveSet A) (hB : M.TransitiveSet B)
      (limit : M.IsLimitOrdinal L) (hα : M.mem α L) (hC : M.mem C A) (hC' : M.mem C B)
      (ca : Vr_d A L C) (cb : Vr_d B L C) (hW : M.mem W A) (wa : Vr_d A α W) :
      M.mem W B ∧ Vr_d B α W ∧ M.MemberSubset W C := by
    obtain ⟨hw, rank⟩ := ca.rank_l hZF hA hC limit (ca.ordinal_subset_l hZF hA hC α hα) hW wa
    exact ⟨hB C hC' W hw, cb.of_rank_l hB hC' hw rank, (ca.transitive_l hA hC) W hw⟩
  obtain ⟨W, wx, wn, xw, nw, maps⟩ := a.source_rank
  obtain ⟨U, un, ud, nu, du, maps'⟩ := b.source_rank
  obtain ⟨wd, dw, wu⟩ := transfer a.source_right b.source_right b.source_limit hρ un ud nu du wn nw
  obtain ⟨V, vy, vz, yv, zv⟩ := a.target_rank
  obtain ⟨C, cz, cp, zc, pc⟩ := b.target_rank
  obtain ⟨vp, pv, _⟩ := transfer a.target_right b.target_right b.target_limit hφ cz cp zc pc vz zv
  exact ⟨a.source_left, a.target_left, b.source_right, b.target_right, a.source_limit, a.target_limit,
    ⟨W, wx, wd, xw, dw, fun x y hx => (maps x y hx).trans (maps' x y (wu x hx))⟩,
    ⟨V, vy, vp, yv, pv⟩, a.left_end,
    (maps' ρ φ (nu.ordinal_subset_l hZF b.source_left un ρ hρ)).mp a.right_end⟩

/-- 复制需要的两个有限幂前提均从前驱的实际共同秩段读取。 -/
theorem Pn_agree_d.copy_l {ω κ κ' K K' K₀ K₁ X R Y S π N R₀ Z R₁ σ ρ φ : M.Domain}
    (a : Pn_agree_d X Y π N Z σ ρ φ)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S) (target' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₁ Z R₁)
    (hκ : M.mem κ ρ) (hκ' : M.mem κ' φ) :
    Ea_agree_d ω κ X N ∧ Ea_agree_d ω κ' Y Z ∧ Ea_maps_d ω κ X π σ := by
  obtain ⟨W, wx, wn, xw, nw, maps⟩ := a.source_rank
  have hκW := xw.ordinal_subset_l hZF a.source_left wx κ hκ
  have left := source.rank_agree_l hZF wx xw a.source_limit hκW
  have right := owner.rank_agree_l hZF wn nw a.source_limit hκW
  obtain ⟨V, vy, vz, yv, zv⟩ := a.target_rank
  have hκV := yv.ordinal_subset_l hZF a.target_left vy κ' hκ'
  have left' := target.rank_agree_l hZF vy yv a.target_limit hκV
  have right' := target'.rank_agree_l hZF vz zv a.target_limit hκV
  exact ⟨fun n D A hn hd sub => (left n D A hn hd sub).symm.trans (right n D A hn hd sub),
    fun n D A hn hd sub => (left' n D A hn hd sub).symm.trans (right' n D A hn hd sub),
    fun n D A B hn hd hA sub hAB => (maps A B ((left n D A hn hd sub).mpr hA)).mp hAB⟩

/-- 新的较高共同秩段保留每个较早支撑处的实际覆盖和缺失见证。 -/
theorem Pn_agree_d.strength_l {X Y π N Z σ μ ψ A ρ : M.Domain}
    (a : Pn_agree_d X Y π N Z σ μ ψ) (hρ : M.mem ρ μ)
    (h : Es_strength_d A ρ X) : Es_strength_d A ρ N := by
  obtain ⟨W, wx, wn, xw, nw, _⟩ := a.source_rank
  refine ⟨fun β hβ x hx sub => a.source_right W wn x ?_, ?_⟩
  · exact xw.subset_mem_l a.source_left wx
      (xw.ordinal_subset_l hZF a.source_left wx β (a.source_limit.1.transitive ρ hρ β hβ)) (h.1 β hβ x hx sub) sub
  · obtain ⟨x, hx, sub, missing⟩ := h.2
    exact ⟨x, hx, sub, fun hxn => missing (a.source_left W wx x
      (nw.subset_mem_l a.source_right wn (nw.ordinal_subset_l hZF a.source_right wn ρ hρ) hxn sub))⟩

/-- 原树在临界点上的一致性排除临界点越过任何仍有缺失见证的较早支撑。 -/
theorem ea_critical_bound_l {ω κ ρ K X R K' Y S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (agree : Ea_agree_d ω κ X Y) (hκ : M.IsOrdinal κ) (hρ : M.IsOrdinal ρ)
    (missing : ∃ x, M.mem x X ∧ M.MemberSubset x ρ ∧ ¬ M.mem x Y) : M.mem κ ρ := by
  obtain ⟨x, hx, sub, no⟩ := missing
  rcases hκ.trichotomy hZF.1 hρ (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) κ ρ) with eq | lt | gt
  · exact (no (agree.subset_l.set_l hZF source target hx (fun y hy => (eq y).mpr (sub y hy)))).elim
  · exact lt
  · exact (no (agree.subset_l.set_l hZF source target hx (fun y hy => hκ.transitive ρ gt y (sub y hy)))).elim

end YesMetaZFC.SetTheory.LargeCardinal
