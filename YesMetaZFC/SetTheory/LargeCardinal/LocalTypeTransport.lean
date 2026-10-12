import YesMetaZFC.SetTheory.LargeCardinal.LocalIndiscerniblesLeast
import YesMetaZFC.Model.SetTheory.Internal.TypeMoveRead

/-! # 局部不可分辨序数间有限后继秩层的完整类型搬运

在固定 Vδ∪{δ} 上命名元组。空名字表示移动高度，其余名字仍是原集合常量；
所有内部有限长度、排列和重复均保留。两侧输出字面相同的 κ 型集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 指定有限后继秩层、实际元组及其完整类型共同构成搬运结果。 -/
def Li_finite_d (ω e δ ν k n E U D t : M.Domain) : Prop := M.mem k ω ∧ M.mem e k ∧ ∃ β A c R s,
  M.IsOrdinalAddition I β ν k ∧ V_d I β A ∧ Smem_d I c A R ∧
    Tn_assign_d e e ν E s ∧ Tt_realized_d I ω c A R n s δ U D t

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 一次生成固定名字域；随后任意内部有限后继层及名字列都自动取得同一完整类型。 -/
theorem Li_pair_d.finite_types_l {ω e γ W F δ ν μ : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) (band : M.IsOrdinalAddition Q γ δ ω)
    (hW : V_d Q γ W) (pool₀ : Tt_pool_d Q ω e W F) (hδν : M.mem δ ν)
    (h : Li_pair_d Q ω e W F ν μ) :
    ∃ C P Z, V_d Q δ C ∧ (∀ x, M.mem x P ↔ M.mem x C ∨ x = δ) ∧ Tn_names_d e P Z ∧
      ∀ κ k n E, M.mem κ δ → M.mem k ω → M.mem e k → M.mem n ω → Fn0_d n Z E →
        ∃ B U D t, V_d Q κ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧ Tt_pool_d Q ω n U D ∧
          Li_finite_d Q ω e δ ν k n E U D t ∧ Li_finite_d Q ω e δ μ k n E U D t := by
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hδ.1).limit_value (hω.isLimitOrdinal hZF) band
  have hδγ := (ZF.ordinalAddition_mem_iff hZF Q (hω.isOrdinal hZF) band).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  have wt := ZF.v_transitive_l Q hZF hW
  have hδW := ZF.v_ordinal_mem_l Q hZF hW hδγ
  have hωW := wt δ hδW ω hωδ
  obtain ⟨C, P, hC, hPW, params⟩ := tt_constants_exists_l hZF hW hγ hδγ
  have hCW := ZF.v_mem_l Q hZF hC hW hδγ
  have ct := ZF.v_transitive_l Q hZF hC
  have hωC := ZF.v_ordinal_mem_l Q hZF hC hωδ
  obtain ⟨Z, names⟩ := tn_names_exists_l hZF e P
  have hZW := names.rank_mem_l hZF hω hW hγ hωW heω hPW
  obtain ⟨G, seq⟩ := ZF.fseq_space_exists_l Q hZF hω Z
  have hGW := ZF.v_fseq_mem_l Q hZF hW hγ hω hωW hZW seq
  refine ⟨C, P, Z, hC, params, names, fun κ k n E hκδ hk hek hn column => ?_⟩
  have hEW := wt G hGW E ((seq E).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) column⟩)
  have ho := hω.members_areOrdinals hZF k hk
  have build (v : M.Domain) (hv : M.IsOrdinal v) (hδv : M.mem δ v) :
      ∃ β A c R s, M.IsOrdinalAddition Q β v k ∧ V_d Q β A ∧ Smem_d Q c A R ∧
        Tn_assign_d e e v E s ∧ Fn0_d n A s ∧ M.mem δ A ∧ M.mem κ A ∧
          M.MemberSubset C A ∧ M.MemberSubset ω β := by
    obtain ⟨β, sum, _⟩ := ZF.ordinalAddition_existsUnique hZF Q v ho
    have hβ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hv).1.2 _ _ ho sum
    have hvβ := (ZF.ordinalAddition_mem_iff hZF Q ho sum).mpr
      (Or.inr ⟨e, hek, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
    have hδβ := hβ.transitive v hvβ δ hδv
    obtain ⟨A, hA⟩ := ZF.v_exists_l Q hZF hβ
    have point := ZF.v_ordinal_mem_l Q hZF hA hδβ
    have sub := ZF.v_mono_l Q hZF hC hA (hβ.transitive δ hδβ)
    have empty : Fn0_d e A e := ⟨fun p hp => (he p hp).elim,
      fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
    obtain ⟨s, assign, tuple⟩ := tn_assign_exists_l hZF (Structure.IsOrdinal.of_no_members he) empty
      (ZF.v_ordinal_mem_l Q hZF hA hvβ) (fun x hx => ((params x).mp hx).elim (sub x) (fun eq => eq.symm ▸ point)) names column
    obtain ⟨c, R, model⟩ := smdl_membership_l Q hZF ⟨δ, point⟩
    exact ⟨β, A, c, R, s, sum, hA, model, assign, tuple, point,
      ZF.v_ordinal_mem_l Q hZF hA (hβ.transitive δ hδβ κ hκδ), sub,
      fun i hi => hβ.transitive δ hδβ i (hδ.1.transitive ω hωδ i hi)⟩
  have hν := h.1
  have hμ := h.2.1
  obtain ⟨β, A, c, R, s, sum, hA, model, assign, tuple, point, hκA, ca, hων⟩ := build ν hν hδν
  obtain ⟨β', A', c', R', s', sum', hA', model', assign', tuple', point', hκA', ca', hωμ⟩ :=
    build μ hμ (hμ.transitive ν h.2.2.1 δ hδν)
  obtain ⟨B, U, hB, hUC, constants⟩ := tt_constants_exists_l hZF hC hδ hκδ
  obtain ⟨D, pool⟩ := tt_pool_exists_l Q hZF hω n U
  have hDC := pool.rank_mem_l hZF hω hC hδ hωC hn hUC
  obtain ⟨t, truth, _⟩ := tt_truth_exists_l Q hZF ω c n s δ D
  have htW := wt C hCW t (ZF.v_subset_mem_l Q hZF hC hDC (fun p hp => ((truth p).mp hp).1))
  have ha : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W :=
    Fin.cases hωW (Fin.cases hCW (Fin.cases (wt δ hδW κ hκδ)
      (Fin.cases (wt ω hωW k hk) (Fin.cases (wt ω hωW n hn) (Fin.cases hZW
        (Fin.cases hEW (Fin.cases hδW (Fin.cases (wt ω hωW e heω) (fun _ => htW)))))))))
  obtain ⟨ξ, ζ, X, Y, a, H, b, K, u, sx, sy, hx, hy, mx, my, l, r, _⟩ := h.read_l hZF hω he heω pool₀
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hν).limit_value (hω.isLimitOrdinal hZF) sx
  have hζ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).limit_value (hω.isLimitOrdinal hZF) sy
  have hβξ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k ω ho (hω.isOrdinal hZF) hk β ξ sum sx
  have hβζ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hμ k ω ho (hω.isOrdinal hZF) hk β' ζ sum' sy
  have low := l.move_read_l hZF mx hω hξ hx hν hk sum hβξ hA hων hκA hC hδ hωδ hκδ
    hB constants pool model hn column assign tuple point ha
  have high := r.move_read_l hZF my hω hζ hy hμ hk sum' hβζ hA' hωμ hκA' hC hδ hωδ hκδ
    hB constants pool model' hn column assign' tuple' point' ha
  have same := l.point_congr_l hZF hω r tm_type_f tm_type_closed_l (tm_params_l ω C κ k n Z E δ e t) ha
  have truth' := high.mp (same.mp (low.mpr truth))
  exact ⟨B, U, D, t, hB, constants, pool,
    ⟨hk, hek, β, A, c, R, s, sum, hA, model, assign,
      ⟨model.1, hn, tuple, point, fun x hx => ca x (ct U hUC x hx), pool, truth⟩⟩,
    ⟨hk, hek, β', A', c', R', s', sum', hA', model', assign',
      ⟨model'.1, hn, tuple', point', fun x hx => ca' x (ct U hUC x hx), pool, truth'⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
