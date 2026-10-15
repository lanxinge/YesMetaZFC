import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericMeet
import YesMetaZFC.Model.Forcing.Internal.Ground.LegalMove

/-! # 首达时刻的实际请求捕获

首达之前的最后一个请求落在目标 Vκ 中，故其参数域严格小于 κ。由原规则
推出目标请求合法，再以最小编号性排除越过目标编号；整个类型检查留在地模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Tg_aux_data_d.domain_bound_l {a ℓ t τ u κ C : M.Domain}
    (data : Tg_aux_data_d a ℓ t τ u) (hC : V_d I κ C) (hτ : M.IsOrdinal τ) (ha : M.mem a C) : M.mem τ κ := by
  obtain ⟨b, ⟨d, pair₀, pair₁⟩, pair₂⟩ := data
  have tr := ZF.v_transitive_l I hM hC
  exact ZF.v_ordinal_height_l hM hC hτ
    (KPair_d.mem_l M pair₂ tr (KPair_d.mem_l M pair₀ tr (KPair_d.mem_l M pair₁ tr ha).2).2).1

/-- 原逐步检查给出实际可追加历史，不把“合法请求”当作额外判定器。 -/
theorem Tg_histories_d.admit_l {p : Tg_params_d M.Domain} {X F L i n h a : M.Domain}
    (histories : Tg_histories_d hM p X F L) (hw : M.IsOmega p.ω) (hi : M.mem i p.ω)
    (hn : M.mem n p.ω) (fn : Fn0_d i X h) (div : M.IsOrdinalDivision I i p.c n p.e)
    (ha : M.mem a X) (aux : Tg_aux_d hM p n h a) : Cg_admit_d hM p.ω L h a := by
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hM hw hi (fn0_function_l (ZF.modelsKP hM) fn) ha
  obtain ⟨j', i', d⟩ := endt
  have ei := d.prefix_sequence.2.2.2.eq hM.1 (fn0_function_l (ZF.modelsKP hM) fn).2.1
  have ej := d.source.2.2.2.eq hM.1 ft.2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  exact ⟨t, (histories.2 t).mpr ⟨(histories.1 t).mpr ⟨j, hj, ft⟩,
    tg_check_end_l hM hj succ (fn0_of_function_l (ZF.modelsKP hM) ft) fn ⟨j', i', d⟩
      ⟨n, p.e, hn, div, Or.inl ⟨rfl, aux⟩⟩⟩, j', i', d⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

/-- 6.6 的捕获步骤：首次不低于 i 的选择只能等于 i。此前只需最后一次选择的界。 -/
theorem Tg_generic_target_d.capture_l {p : Tg_params_d M.Domain}
    {X F L ℓ s t k m β g a₀ b₀ κ C a u q d i n z h r j a' ℓ' t' τ u' : M.Domain}
    {f v w : N.Domain}
    (target : Tg_generic_target_d hM p ℓ s t k m β g a₀ b₀ κ C a u)
    (hw : M.IsOmega p.ω) (hw' : N.IsOmega (e p.ω)) (histories : Tg_histories_d hM p X F L)
    (fq : Fn0_d d X q) (dw : M.mem d p.ω) (ia : Rd_entry_d i a q) (iw : M.mem i p.ω)
    (before : ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C)
    (ff : N.IsSetFunction J f) (kept : ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) f)
    (scan : Cg_scan_d hN (e p.ω) (e L) f (e h) v) (cross : ¬ N.mem v (e i))
    (lastIndex : Rd_entry_d w (e a') f) (below : N.mem w (e i))
    (old : Tg_aux_data_d a' ℓ' t' τ u') (oτ : M.IsOrdinal τ)
    (succ : M.SuccessorOf n j) (oldEvent : Tg_event_d I p.c j p.e h a')
    (hn : M.mem n p.ω) (hr : M.mem r p.ω) (fn : Fn0_d r X h)
    (div : M.IsOrdinalDivision I r p.c n p.e)
    (digits : Tg_digits_d hM p.c p.b n p.A h z) (real : M.IsRestrictionOf I s z k)
    (hℓ : M.mem ℓ n) (event₀ : Tg_event_d I p.c ℓ p.e h a₀) (event₁ : Tg_event_d I p.c ℓ p.a h b₀) :
    v = e i ∧ Rd_entry_d v (e a) f ∧ Tg_aux_d hM p n h a := by
  obtain ⟨j₀, hj₀, eq⟩ := (he i w).mp below
  have fq' := fn0_function_l (ZF.modelsKP hM) fq
  have hid := fq'.input_mem_of_pairMember ia
  -- i 是有限条件已有的坐标，故 i 之前的枚举值均来自该条件。
  have od := hw.members_areOrdinals hM d dw
  obtain ⟨y, _, jy⟩ := fq'.2.2 j₀ (od.transitive i hid j₀ hj₀)
  have same : e a' = e y := ff.2 (e j₀) (e a') (e y) (eq.symm ▸ lastIndex) (kept j₀ y jy)
  have bound := old.domain_bound_l hM target.2.1 oτ ((hi same).symm ▸ before j₀ y hj₀ jy)
  have aux := target.2.2.2.2 n h z digits real hℓ event₀ event₁ (Or.inr ⟨j, a', ℓ', t', τ, u', succ, oldEvent, old, bound⟩)
  have legal := histories.admit_l hM hw hr hn fn div (fq.bound_l ia).2 aux
  have hh := (histories.1 h).mpr ⟨r, hr, fn0_function_l (ZF.modelsKP hM) fn⟩
  have legal' := (image_admit_l hM hN e hi he hw hw' histories.1 (fun t ht => ((histories.2 t).mp ht).1) hh).mp legal
  have eq := (scan.le_l hN hw' ((image_member_l e hi he).mpr iw) (kept i a ia) legal').elim (fun lt => (cross lt).elim) (fun eq => eq)
  exact ⟨eq, eq.symm ▸ kept i a ia, aux⟩

end YesMetaZFC.SetTheory.LargeCardinal
