import YesMetaZFC.Model.SetTheory.Internal.TypeGuardCode
import YesMetaZFC.Model.SetTheory.Internal.TypeGuardColumn
import YesMetaZFC.Model.SetTheory.Internal.TypeMinus

/-! # 前驱定义域的完整类型查询

实际查询只依赖变量数和集合常量 κ，与实现元组和秩层无关。
查询成员性精确检查 κ、δ 及所有原变量是否属于最大序数对应的前一层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 为任意内部元数生成同一个可复用查询，随后可在所有后继秩层的实现类型中读取。 -/
theorem tt_guard_query_l {ω n κ U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.mem κ U) (pool : Tt_pool_d I ω n U D) : ∃ p, M.mem p D ∧
      ∀ ν μ X Y c R s δ t, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
        Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
        (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨b, l, k, e, hb, hl, hlω, hk, fn, column⟩ := tg_column_l hZF hω hn hκ names
  obtain ⟨a, m, G, u, form, guard⟩ := sg_guard_rank_l I hZF hω hlω
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨p, hp⟩ := (I).total z e
  have hz := sc_num_natural_l I hZF hω code
  have hpD := (prod p).mpr ⟨z, hz, e, (seq e).mpr ⟨l, hlω, fn⟩, hp⟩
  refine ⟨p, hpD, fun ν μ X Y c R s δ t hV hW hs hων hm type => ?_⟩
  obtain ⟨v, assign, fv⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n hn)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fv) type.point
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) hp hz hlω fn.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans ((guard ν μ X Y c R f hV hW hs hων hm ff).trans
        (tg_column_values_l hZF hω hb hl hlω hk column type.tuple assign fill ff)))))

/-- 实际定义域查询是前驱实现的充分必要条件；常量域的下降从 κ 的下降自动推出。 -/
theorem tt_minus_guarded_l {ω ν μ κ B X Y c R n s δ U D t : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hm : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) ∧
      (M.mem p t ↔ ∃ d S u, Smem_d I d X S ∧ Tm_minus_d I ω D t u ∧
        Tt_realized_d I ω d X S n s δ U D u) := by
  obtain ⟨p, hp, read⟩ := tt_guard_query_l hZF hω type.finite ((constants κ).mpr (Or.inr rfl)) type.pool
  have guard := read ν μ X Y c R s δ t hV hW hs hων hm type
  refine ⟨p, hp, guard, ⟨?_, ?_⟩⟩
  · intro ht
    obtain ⟨tuple, point, critical⟩ := guard.mp ht
    have hκν := ZF.v_ordinal_height_l hZF hV (v_ordinal_l I hB) critical
    have sub := ZF.v_mono_l I hZF hB hV ((v_ordinal_l I hV).transitive κ hκν)
    exact tt_minus_rank_l hZF hω hV hW hs type hm tuple point (fun x hx =>
      ((constants x).mp hx).elim (sub x) (fun eq => eq.symm ▸ critical))
  · rintro ⟨_, _, _, _, _, lower⟩
    exact guard.mpr ⟨lower.tuple, lower.point, lower.constants κ ((constants κ).mpr (Or.inr rfl))⟩

end YesMetaZFC.SetTheory.Internal
