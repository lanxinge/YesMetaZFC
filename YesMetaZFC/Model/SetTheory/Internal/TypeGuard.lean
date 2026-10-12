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

/-- 读取指定的原程序和原名字列，不重新选择查询。 -/
theorem Tg_guard_program_d.query_l {ω n κ U D l z p : M.Domain} (hω : M.IsOmega ω)
    (program : Tg_guard_program_d I ω l z) (pool : Tt_pool_d I ω n U D)
    (code : Tg_guard_code_d n κ U l z p) : M.mem p D ∧
    ∀ ν μ X Y c R s δ t, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
      Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
      (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) := by
  obtain ⟨b, k, e, N, hb, hl, names, fn₀, hk, hp, old, last⟩ := code
  obtain ⟨N', E, names', seq, prod⟩ := pool
  have eq := hZF.1.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  have fn := fn0_function_l (ZF.modelsKP hZF) fn₀
  have hpD := (prod p).mpr ⟨z, program.2.1, e, (seq e).mpr ⟨l, program.1, fn⟩, hp⟩
  have column i a : Rd_entry_d i a e ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
    refine ⟨fun entry => ?_, fun h => h.elim (fun ⟨hi, eq⟩ => eq.symm ▸ old i hi)
      (fun ⟨eq, eq'⟩ => eq.symm ▸ eq'.symm ▸ last)⟩
    rcases (hl i).mp (fn.input_mem_of_pairMember entry) with hi | eq
    exact Or.inl ⟨hi, fn.1.2 i a i entry (old i hi)⟩
    have eq := hZF.1.eq_of_same_members i b eq
    exact Or.inr ⟨eq, fn.1.2 i a k entry (eq.symm ▸ last)⟩
  refine ⟨hpD, fun ν μ X Y c R s δ t hV hW hs hων hm type => ?_⟩
  obtain ⟨v, assign, fv⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n type.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fv) type.point
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) hp program.2.1 program.1 fn.2.1 assign fill).trans
      ((program.2.2 ν μ X Y c R f hV hW hs hων hm ff).trans
        (tg_column_values_l hZF hω hb hl program.1 hk column type.tuple assign fill ff))))

/-- 程序元数和自然数码与原查询一起返回，供跨模型保持。 -/
theorem tt_guard_query_l {ω n κ U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.mem κ U) (pool : Tt_pool_d I ω n U D) :
    ∃ p l z, Tg_guard_program_d I ω l z ∧ Tg_guard_code_d n κ U l z p ∧ M.mem p D ∧
      ∀ ν μ X Y c R s δ t, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
        Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
        (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨b, l, k, e, hb, hl, hlω, hk, fn, column⟩ := tg_column_l hZF hω hn hκ names
  obtain ⟨z, program⟩ := tg_guard_program_l I hZF hω hlω
  obtain ⟨p, hp⟩ := (I).total z e
  have hpD := (prod p).mpr ⟨z, program.2.1, e, (seq e).mpr ⟨l, hlω, fn⟩, hp⟩
  have code : Tg_guard_code_d n κ U l z p := ⟨b, k, e, N, hb, hl, names,
    fn0_of_function_l (ZF.modelsKP hZF) fn, hk, hp,
    fun i hi => (column i i).mpr (Or.inl ⟨hi, rfl⟩), (column b k).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  exact ⟨p, l, z, program, code, program.query_l hZF hω ⟨N, E, names, seq, prod⟩ code⟩

/-- 实际定义域查询是前驱实现的充分必要条件；常量域的下降从 κ 的下降自动推出。 -/
theorem tt_minus_guarded_l {ω ν μ κ B X Y c R n s δ U D t : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hm : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) ∧
      (M.mem p t ↔ ∃ d S u, Smem_d I d X S ∧ Tm_minus_d I ω D t u ∧
        Tt_realized_d I ω d X S n s δ U D u) := by
  obtain ⟨p, _, _, _, _, hp, read⟩ := tt_guard_query_l hZF hω type.finite ((constants κ).mpr (Or.inr rfl)) type.pool
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
