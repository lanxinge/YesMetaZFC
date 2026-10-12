import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticCode
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticColumn

/-! # 全高度条件成为原 κ 型的一个固定查询

查询在任何类型和实现元组出现之前实际构造。名字列只使用原变量、指定
常量 δ 及 Vκ∪{κ} 中已有的常量；原 κ 型和原元组图都不是新参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_stretch_program_d.query_l {ω κ n U D v d e z p : M.Domain} (hω : M.IsOmega ω)
    (program : Ee_stretch_program_d ω n v d e z) (pool : Tt_pool_d I ω n U D)
    (code : Ee_stretch_code_d ω n κ v d e z p) (hpD : M.mem p D) :
    ∀ (hZFC : M.Models ZFC) ν μ A Y X c R c' R' δ K S s t,
      V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K X S → Smem_d I c A R → Smem_d I c' Y R' →
      Tt_realized_d I ω c' Y R' n s δ U D t → Fn0_d n A s → M.mem δ A →
        (M.mem p t ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c X S) := by
  obtain ⟨C, kw, kn, kk, pair, hw, hnn, hk, old, cw, cn, cd, ck⟩ := code
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z', _, C', hC', pair'⟩ := (prod p).mp hpD
  obtain ⟨eqz, eqC⟩ := kpair_injective_l M pair' pair
  subst z' C'
  obtain ⟨b, hbω, cf⟩ := (seq C).mp hC'
  intro hZFC ν μ A Y X c R c' R' δ K S s t hA hY succ hX hδ hωδ hκδ source lower upper type tuple point
  obtain ⟨r, assign, fr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n program.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) cf)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr) type.point
  have value i q x (hc : Rd_entry_d i q C) (val : Tn_value_d n s δ q x) : Rd_entry_d i x f :=
    (fill.2 i x).mpr ⟨hω.transitive hZF b hbω i (cf.input_mem_of_pairMember hc),
      Or.inl ⟨cf.input_mem_of_pairMember hc, (assign.2 i x).mpr ⟨q, hc, val⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x s) : Rd_entry_d i x f :=
    value i i x (old i (type.tuple.bound_l hx).1) (Or.inl hx)
  have same i x (hi : M.mem i n) : Rd_entry_d i x s ↔ Rd_entry_d i x f := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact (ff.1.2 i y x (vars i y hy) hx) ▸ hy
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) pair program.natural hbω cf.2.1 assign fill).trans
        (program.read hZFC ν μ A Y X c R c' R' κ δ K S s f hA hY succ hX hδ hωδ hκδ source lower upper tuple point ff same
          (value n kw ω cw (Or.inr (Or.inr hw))) (value v kn n cn (Or.inr (Or.inr hnn)))
          (value d n δ cd (Or.inr (Or.inl ⟨rfl, rfl⟩))) (value e kk κ ck (Or.inr (Or.inr hk))))))

/-- 同一程序生成查询，原自然数码和名字列随语义读取一起返回。 -/
theorem ee_query_build_l {ω κ n B U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.IsLimitOrdinal κ) (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d I ω n U D) : ∃ p v d e z,
      Ee_stretch_program_d ω n v d e z ∧ Ee_stretch_code_d ω n κ v d e z p ∧ M.mem p D ∧
      ∀ (hZFC : M.Models ZFC) ν μ A Y X c R c' R' δ K S s t,
      V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K X S → Smem_d I c A R → Smem_d I c' Y R' →
      Tt_realized_d I ω c' Y R' n s δ U D t → Fn0_d n A s → M.mem δ A →
        (M.mem p t ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c X S) := by
  obtain ⟨v, d, e, z, program⟩ := ee_stretch_program_l hZF hω hn
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨hωU, hnU⟩ := tt_constants_finite_l hZF hω hn hκ hB constants
  obtain ⟨b, C, kw, kn, kk, _, hbω, cf, hw, hnn, hk, old, cw, cn, cd, ck⟩ :=
    ee_column_l hZF hω hn program.next program.point program.critical hωU hnU ((constants κ).mpr (Or.inr rfl)) names
  obtain ⟨p, pair⟩ := (I).total z C
  have hpD := (prod p).mpr ⟨z, program.natural, C, (seq C).mpr ⟨b, hbω, cf⟩, pair⟩
  have code : Ee_stretch_code_d ω n κ v d e z p := ⟨C, kw, kn, kk, pair, hw, hnn, hk, old, cw, cn, cd, ck⟩
  exact ⟨p, v, d, e, z, program, code, hpD, program.query_l hZF hω ⟨N, E, names, seq, prod⟩ code hpD⟩

end YesMetaZFC.SetTheory.LargeCardinal
