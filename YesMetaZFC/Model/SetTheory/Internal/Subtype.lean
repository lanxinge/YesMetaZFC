import YesMetaZFC.Model.SetTheory.Internal.SubtypeCode

/-! # 子类型查询的自动构造与定义 3.7

候选低域类型的秩界自动保证其名字合法。固定程序及唯一查询码读取
原定义中的全部实现见证，允许任意内部有限元数和排列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ts_parameters_rank_l {ω κ τ n m B U A V D w : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hA : V_d I τ A) (small : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ)
    (pool : Tt_pool_d I ω m V D) (sub : M.MemberSubset w D) :
    M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U := by
  have hwκ := ordinal_down_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) hκ.1
    (hω.subset_limitOrdinal hZF hτ) hτκ
  have hV := tt_constants_rank_l hZF hB hκ hτκ hA small
  have hD := pool.rank_mem_l hZF hω hB hκ (ZF.v_ordinal_mem_l I hZF hB hwκ) hm hV
  have finite := tt_constants_finite_l hZF hω hn hκ hB constants
  exact ⟨(constants w).mpr (Or.inl (ZF.v_subset_mem_l I hZF hB hD sub)),
    (tt_constants_finite_l hZF hω hm hκ hB constants).2, finite.2,
    (constants τ).mpr (Or.inl (ZF.v_ordinal_mem_l I hZF hB hτκ)),
    (constants κ).mpr (Or.inr rfl), finite.1⟩

theorem Ts_query_d.read_l {ω n κ τ m U w b a z q : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z) (code : Ts_query_d ω n κ τ m U w b σ z q)
    {η Y c R s δ D t A V W : M.Domain} (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n s δ U D t)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ) (hm : M.mem m ω)
    (hA : V_d I τ A) (constants : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ) (small : Tt_pool_d I ω m V W) :
    M.mem q t ↔ M.MemberSubset n m ∧ Ts_real_d hZF ω δ n s m V W w η := by
  obtain ⟨hc, N, C, v, names, col, orig, params, vals, pair⟩ := code
  let ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7 :=
    ⟨Fin.cases ⟨w, type.constants w hc.1⟩ (Fin.cases ⟨δ, type.point⟩
      (Fin.cases ⟨m, type.constants m hc.2.1⟩ (Fin.cases ⟨n, type.constants n hc.2.2.1⟩
        (Fin.cases ⟨τ, type.constants τ hc.2.2.2.1⟩ (Fin.cases ⟨κ, type.constants κ hc.2.2.2.2.1⟩
          (fun _ => ⟨ω, type.constants ω hc.2.2.2.2.2⟩)))))), fun _ => ⟨δ, type.point⟩⟩
  have values : ∀ i, Tn_value_d n s δ (v i) (ρ.bound i).val :=
    Fin.cases (Or.inr (Or.inr vals.1)) (Fin.cases (Or.inr (Or.inl ⟨vals.2.1, rfl⟩))
      (Fin.cases (Or.inr (Or.inr vals.2.2.1)) (Fin.cases (Or.inr (Or.inr vals.2.2.2.1))
        (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.1)) (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.2.1))
          (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.2.2)) (fun i => Fin.elim0 i)))))))
  exact prog.read_l hZF hω type.pool names v (fn0_function_l (ZF.modelsKP hZF) col) orig params pair
    model type ρ hY values rfl rfl rfl hκ hτ hτκ hm hA constants small

theorem ts_subtype_realized_l {ω n κ τ m U w b a z : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    {η Y c R s δ B D t A V W : M.Domain} (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n s δ U D t)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ) (hm : M.mem m ω)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hA : V_d I τ A) (small : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ)
    (pool : Tt_pool_d I ω m V W) (sub : M.MemberSubset w W) :
    Ts_subtype_d ω n κ τ m U w b σ z t ↔ M.MemberSubset n m ∧ Ts_real_d hZF ω δ n s m V W w η := by
  constructor
  · rintro ⟨_, _, q, code, hq⟩
    exact (code.read_l hZF hω prog hY model type hκ hτ hτκ hm hA small pool).mp hq
  · intro real
    obtain ⟨q, _, code⟩ := prog.query_exists_l hZF type.pool
      (ts_parameters_rank_l hZF hω prog.finite hm hκ hτ hτκ hB constants hA small pool sub)
    exact ⟨hτκ, real.1, q, code, (code.read_l hZF hω prog hY model type hκ hτ hτκ hm hA small pool).mpr real⟩

end YesMetaZFC.SetTheory.Internal
