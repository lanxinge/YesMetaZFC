import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 原公式在完整类型中的实际查询码

给原公式每个参数一个合法名字，就自动编译出类型查询。名字可以重复或置换，
并可同时引用实现元组、指定常量和参数域中的任意集合常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原模板的自然数程序先于任何常量和名字列取定。 -/
structure Tt_program_d (ω z : M.Domain) {d : Nat} (φ : Formula 1 d) : Prop where
  natural : M.mem z ω
  read : ∀ c Z R f (model : Smdl_d I c Z R) (ρ : Env (smdl_structure_l I (R := R) model.2.1) d),
    M.IsSetFunctionFromTo I f ω Z →
    (∀ i x, Num_d i.val x → Rd_entry_d x (ρ.bound i).val f) →
      (Sc_sat_d I ω c z f ↔ Formula.satisfies ρ φ)

theorem tt_program_l {ω : M.Domain} (hω : M.IsOmega ω) {d : Nat}
    (φ : Formula 1 d) (hc : φ.FreeClosed) : ∃ z, ∃ v : Fin d → M.Domain,
      (∀ i, Num_d i.val (v i)) ∧ Tt_program_d hZF ω z φ := by
  obtain ⟨a, m, F, k, v, form, nums, compile⟩ := source_compile_l I hZF hω φ hc
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  refine ⟨z, v, nums, sc_num_natural_l I hZF hω code, fun c Z R f model ρ fn values => ?_⟩
  obtain ⟨E, space⟩ := ZF.exists_functionSpace hZF I ω Z
  exact (sc_sat_decode_l I hZF hω code).trans ((satisfies_decode_l I hZF.1 model form space).trans
    (compile Z R model.2.1 E space f ((space f).mpr fn) ρ (fun i => values i (v i) (nums i))))

/-- 自然数程序与实际名字列组成原查询；证书不包含语义假设。 -/
def Tt_code_d {d : Nat} (n U z p : M.Domain) (a : Fin d → M.Domain) : Prop :=
  ∃ N C b, Tn_names_d n U N ∧ Num_d d b ∧ Fn0_d b N C ∧ KPair_d M p z C ∧
    ∀ i x, Num_d i.val x → Rd_entry_d x (a i) C

theorem tt_code_l {ω n U D z : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D)
    (hz : M.mem z ω) {d : Nat} (v a : Fin d → M.Domain) (hv : ∀ i, Num_d i.val (v i))
    (names : ∀ i, Tn_name_d n U (a i)) : ∃ p, M.mem p D ∧ Tt_code_d n U z p a := by
  obtain ⟨N, E, hN, hE, hD⟩ := pool
  obtain ⟨b, hb⟩ := num_exists_l (ZF.modelsKP hZF) d
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF I b N
  have injective : Function.Injective v := fun i j eq =>
    Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (eq.symm ▸ hv j))
  obtain ⟨e, heB, params⟩ := senv_params_l I hZF hB ⟨n, (hN n).mpr (Or.inr (Or.inl rfl))⟩ v a injective
    (fun i => num_lt_l hZF.1 (hv i) hb i.isLt) (fun i => (hN (a i)).mpr (names i))
  have he := (hB e).mp heB
  obtain ⟨p, hp⟩ := (I).total z e
  have hbω := num_mem_l hZF.1 hω hb
  exact ⟨p, (hD p).mpr ⟨z, hz, e, (hE e).mpr ⟨b, hbω, he⟩, hp⟩,
    N, e, b, hN, hb, fn0_of_function_l (ZF.modelsKP hZF) he, hp,
    fun i x hx => (num_unique_l hZF.1 (hv i) hx) ▸ params i⟩

theorem Tt_code_d.read_l {ω n U D z p : M.Domain} (hω : M.IsOmega ω) (hzω : M.mem z ω)
    {d : Nat} {a : Fin d → M.Domain}
    (pool : Tt_pool_d I ω n U D) (code : Tt_code_d n U z p a) : M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) →
        ∃ f, M.IsSetFunctionFromTo I f ω Z ∧ (∀ i x, Num_d i.val x → Rd_entry_d x (ρ.bound i).val f) ∧
          (M.mem p t ↔ Sc_sat_d I ω c z f) := by
  obtain ⟨N, e, b, hN, hb, fn, hp, params⟩ := code
  obtain ⟨N', E, hN', hE, hD⟩ := pool
  have eq := hZF.1.eq_of_same_members N' N (fun x => (hN' x).trans (hN x).symm)
  subst N'
  have he := fn0_function_l (ZF.modelsKP hZF) fn
  have hbω := num_mem_l hZF.1 hω hb
  have hpD := (hD p).mpr ⟨z, hzω, e, (hE e).mpr ⟨b, hbω, he⟩, hp⟩
  refine ⟨hpD, fun c Z R s δ t h ρ values => ?_⟩
  obtain ⟨r, hr, fnr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals hZF n h.finite)
    h.tuple h.point h.constants hN (fn0_of_function_l (ZF.modelsKP hZF) he)
  obtain ⟨f, hf, fnf⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fnr) h.point
  have match_params i x (hx : Num_d i.val x) : Rd_entry_d x (ρ.bound i).val f :=
    (hf.2 x (ρ.bound i).val).mpr ⟨num_mem_l hZF.1 hω hx, Or.inl
      ⟨num_lt_l hZF.1 hx hb i.isLt, (hr.2 x (ρ.bound i).val).mpr ⟨a i, params i x hx, values i⟩⟩⟩
  exact ⟨f, fnf, match_params, (h.truth p).trans ((and_iff_right hpD).trans
    (tt_query_decode_l I (ZF.modelsKP hZF) hp hzω hbω he.2.1 hr hf))⟩

theorem Tt_program_d.query_l {ω n U D z p : M.Domain} (hω : M.IsOmega ω)
    {d : Nat} {φ : Formula 1 d} {a : Fin d → M.Domain} (program : Tt_program_d hZF ω z φ)
    (pool : Tt_pool_d I ω n U D) (code : Tt_code_d n U z p a) : M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) → (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨hp, read⟩ := code.read_l hZF hω program.natural pool
  refine ⟨hp, fun c Z R s δ t h ρ values => ?_⟩
  obtain ⟨f, fn, params, truth⟩ := read c Z R s δ t h ρ values
  exact truth.trans (program.read c Z R f h.model ρ fn params)

/-- 查询在任何类型及实现出现之前固定；同一程序和实际名字列供全部模型读取。 -/
theorem tt_fixed_query_l {ω n U D : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D)
    {d : Nat} (φ : Formula 1 d) (hφ : φ.FreeClosed) (a : Fin d → M.Domain)
    (names : ∀ i, Tn_name_d n U (a i)) : ∃ p, M.mem p D ∧
      ∀ c Z R s δ t (h : Tt_realized_d I ω c Z R n s δ U D t)
        (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d),
        (∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) → (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨z, v, nums, program⟩ := tt_program_l hZF hω φ hφ
  obtain ⟨p, hp, code⟩ := tt_code_l hZF hω pool program.natural v a nums names
  exact ⟨p, hp, (program.query_l hZF hω pool code).2⟩

theorem tt_source_l {ω c Z R n s δ U D t : M.Domain}
    (hω : M.IsOmega ω) (h : Tt_realized_d I ω c Z R n s δ U D t)
    {d : Nat} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) d) (a : Fin d → M.Domain)
    (names : ∀ i, Tn_name_d n U (a i)) (values : ∀ i, Tn_value_d n s δ (a i) (ρ.bound i).val) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Formula.satisfies ρ φ) := by
  obtain ⟨p, hp, read⟩ := tt_fixed_query_l hZF hω h.pool φ hφ a names
  exact ⟨p, hp, read c Z R s δ t h ρ values⟩

end YesMetaZFC.SetTheory.Internal
