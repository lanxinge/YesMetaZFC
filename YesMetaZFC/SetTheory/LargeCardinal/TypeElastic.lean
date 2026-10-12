import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticQuery
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticClauses
import YesMetaZFC.Model.SetTheory.Internal.TypeGuard

/-! # Neeman 定义 3.13：原类型的弹性

编译时固定四条具体查询：最大序数、前驱参数域、δ 不可达、全高度伸展。
固定语言表示后，定义只检查这四条查询是否属于类型；不要求类型可实现或
对逻辑推论封闭。`ee_definition_l` 在任何类型出现之前构造全部查询及其域。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 四条查询是编译所得的实际数据，次序与定义 3.4、3.13 一致。 -/
structure Ee_queries_d (M : Structure.{u}) where
  largest : M.Domain
  domain : M.Domain
  inaccessible : M.Domain
  stretch : M.Domain

def Ee_defined_d (q : Ee_queries_d M) (t : M.Domain) : Prop := M.mem q.largest t ∧ M.mem q.domain t

def Ee_elastic_d (q : Ee_queries_d M) (t : M.Domain) : Prop :=
  Ee_defined_d q t ∧ M.mem q.inaccessible t ∧ M.mem q.stretch t

def Ee_minus_d (I : kpair_convention_l.Interpretation M) (ω D : M.Domain) (q : Ee_queries_d M)
    (t v : M.Domain) : Prop := Ee_defined_d q t ∧ Tm_minus_d I ω D t v

def ee_elastic_m {d} (g h i e t : Term d) : Formula 1 d :=
  .conj (.conj (.mem g t) (.mem h t)) (.conj (.mem i t) (.mem e t))
derive_free_closed ee_elastic_m

theorem ee_elastic_delta_l {d} (g h i e t : Term d) : (ee_elastic_m g h i e t).IsDelta0 :=
  .conj (.conj (.mem ..) (.mem ..)) (.conj (.mem ..) (.mem ..))

theorem ee_elastic_sat_l {d} (ρ : Env M d) (g h i e t : Term d) :
    Formula.satisfies ρ (ee_elastic_m g h i e t) ↔
      Ee_elastic_d ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ (t.eval ρ) := by
  simp only [ee_elastic_m, Ee_elastic_d, Ee_defined_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]

/-- 固定的原查询在传递模型中绝对；这里没有实现、超幂或集合论理论假设。 -/
theorem ee_elastic_absolute_l {X : M.Domain} (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
    {d} (ρ : Env (rt_model_l X nx) d) (g h i e t : Term d) :
    Formula.satisfies ρ (ee_elastic_m g h i e t) ↔
      Ee_elastic_d ⟨(g.eval ρ).val, (h.eval ρ).val, (i.eval ρ).val, (e.eval ρ).val⟩ (t.eval ρ).val := by
  have read := ee_elastic_sat_l (image_env_l (M := rt_model_l X nx) (N := M) Subtype.val ρ) g h i e t
  simp only [eval_image_env_l (M := rt_model_l X nx) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hX nx (ee_elastic_delta_l ..) ρ).trans read

/-- 任意裸类型的偏算子：只有两条定义域查询同时属于类型时才有前驱。 -/
theorem ee_minus_exists_l (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
    (ω D : M.Domain) (q : Ee_queries_d M) (t : M.Domain) :
    (∃ v, Ee_minus_d I ω D q t v) ↔ Ee_defined_d q t := by
  refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
  obtain ⟨v, hv⟩ := tm_minus_exists_l I hZF ω D t
  exact ⟨v, h, hv⟩

theorem Ee_minus_d.unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {ω D q t v w} (h : Ee_minus_d I ω D q t v) (k : Ee_minus_d I ω D q t w) : v = w :=
  h.2.unique_l I hE k.2

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 四个低程序证书及组成当前查询的实际名字列。 -/
def Ee_numeric_d (ω κ n U : M.Domain) (q : Ee_queries_d M) : Prop := ∃ l v d e zg zh zi ze kw,
  Ee_largest_program_d hZF ω zg ∧ Tt_code_d n U zg q.largest (Fin.elim0 : Fin 0 → M.Domain) ∧
  Tg_guard_program_d I ω l zh ∧ Tg_guard_code_d n κ U l zh q.domain ∧
  Ee_inacc_program_d hZF ω zi ∧ KPair_d M kw ω ω ∧
  Tt_code_d n U zi q.inaccessible (Fin.cases n (fun _ => kw) : Fin 2 → M.Domain) ∧
  Ee_stretch_program_d ω n v d e ze ∧ Ee_stretch_code_d ω n κ v d e ze q.stretch

/-- 两条原定义域查询的完整接口；不含不可达性、伸展或 κ 型秩证书。 -/
structure Ee_domain_d (ω κ n U D g h : M.Domain) : Prop where
  omega_mem : M.mem ω U
  pool : Tt_pool_d I ω n U D
  successor : ∀ μ Y c R s δ t, V_d I μ Y → Smem_d I c Y R →
    Tt_realized_d I ω c Y R n s δ U D t → (M.mem g t ↔ ∃ ν, M.SuccessorOf μ ν)
  domain : ∀ ν μ A Y c R s δ t, V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
    Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
      (M.mem h t ↔ Fn0_d n A s ∧ M.mem δ A ∧ M.mem κ A)

/-- 实际编译语言的证书：定义域、不可达性与伸展使用同一组原查询。 -/
structure Ee_language_d (ω κ n B U D : M.Domain) (q : Ee_queries_d M)
    extends Ee_domain_d hZF ω κ n U D q.largest q.domain where
  limit : M.IsLimitOrdinal κ
  rank : V_d I κ B
  constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ
  largest_mem : M.mem q.largest D
  domain_mem : M.mem q.domain D
  inaccessible_mem : M.mem q.inaccessible D
  stretch_mem : M.mem q.stretch D
  inaccessible : ∀ c Y R s δ t, Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
    (M.mem q.inaccessible t ↔ Sc_inaccessible_d ω Y δ)
  read : ∀ (hZFC : M.Models ZFC) ν μ A Y X c R δ K S s t,
    V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
    M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K X S → Smem_d I c Y R →
    Tt_realized_d I ω c Y R n s δ U D t →
    (Ee_elastic_d q t ↔ Sc_inaccessible_d ω Y δ ∧ ∃ c₀ R₀ w, Smem_d I c₀ A R₀ ∧ Tm_minus_d I ω D t w ∧
      Tt_realized_d I ω c₀ A R₀ n s δ U D w ∧ ∀ τ, M.mem τ δ → Ee_step_d (ZFC.models_zf_l hZFC) ω κ δ n s c₀ X S w τ)
  numeric : Ee_numeric_d hZF ω κ n U q

/-- 同一自然数程序和原名字列恢复整份语言，不重新编译或选择查询。 -/
theorem Ee_numeric_d.language_l {ω κ n B U D : M.Domain} {q : Ee_queries_d M} (hω : M.IsOmega ω)
    (hκ : M.IsLimitOrdinal κ) (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d I ω n U D) (numeric : Ee_numeric_d hZF ω κ n U q)
    (he : M.mem q.stretch D) : Ee_language_d hZF ω κ n B U D q := by
  have original := numeric
  obtain ⟨l, v, d, e, zg, zh, zi, ze, kw, pg, cg, ph, ch, pi, hw, ci, pe, ce⟩ := numeric
  have hn := pe.finite
  obtain ⟨hwU, _⟩ := tt_constants_finite_l hZF hω hn hκ hB constants
  obtain ⟨hg, greatest⟩ := pg.2 n U D q.largest pool cg
  obtain ⟨hd, guard⟩ := ph.query_l hZF hω pool ch
  obtain ⟨hi, inaccessible⟩ := pi.2 n U D kw q.inaccessible pool hwU hw ci
  have stretch := pe.query_l hZF hω pool ce he
  refine ⟨⟨hwU, pool, greatest, guard⟩, hκ, hB, constants, hg, hd, hi, he, inaccessible,
    fun hZFC ν μ A Y X c R δ K S s t hA hY succ hX hδ hwδ hkδ source upper type => ?_, original⟩
  have hwY := type.constants ω hwU
  have hων : M.MemberSubset ω ν := by
    rcases (succ ω).mp (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) hwY) with lt | eq
    · exact (v_ordinal_l I hA).transitive ω lt
    · exact fun x hx => (eq x).mp hx
  obtain ⟨z, _, hzω⟩ := hω.1.1
  obtain ⟨c₀, R₀, lower⟩ := smdl_membership_l I hZF ⟨z, ZF.v_ordinal_mem_l I hZF hA (hων z hzω)⟩
  have domain := guard ν μ A Y c R s δ t hA hY succ hων upper type
  have inacc := inaccessible c Y R s δ t upper type
  have top := (greatest μ Y c R s δ t hY upper type).mpr ⟨ν, succ⟩
  constructor
  · rintro ⟨⟨_, ht⟩, ii, ee⟩
    -- 守卫使原变量和全部常量下降；完整真值的唯一性识别公式中的 w 与 u⁻。
    obtain ⟨tuple, point, critical⟩ := domain.mp ht
    have hκν := ZF.v_ordinal_height_l hZF hA hκ.1 critical
    have sub := ZF.v_mono_l I hZF hB hA ((v_ordinal_l I hA).transitive κ hκν)
    obtain ⟨c₁, R₁, w, model, minus, realized⟩ := tt_minus_rank_l hZF hω hA hY succ type upper tuple point
      (fun x hx => ((constants x).mp hx).elim (sub x) (fun eq => eq.symm ▸ critical))
    obtain ⟨ec, er⟩ := smem_unique_l I hZF.1 model lower
    subst c₁ R₁
    obtain ⟨B', U', D', w', hB', hc', hp', truth, all⟩ :=
      (stretch hZFC ν μ A Y X c₀ R₀ c R δ K S s t hA hY succ hX hδ hwδ hkδ source lower upper type tuple point).mp ee
    have eqB := ZF.v_unique_l I hZF hB' hB
    subst B'
    have eqU := hZF.1.eq_of_same_members U' U (fun x => (hc' x).trans (constants x).symm)
    subst U'
    have eqD := hp'.unique_l hZF.1 I pool
    subst D'
    have eqw := hZF.1.eq_of_same_members w' w (fun p => (truth p).trans (realized.truth p).symm)
    exact ⟨inacc.mp ii, c₀, R₀, w, lower, minus, realized, eqw ▸ all⟩
  · rintro ⟨ii, c₁, R₁, w, model, _, realized, all⟩
    obtain ⟨ec, er⟩ := smem_unique_l I hZF.1 model lower
    subst c₁ R₁
    refine ⟨⟨top, domain.mpr ⟨realized.tuple, realized.point, realized.constants κ ((constants κ).mpr (Or.inr rfl))⟩⟩,
      inacc.mpr ii, ?_⟩
    exact (stretch hZFC ν μ A Y X c₀ R₀ c R δ K S s t hA hY succ hX hδ hwδ hkδ source lower upper
      type realized.tuple realized.point).mpr ⟨B, U, D, w, hB, constants, pool, realized.truth, all⟩

/-- 一次构造整份语言；程序码、名字列及全部实现的读取使用同一组见证。 -/
theorem ee_definition_l {ω κ n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) (hκ : M.IsLimitOrdinal κ) :
    ∃ B U D, ∃ q : Ee_queries_d M, Ee_language_d hZF ω κ n B U D q := by
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hκ.1
  obtain ⟨a, ha⟩ := KP.exists_pair (ZF.modelsKP hZF) κ κ
  obtain ⟨U, hu⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B a
  have constants x : M.mem x U ↔ M.mem x B ∨ x = κ := (hu x).trans
    (or_congr Iff.rfl ((ha x).trans ⟨fun h => h.elim id id, Or.inl⟩))
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨hwU, _⟩ := tt_constants_finite_l hZF hω hn hκ hB constants
  obtain ⟨g, zg, pg, cg, _, _⟩ := ee_largest_query_l hZF hω pool
  obtain ⟨h, l, zh, ph, ch, _, _⟩ := tt_guard_query_l hZF hω hn ((constants κ).mpr (Or.inr rfl)) pool
  obtain ⟨i, zi, kw, pi, hw, ci, _, _⟩ := ee_inaccessible_query_l hZF hω pool hwU
  obtain ⟨j, v, d, e, ze, pe, ce, hj, _⟩ := ee_query_build_l hZF hω hn hκ hB constants pool
  have numeric : Ee_numeric_d hZF ω κ n U ⟨g, h, i, j⟩ :=
    ⟨l, v, d, e, zg, zh, zi, ze, kw, pg, cg, ph, ch, pi, hw, ci, pe, ce⟩
  exact ⟨B, U, D, ⟨g, h, i, j⟩, numeric.language_l hZF hω hκ hB constants pool hj⟩

end YesMetaZFC.SetTheory.LargeCardinal
