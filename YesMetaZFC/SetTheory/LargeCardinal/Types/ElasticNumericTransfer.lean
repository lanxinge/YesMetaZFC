import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticQuery
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticClauses
import YesMetaZFC.Model.SetTheory.Types.ProgramReflect
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Source.InaccessibleSyntax
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice
import YesMetaZFC.Model.SetTheory.Relations.SliceEmbedding
import YesMetaZFC.Model.SetTheory.Embedding.Relative

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
    M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S → Smem_d I c Y R →
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
    rcases (succ ω).mp (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal (ZF.modelsKP hZF)) hwY) with lt | eq
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

/-! ## 编码表中的实际弹性关系

这里在背景模型内量化原超幂和完整类型。公式不把候选类型当作真值谕示，
只为已有的实际伸展关系提供可作分离与收集的原语言表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def et_stretch_raw_m {d} (ω κ L F X R t D v : Term d) : Formula 1 d := set[d] ⟪∃ b c Y S j w,
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(b, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, S) ∧
  ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ, b, c, j) ∧
  ⌜rd_entry0_m⌝ₚ(⌜t⌝ₛ, w, j) ∧ (∀ p, p ∈ ⌜v⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ p ∈ w)⟫
derive_free_closed et_stretch_raw_m

theorem et_stretch_raw_sat_l {d} (ρ : Env M d) (ω κ L F X R t D v : Term d) :
    Formula.satisfies ρ (et_stretch_raw_m ω κ L F X R t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) (R.eval ρ)
        (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  simp only [et_stretch_raw_m, Et_stretch_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    smem_sat_l I, it_ultra_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def ee_step0_m {d} (ω κ δ n s c X R t τ : Term d) : Formula 1 d := set[d] ⟪∃ L F B U D v,
  L ∈ ⌜δ⌝ₛ ∧ ⌜κ⌝ₛ ∈ L ∧ ⌜τ⌝ₛ ∈ L ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜τ⌝ₛ, B) ∧
  ⌜tt_constants0_m⌝ₚ(⌜τ⌝ₛ, B, U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U, D) ∧
  ⌜tt_truth_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, D, v) ∧
  ⌜ex_quality_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, L, ⌜X⌝ₛ, F) ∧
  ⌜et_stretch_raw_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, L, F, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜t⌝ₛ, D, v)⟫
derive_free_closed ee_step0_m

theorem ee_step0_sat_l {d K} (ρ : Env M d) (ω κ δ n s c X R t τ : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (ee_step0_m ω κ δ n s c X R t τ) ↔
      Ee_step_d hZF (ω.eval ρ) (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (c.eval ρ)
        (X.eval ρ) (R.eval ρ) (t.eval ρ) (τ.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken
  have quality L F B U D v := ex_quality_sat_l (ZF.modelsKP hZF) ((((((ρ.push L).push F).push B).push U).push D).push v)
    (w ω) (w κ) Term.newest.weaken.weaken.weaken.weaken.weaken (w X) Term.newest.weaken.weaken.weaken.weaken
      (by simpa only [w, Definitional.Term.eval_weaken] using source)
  dsimp only [w] at quality
  simp only [ee_step0_m, Ee_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, v_sat_l I hZF.1, tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF), tt_truth_sat_l I (ZF.modelsKP hZF), quality,
    et_stretch_raw_sat_l hZF, Definitional.Term.eval_weaken, and_assoc]
  rfl

/-- 全高度实现的背景公式，供低自然数程序的统一正确性句子使用。 -/
def ee_realized0_m {d} (ω κ δ n s c X R : Term d) : Formula 1 d := set[d] ⟪∃ B U D t,
  ⌜v_m kpair_convention_l⌝ₚ(⌜κ⌝ₛ, B) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, B, U) ∧
  ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U, D) ∧ ⌜tt_truth_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, D, t) ∧
  (∀ τ ∈ ⌜δ⌝ₛ, ⌜ee_step0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜c⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, t, τ))⟫
derive_free_closed ee_realized0_m

theorem ee_realized0_sat_l {d K} (ρ : Env M d) (ω κ δ n s c X R : Term d)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (ee_realized0_m ω κ δ n s c X R) ↔
      Ee_realized_d hZF (ω.eval ρ) (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken
  have read B U D t τ := ee_step0_sat_l hZF (((((ρ.push B).push U).push D).push t).push τ)
    (w ω) (w κ) (w δ) (w n) (w s) (w c) (w X) (w R) Term.newest.weaken .newest
    (by simpa only [w, Definitional.Term.eval_weaken] using source)
  dsimp only [w] at read
  simp only [ee_realized0_m, Ee_realized_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hZF.1, tt_constants0_sat_l hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF),
    tt_truth_sat_l I (ZF.modelsKP hZF), Formula.satisfies_forallMem_iff, read, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 四条弹性查询的统一读取公式

固定代码先于所有实现取定；全称读取同时覆盖全部内部元数的实际元组。
伸展仍是同一扩展器的原超幂关系，源证书由公式自身的前件完整检查。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ee_read_d (ω κ n U D : M.Domain) (q : Ee_queries_d M) : Prop :=
  ∀ ν μ A Y X c R δ K S s t,
    V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
    M.mem ω δ → M.mem κ δ → Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X S → Smem_d I c Y R →
    Tt_realized_d I ω c Y R n s δ U D t →
    (Ee_elastic_d q t ↔ Sc_inaccessible_d ω Y δ ∧ ∃ b Q w, Smem_d I b A Q ∧ Tm_minus_d I ω D t w ∧
      Tt_realized_d I ω b A Q n s δ U D w ∧ ∀ τ, M.mem τ δ → Ee_step_d hZF ω κ δ n s b X S w τ)

def ee_read_m {d} (ω κ n U D g h i e : Term d) : Formula 1 d := set[d] ⟪∀ ν μ A Y X c R δ K S s t,
  ⌜v_m kpair_convention_l⌝ₚ(ν, A) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) →
  ⌜Formula.isSuccessor⌝ₚ(μ, ν) → ⌜v_m kpair_convention_l⌝ₚ(δ, X) → ⌜Formula.isLimitOrdinal⌝ₚ(δ) →
  ⌜ω⌝ₛ ∈ δ → ⌜κ⌝ₛ ∈ δ → ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, K, X, S) →
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
  (⌜ee_elastic_m⌝ₚ(⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ, t) ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ) ∧
    (∃ b Q w, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(b, A, Q) ∧ ⌜tm_minus_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, t, w) ∧
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, b, A, Q, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, w) ∧
      (∀ τ ∈ δ, ⌜ee_step0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, δ, ⌜n⌝ₛ, s, b, X, S, w, τ))))⟫
derive_free_closed ee_read_m

theorem ee_read_sat_l {d} (ρ : Env M d) (ω κ n U D g h i e : Term d) :
    Formula.satisfies ρ (ee_read_m ω κ n U D g h i e) ↔
      Ee_read_d hZF (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [ee_read_m, Ee_read_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, ep_source_sat_l (ZF.modelsKP hZF), smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_iff_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, ee_elastic_sat_l, sc_inaccessible_raw_sat_l, tm_minus_sat_l I hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine forall_congr' fun ν => forall_congr' fun μ => forall_congr' fun A => forall_congr' fun Y =>
    forall_congr' fun X => forall_congr' fun c => forall_congr' fun R => forall_congr' fun δ =>
    forall_congr' fun K => forall_congr' fun S => forall_congr' fun s => forall_congr' fun t => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun source =>
    forall_congr' fun _ => forall_congr' fun _ => ?_
  refine iff_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun b => exists_congr fun Q => exists_congr fun w =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun τ => forall_congr' fun _ => ?_)))))
  let θ := ((((((((((((((((ρ.push ν).push μ).push A).push Y).push X).push c).push R).push δ).push K).push S).push s).push t).push b).push Q).push w).push τ)
  let v (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  simpa only [θ, v, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
    ee_step0_sat_l hZF θ (v ω) (v κ) Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (v n)
      Term.newest.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
      Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      Term.newest.weaken.weaken.weaken.weaken.weaken.weaken Term.newest.weaken .newest
      (by simpa only [θ, v, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using source)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弹性程序的低参数正确性句子

四个程序只携带 ω、内部元数和自然数码；原 κ 常量留在实际名字列中。
因此程序正确性可沿固定低参数的根嵌入往返，而不会假定语义证书绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ee_largest_program0_m : Formula 1 2 :=
  let ω : Term 2 := .bound 0
  let z : Term 2 := .bound 1
  set[2] ⟪⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ n U D p, ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, n, U, D) → ⌜tt_code0_m⌝ₚ(n, U, ⌜z⌝ₛ, p) → p ∈ D ∧
    (∀ μ Y c R s δ t, ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, n, s, δ, U, D, t) →
        (p ∈ t ↔ ∃ ν, ⌜Formula.isSuccessor⌝ₚ(μ, ν))))⟫
theorem ee_largest_program0_closed_l : ee_largest_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_largest_program0_m, Definitional.Formula.FreeClosed]

def ee_largest_program_m {d} (ω z : Term d) : Formula 1 d :=
  ee_largest_program0_m.bind (Fin.cases ω (fun _ => z))

@[simp] theorem ee_largest_program_closed_l {d} (ω z : Term d)
    (hw : ω.freeSupport = []) (hz : z.freeSupport = []) : (ee_largest_program_m ω z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (fun _ => hz)) _).mpr ee_largest_program0_closed_l

def ee_inacc_program0_m : Formula 1 2 :=
  let ω : Term 2 := .bound 0
  let z : Term 2 := .bound 1
  set[2] ⟪⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ n U D kw p, ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, n, U, D) → ⌜ω⌝ₛ ∈ U → ⌜kpair0_m⌝ₚ(kw, ⌜ω⌝ₛ, ⌜ω⌝ₛ) →
    ⌜tt_code2_m⌝ₚ(n, U, ⌜z⌝ₛ, p, n, kw) → p ∈ D ∧
    (∀ c Y R s δ t, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, n, s, δ, U, D, t) →
        (p ∈ t ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ))))⟫
theorem ee_inacc_program0_closed_l : ee_inacc_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_inacc_program0_m, Definitional.Formula.FreeClosed]

def ee_inacc_program_m {d} (ω z : Term d) : Formula 1 d :=
  ee_inacc_program0_m.bind (Fin.cases ω (fun _ => z))

@[simp] theorem ee_inacc_program_closed_l {d} (ω z : Term d)
    (hw : ω.freeSupport = []) (hz : z.freeSupport = []) : (ee_inacc_program_m ω z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (fun _ => hz)) _).mpr ee_inacc_program0_closed_l

def ee_stretch_code_m {d} (ω n κ v d₀ e z p : Term d) : Formula 1 d := set[d] ⟪∃ C kw kn kk,
  ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧ ⌜kpair0_m⌝ₚ(kw, ⌜ω⌝ₛ, ⌜ω⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(kn, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(kk, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧
  (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧ ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, kw, C) ∧
  ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, kn, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜d₀⌝ₛ, ⌜n⌝ₛ, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, kk, C)⟫
derive_free_closed ee_stretch_code_m

def ee_stretch_read_m {d} (ω n v d₀ e z : Term d) : Formula 1 d := set[d] ⟪∀ ν μ X Y Z c R c' R' κ δ K S s f,
  ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜Formula.isSuccessor⌝ₚ(μ, ν) →
  ⌜v_m kpair_convention_l⌝ₚ(δ, Z) → ⌜Formula.isLimitOrdinal⌝ₚ(δ) → ⌜ω⌝ₛ ∈ δ → κ ∈ δ →
  ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, κ, K, Z, S) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c', Y, R') → ⌜fn0_m⌝ₚ(⌜n⌝ₛ, X, s) → δ ∈ X →
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
  (∀ i x, i ∈ ⌜n⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, x, s) ↔ ⌜rd_entry0_m⌝ₚ(i, x, f))) →
  ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, ⌜ω⌝ₛ, f) → ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, ⌜n⌝ₛ, f) →
  ⌜rd_entry0_m⌝ₚ(⌜d₀⌝ₛ, δ, f) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, κ, f) →
    (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c', ⌜z⌝ₛ, f) ↔
      ⌜ee_realized0_m⌝ₚ(⌜ω⌝ₛ, κ, δ, ⌜n⌝ₛ, s, c, Z, S))⟫
derive_free_closed ee_stretch_read_m

def ee_stretch_program0_m : Formula 1 6 :=
  let ω : Term 6 := .bound 0
  let n : Term 6 := .bound 1
  let v : Term 6 := .bound 2
  let d₀ : Term 6 := .bound 3
  let e : Term 6 := .bound 4
  let z : Term 6 := .bound 5
  set[6] ⟪
  ⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜d₀⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜v⌝ₛ, ⌜n⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜d₀⌝ₛ, ⌜v⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜e⌝ₛ, ⌜d₀⌝ₛ) ∧ ⌜ee_stretch_read_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜v⌝ₛ, ⌜d₀⌝ₛ, ⌜e⌝ₛ, ⌜z⌝ₛ)⟫
theorem ee_stretch_program0_closed_l : ee_stretch_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_stretch_program0_m, Definitional.Formula.FreeClosed]

def ee_stretch_program_m {d} (ω n v d₀ e z : Term d) : Formula 1 d :=
  ee_stretch_program0_m.bind (Fin.cases ω (Fin.cases n (Fin.cases v (Fin.cases d₀ (Fin.cases e (fun _ => z))))))

@[simp] theorem ee_stretch_program_closed_l {d} (ω n v d₀ e z : Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hv : v.freeSupport = [])
    (hd : d₀.freeSupport = []) (he : e.freeSupport = []) (hz : z.freeSupport = []) :
    (ee_stretch_program_m ω n v d₀ e z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hn (Fin.cases hv (Fin.cases hd (Fin.cases he (fun _ => hz)))))) _).mpr ee_stretch_program0_closed_l

def ee_numeric0_m : Formula 1 8 :=
  let p : Fin 8 → Term 8 := Term.bound
  set[8] ⟪∃ l v d e zg zh zi ze kw,
    ⌜ee_largest_program_m⌝ₚ(⌜p 0⌝ₛ, zg) ∧ ⌜tt_code0_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 3⌝ₛ, zg, ⌜p 4⌝ₛ) ∧
    ⌜tg_guard_program_m⌝ₚ(⌜p 0⌝ₛ, l, zh) ∧ ⌜tg_guard_code_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, l, zh, ⌜p 5⌝ₛ) ∧
    ⌜ee_inacc_program_m⌝ₚ(⌜p 0⌝ₛ, zi) ∧ ⌜kpair0_m⌝ₚ(kw, ⌜p 0⌝ₛ, ⌜p 0⌝ₛ) ∧
    ⌜tt_code2_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 3⌝ₛ, zi, ⌜p 6⌝ₛ, ⌜p 2⌝ₛ, kw) ∧
    ⌜ee_stretch_program_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, v, d, e, ze) ∧
    ⌜ee_stretch_code_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 1⌝ₛ, v, d, e, ze, ⌜p 7⌝ₛ)⟫

theorem ee_numeric0_closed_l : ee_numeric0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_numeric0_m, Definitional.Formula.FreeClosed]

def ee_numeric_m {d} (ω κ n U g h i j : Term d) : Formula 1 d := ee_numeric0_m.bind
  (Fin.cases ω (Fin.cases κ (Fin.cases n (Fin.cases U (Fin.cases g (Fin.cases h (Fin.cases i (fun _ => j))))))))

@[simp] theorem ee_numeric_closed_l {d} (ω κ n U g h i j : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = []) (hU : U.freeSupport = [])
    (hg : g.freeSupport = []) (hh : h.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (ee_numeric_m ω κ n U g h i j).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hk (Fin.cases hn (Fin.cases hU (Fin.cases hg (Fin.cases hh (Fin.cases hi (fun _ => hj)))))))) _).mpr
      ee_numeric0_closed_l

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_largest_program_sat_l {d} (ρ : Env M d) (ω z : Term d) :
    Formula.satisfies ρ (ee_largest_program_m ω z) ↔ Ee_largest_program_d hZF (ω.eval ρ) (z.eval ρ) := by
  simp only [ee_largest_program_m, Formula.satisfies_bind, ee_largest_program0_m, Ee_largest_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, tt_pool_sat_l I (ZF.modelsKP hZF), tt_code0_sat_l (ZF.modelsKP hZF),
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]
  rfl

theorem ee_inacc_program_sat_l {d} (ρ : Env M d) (ω z : Term d) :
    Formula.satisfies ρ (ee_inacc_program_m ω z) ↔ Ee_inacc_program_d hZF (ω.eval ρ) (z.eval ρ) := by
  simp only [ee_inacc_program_m, Formula.satisfies_bind, ee_inacc_program0_m, Ee_inacc_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, tt_pool_sat_l I (ZF.modelsKP hZF), kpair0_sat_l hZF.1,
    tt_code2_sat_l (ZF.modelsKP hZF), smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_iff_iff,
    sc_inaccessible_raw_sat_l, Definitional.Term.eval_weaken]
  rfl

theorem ee_stretch_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n κ v d₀ e z p : Term d) :
    Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p) ↔
      Ee_stretch_code_d (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [ee_stretch_code_m, Ee_stretch_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem ee_stretch_read_sat_l {d} (ρ : Env M d) (ω n v d₀ e z : Term d) :
    Formula.satisfies ρ (ee_stretch_read_m ω n v d₀ e z) ↔
      Ee_stretch_read_d hZF (ω.eval ρ) (n.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) := by
  simp only [ee_stretch_read_m, Ee_stretch_read_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, ep_source_sat_l (ZF.modelsKP hZF), smem_sat_l I, fn0_sat_l hZF.1,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hZF.1, sc_sat_formula_l I hZF.1, Definitional.Term.eval_weaken]
  refine forall_congr' fun ν => forall_congr' fun μ => forall_congr' fun X => forall_congr' fun Y =>
    forall_congr' fun Z => forall_congr' fun c => forall_congr' fun R => forall_congr' fun c' =>
    forall_congr' fun R' => forall_congr' fun κ => forall_congr' fun δ => forall_congr' fun K =>
    forall_congr' fun S => forall_congr' fun s => forall_congr' fun f => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun source => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => iff_congr Iff.rfl ?_
  let θ := ρ.push ν |>.push μ |>.push X |>.push Y |>.push Z |>.push c |>.push R |>.push c'
    |>.push R' |>.push κ |>.push δ |>.push K |>.push S |>.push s |>.push f
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have read := ee_realized0_sat_l hZF θ (w ω) Term.newest.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken.weaken.weaken (w n) Term.newest.weaken
    Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken
    (by simpa only [θ, w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using source)
  simpa only [θ, w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using read

theorem ee_stretch_program_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω n v d₀ e z : Term d) :
    Formula.satisfies ρ (ee_stretch_program_m ω n v d₀ e z) ↔
      Ee_stretch_program_d (ω.eval ρ) (n.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) := by
  simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, ee_stretch_read_sat_l (ZFC.models_zf_l hZFC)]
  exact ⟨fun ⟨hn, hv, hd, he, hz, sn, sv, sd, read⟩ => ⟨hn, hv, hd, he, hz, sn, sv, sd, fun _ => read⟩,
    fun p => ⟨p.finite, p.next_finite, p.point_finite, p.critical_finite, p.natural, p.next, p.point, p.critical, p.read hZFC⟩⟩

theorem ee_numeric_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n U g h i j : Term d) :
    Formula.satisfies ρ (ee_numeric_m ω κ n U g h i j) ↔
      Ee_numeric_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, j.eval ρ⟩ := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [ee_numeric_m, Formula.satisfies_bind, ee_numeric0_m, Ee_numeric_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ee_largest_program_sat_l hZF, tt_code0_sat_l (ZF.modelsKP hZF), tg_guard_program_sat_l (ZF.modelsKP hZF), tg_guard_code_sat_l (ZF.modelsKP hZF),
    ee_inacc_program_sat_l hZF, kpair0_sat_l hZF.1, tt_code2_sat_l (ZF.modelsKP hZF),
    ee_stretch_program_sat_l hZFC, ee_stretch_code_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一伸展名字列在传递证书层之间搬运

全部存在见证都是原查询列及其实际坐标；只使用传递性和有界绝对性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hE hX

theorem ee_stretch_code_source_l {d} (ρ : Env N d) (ω n κ v d₀ e z p : Term d)
    (valid : Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p)) :
    Ee_stretch_code_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (v.eval ρ).val
      (d₀.eval ρ).val (e.eval ρ).val (z.eval ρ).val (p.eval ρ).val := by
  simp only [ee_stretch_code_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨C, kw, kn, kk, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (ee_stretch_code_m ω n κ v d₀ e z p) := by
    simp only [ee_stretch_code_m, Formula.satisfies_exists_iff]
    exact ⟨C.val, kw.val, kn.val, kk.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (ee_stretch_code_sat_l hE _ _ _ _ _ _ _ _ _).mp full

theorem ee_stretch_code_reflect_l {d} (ρ : Env N d) (ω n κ v d₀ e z p : Term d)
    (code : Ee_stretch_code_d (ω.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (v.eval ρ).val
      (d₀.eval ρ).val (e.eval ρ).val (z.eval ρ).val (p.eval ρ).val) :
    Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p) := by
  obtain ⟨C, kw, kn, kk, pair, hw, hn, hk, old, ew, en, ed, ek⟩ := code
  have hC := (pair.mem_l M hX (p.eval ρ).property).2
  let c₀ : (N).Domain := ⟨C, hC⟩
  let w₀ : (N).Domain := ⟨kw, (rd_entry_transitive_l hX hC ew).2⟩
  let n₀ : (N).Domain := ⟨kn, (rd_entry_transitive_l hX hC en).2⟩
  let k₀ : (N).Domain := ⟨kk, (rd_entry_transitive_l hX hC ek).2⟩
  simp only [ee_stretch_code_m, Formula.satisfies_exists_iff]
  refine ⟨c₀, w₀, n₀, k₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, kpair0_sat_l hE, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨pair, hw, hn, hk, old, ew, en, ed, ek⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弹性语言证书的原公式

代码表的一行保留原四条查询及所有实际读取性质。对该原公式作集合内
选择，得到的仍是原来的 `Ee_language_d`，没有额外语义参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ee_successor_m {d} (ω n U D g : Term d) : Formula 1 d := set[d] ⟪∀ μ Y c R s δ t,
  ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜g⌝ₛ ∈ t ↔ ∃ ν, ⌜Formula.isSuccessor⌝ₚ(μ, ν))⟫
derive_free_closed ee_successor_m

def ee_domain_m {d} (ω κ n U D h : Term d) : Formula 1 d := set[d] ⟪∀ ν μ A Y c R s δ t,
  ⌜v_m kpair_convention_l⌝ₚ(ν, A) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜Formula.isSuccessor⌝ₚ(μ, ν) →
  ⌜ω⌝ₛ ⊆ ν → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜h⌝ₛ ∈ t ↔ ⌜fn0_m⌝ₚ(⌜n⌝ₛ, A, s) ∧ δ ∈ A ∧ ⌜κ⌝ₛ ∈ A)⟫
derive_free_closed ee_domain_m

def ee_inacc_m {d} (ω n U D i : Term d) : Formula 1 d := set[d] ⟪∀ c Y R s δ t,
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜i⌝ₛ ∈ t ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ))⟫
derive_free_closed ee_inacc_m

def ee_domain_pack0_m : Formula 1 7 :=
  let ω := Term.bound 0; let κ := Term.bound 1; let n := Term.bound 2
  let U := Term.bound 3; let D := Term.bound 4; let g := Term.bound 5; let h := Term.bound 6
  set[7] ⟪
  ⌜ω⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ) ∧
  ⌜ee_successor_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜ee_domain_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜h⌝ₛ)⟫

theorem ee_domain_pack0_closed_l : ee_domain_pack0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_domain_pack0_m, Definitional.Formula.FreeClosed]

def ee_domain_pack_m {d} (ω κ n U D g h : Term d) : Formula 1 d :=
  ee_domain_pack0_m.bind (fun i => [ω, κ, n, U, D, g, h].get i)

@[simp] theorem ee_domain_pack_closed_l {d} (ω κ n U D g h : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hg : g.freeSupport = []) (hh : h.freeSupport = []) :
    (ee_domain_pack_m ω κ n U D g h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ee_domain_pack0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hk, hn, hU, hD, hg, hh, fun i => Fin.elim0 i⟩

theorem ee_domain_pack_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ n U D g h : Term d) :
    Formula.satisfies ρ (ee_domain_pack_m ω κ n U D g h) ↔
      Ee_domain_d hZF (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (g.eval ρ) (h.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ee_domain_pack_m, Formula.satisfies_bind, ee_domain_pack0_m, ee_successor_m, ee_domain_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, tt_pool_sat_l I (ZF.modelsKP hZF), Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, fn0_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun p => ⟨p.omega_mem, p.pool, p.successor, p.domain⟩⟩

def ee_language0_m : Formula 1 10 :=
  let ω := Term.bound 0; let κ := Term.bound 1; let n := Term.bound 2
  let B := Term.bound 3; let U := Term.bound 4; let D := Term.bound 5
  let g := Term.bound 6; let h := Term.bound 7; let i := Term.bound 8; let e := Term.bound 9
  set[10] ⟪
  ⌜ee_domain_pack_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ⌝ₛ) ∧ ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ) ∧
  ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ, ⌜U⌝ₛ) ∧
  ⌜g⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜h⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜i⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜D⌝ₛ ∧
  ⌜ee_inacc_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜i⌝ₛ) ∧
  ⌜ee_read_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ) ∧
  ⌜ee_numeric_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ)⟫
@[simp] theorem ee_language0_closed_l : ee_language0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_language0_m, Definitional.Formula.FreeClosed]

def ee_language_m {d} (ω κ n B U D g h i e : Term d) : Formula 1 d :=
  ee_language0_m.bind (fun j => [ω, κ, n, B, U, D, g, h, i, e].get j)

@[simp] theorem ee_language_closed_l {d} (ω κ n B U D g h i e : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hB : B.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hg : g.freeSupport = []) (hh : h.freeSupport = []) (hi : i.freeSupport = []) (he : e.freeSupport = []) :
    (ee_language_m ω κ n B U D g h i e).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ee_language0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hk, hn, hB, hU, hD, hg, hh, hi, he, fun j => Fin.elim0 j⟩

theorem ee_language0_sat_l (hZFC : M.Models ZFC) (ρ : Env M 10) :
    Formula.satisfies ρ ee_language0_m ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
        (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) ⟨ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9⟩ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ee_language0_m, ee_inacc_m, ee_domain_pack_sat_l hZF,
    Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    sc_inaccessible_raw_sat_l, ee_read_sat_l hZF, ee_numeric_sat_l hZFC, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨a, b, c, d, f, j, k, l, v, r, numeric⟩
    exact ⟨a, b, c, d, f, j, k, l, v, fun _ => r, numeric⟩
  · intro q
    exact ⟨q.toEe_domain_d, q.limit, q.rank, q.constants, q.largest_mem, q.domain_mem, q.inaccessible_mem,
      q.stretch_mem, q.inaccessible, q.read hZFC, q.numeric⟩

theorem ee_language_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n B U D g h i e : Term d) :
    Formula.satisfies ρ (ee_language_m ω κ n B U D g h i e) ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_sat_l hZFC]
  rfl

def ee_rebuild_seed_m : Formula 1 10 :=
  let p : Fin 10 → Term 10 := Term.bound
  set[10] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 1⌝ₛ) ∧
    ⌜v_sigma_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ) ∧ ⌜tt_constants0_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ) ∧ ⌜p 9⌝ₛ ∈ ⌜p 5⌝ₛ ∧
    ⌜ee_numeric_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 4⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ)⟫

@[simp] theorem ee_rebuild_seed_closed_l : ee_rebuild_seed_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_rebuild_seed_m, Definitional.Formula.FreeClosed]

def ee_rebuild_m : Formula 1 0 := Formula.forallClosure 10 (.imp ee_rebuild_seed_m ee_language0_m)

theorem ee_rebuild_closed_l : ee_rebuild_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨ee_rebuild_seed_closed_l, ee_language0_closed_l⟩

/-- 目标秩段只需反射这条已证重建句子，无须满足整个 ZFC。 -/
theorem ee_rebuild_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) ee_rebuild_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [Formula.satisfies_imp_iff, ee_rebuild_seed_m, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF), Formula.satisfies_mem_iff,
    ee_numeric_sat_l hZFC, ee_language0_sat_l hZFC]
  rintro ⟨hw, hk, rank, constants, pool, he, numeric⟩
  exact numeric.language_l hZF hw hk rank constants pool he

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在任何对局出现之前固定弹性查询表

索引为模型自己的 (κ,n)，不是宿主自然数。集合内选择只执行一次，
结果是 Vδ 中数据之间的实际函数图；非极限 κ 的行取空集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ee_packet_d (hZF : M.Models ZF) (ω κ n r : M.Domain) : Prop :=
  ∃ B U D g h i e p, Rd_quad_d r B U D p ∧ Rd_quad_d p g h i e ∧
    Ee_language_d hZF ω κ n B U D ⟨g, h, i, e⟩

def ee_packet_m {d} (ω κ n r : Term d) : Formula 1 d := set[d] ⟪∃ B U D g h i e p,
  ⌜rd_quad_m⌝ₚ(⌜r⌝ₛ, B, U, D, p) ∧ ⌜rd_quad_m⌝ₚ(p, g, h, i, e) ∧
  ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, B, U, D, g, h, i, e)⟫
derive_free_closed ee_packet_m

theorem ee_packet_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n r : Term d) :
    Formula.satisfies ρ (ee_packet_m ω κ n r) ↔
      Ee_packet_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [ee_packet_m, Ee_packet_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hZFC.1, ee_language_sat_l hZFC, Definitional.Term.eval_weaken]
  rfl

theorem sc_quad_l {X a b c d : M.Domain} (h : Sc_algebra_d X)
    (ha : M.mem a X) (hb : M.mem b X) (hc : M.mem c X) (hd : M.mem d X) :
    ∃ r, M.mem r X ∧ Rd_quad_d r a b c d := by
  obtain ⟨p, hp, cp⟩ := h.kpair_l hc hd
  obtain ⟨q, hq, cq⟩ := h.kpair_l hb hp
  obtain ⟨r, hr, cr⟩ := h.kpair_l ha hq
  exact ⟨r, hr, p, cp, q, cq, cr⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_packet_exists_l {ω δ X κ n : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hk : M.mem κ δ) (hκ : M.IsLimitOrdinal κ) (hn : M.mem n ω) :
    ∃ r, M.mem r X ∧ Ee_packet_d hZF ω κ n r := by
  obtain ⟨B, U, D, q, language⟩ := ee_definition_l hZF hω hn hκ
  have algebra := sc_v_algebra_l hZFC hδ hX
  have trans := v_transitive_l I hX
  have hB := ZF.v_mem_l I hZF language.rank hX hk
  have hU := tt_constants_rank_l hZF hX hδ hk language.rank language.constants
  have hD := language.pool.rank_mem_l (ZF.modelsKP hZF) hω hX hδ (ZF.v_ordinal_mem_l I hZF hX hwδ) hn hU
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra (trans D hD q.largest language.largest_mem)
    (trans D hD q.domain language.domain_mem) (trans D hD q.inaccessible language.inaccessible_mem)
    (trans D hD q.stretch language.stretch_mem)
  obtain ⟨r, hr, cr⟩ := sc_quad_l algebra hB hU hD hp
  exact ⟨r, hr, B, U, D, q.largest, q.domain, q.inaccessible, q.stretch, p, cr, cp, language⟩

def Ee_catalog_d (ω δ X P Γ : M.Domain) : Prop := M.IsCartesianProduct I P δ ω ∧ Fn0_d P X Γ ∧
  ∀ κ n x r, M.mem κ δ → M.mem n ω → M.IsLimitOrdinal κ → KPair_d M x κ n →
    Rd_entry_d x r Γ → Ee_packet_d hZF ω κ n r

/-- 原公式的全定义关系在模型内统一化；表和每个键值对都实际存在。 -/
theorem ee_catalog_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) :
    ∃ P Γ, Ee_catalog_d hZFC ω δ X P Γ ∧ M.MemberSubset Γ X := by
  classical
  obtain ⟨P, product⟩ := ZF.exists_cartesianProduct hZF I δ ω
  obtain ⟨e, he, heω⟩ := hω.1.1
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push e
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ κ n,
    ⌜kpair0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ, κ, n) ∧
    ((⌜Formula.isLimitOrdinal⌝ₚ(κ) ∧ ⌜ee_packet_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ, κ, n, ⌜(.newest : Term 4)⌝ₛ)) ∨
      (¬ ⌜Formula.isLimitOrdinal⌝ₚ(κ) ∧ ⌜(.newest : Term 4)⌝ₛ = ⌜(.bound 2 : Term 4)⌝ₛ))⟫ }
  have sat x r : φ.denote ρ x r ↔ ∃ κ n, KPair_d M x κ n ∧
      ((M.IsLimitOrdinal κ ∧ Ee_packet_d hZF ω κ n r) ∨ (¬ M.IsLimitOrdinal κ ∧ r = e)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_isLimitOrdinal_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, kpair0_sat_l hZF.1, ee_packet_sat_l hZFC,
      Definitional.Term.eval_weaken]
    rfl
  have heX := v_transitive_l I hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) e heω
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := P) (Y := X) (fun x hx => by
    obtain ⟨κ, hk, n, hn, code⟩ := (product x).mp hx
    by_cases limit : M.IsLimitOrdinal κ
    · obtain ⟨r, hr, packet⟩ := ee_packet_exists_l hZFC hω hδ hwδ hX hk limit hn
      exact ⟨r, hr, (sat x r).mpr ⟨κ, n, code, Or.inl ⟨limit, packet⟩⟩⟩
    · exact ⟨e, heX, (sat x e).mpr ⟨κ, n, code, Or.inr ⟨limit, rfl⟩⟩⟩)
  refine ⟨P, Γ, ⟨product, fn0_of_function_l (ZF.modelsKP hZF) fn, fun κ n x r _ _ limit code entry => ?_⟩, ?_⟩
  · obtain ⟨κ', n', code', good⟩ := (sat x r).mp (all x r entry)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code' code
    exact good.elim And.right (fun h => (h.1 limit).elim)
  · intro p hp
    obtain ⟨x, r, pair⟩ := fn.1.1 p hp
    have entry := (show M.PairMember I x r Γ from ⟨p, pair, hp⟩)
    obtain ⟨κ, hk, n, hn, key⟩ := (product x).mp (fn.input_mem_of_pairMember entry)
    have algebra := sc_v_algebra_l hZFC hδ hX
    have hnX := v_transitive_l I hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) n hn
    obtain ⟨x', hx', key'⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF hX hk) hnX
    have eq := kpair_unique_l M hZF.1 key' key
    obtain ⟨p', hp', pair'⟩ := algebra.kpair_l (eq ▸ hx') (fn.output_mem_of_pairMember entry)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两个原关系切片之间的完整数值语言

数值程序经同一根的两条实际嵌入传输。查询列先在源共同层中完整读取，
经同一共同图送到目标共同层，再回到目标反射切片；非数值参数不冒充根像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.numeric_l
    {Ω b B R₀ c X R d Y S j k C₀ w₀ z₀ w z w' z' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (eb : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x C})
    (nd : Nonempty {y : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem y D})
    (iC : Rd_entry_d C₀ C.val j) (iD : Rd_entry_d C₀ D.val k)
    (ρ : Env (rt_model_l C nc) 8) (η : Env (rt_model_l D nd) 8)
    (points : ∀ i, Rd_entry_d (ρ.bound i).val.val (η.bound i).val.val t)
    (hw : (ρ.bound 0).val.val = w) (inside : ∀ x, Rd_entry_d x V S → Rd_entry_d x D.val S)
    (A : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (hA : Rd_entry_d A.val U R) (names : Tn_names_d (ρ.bound 2).val (ρ.bound 3).val A)
    (valid : Formula.satisfies ρ ee_numeric0_m) : Formula.satisfies η ee_numeric0_m := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  let Vn : Yn.Domain := ⟨V,common.right_rank.2.1⟩
  let wn : Xn.Domain := ⟨w,source.member⟩
  let wn' : Yn.Domain := ⟨w',target.member⟩
  have hω : (ρ.bound 0).val = wn := Subtype.ext hw
  have ru : V_d (kp_pair_l hX) (⟨L,common.left_rank.1⟩ : Xn.Domain) Un :=
    (rr_rank_native_l I mx.2.1 hX _ _).mp common.left_rank
  have rv : V_d (kp_pair_l hY) (⟨l,common.right_rank.1⟩ : Yn.Domain) Vn :=
    (rr_rank_native_l I my.2.1 hY _ _).mp common.right_rank
  have ut : Xn.TransitiveSet Un := v_transitive_l (kp_pair_l hX) ru
  have vt : Yn.TransitiveSet Vn := v_transitive_l (kp_pair_l hY) rv
  have low i : Xn.mem (ρ.bound i).val Un :=
    ((common.carrier _).mp (common.injection.1.input_mem_of_pairMember (points i))).2
  have hwU : Xn.mem wn Un := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem a Un) hω) (low 0)
  have ex := left.extensional_l hZF hΩ mb mx eb
  have ey := right.extensional_l hZF hΩ mb my eb
  have digits := common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source target ut hwU
  have hwη : (η.bound 0).val.val = w' :=
    common.injection.1.1.2 w _ w' (hw ▸ points 0) digits.1
  have hwV : Yn.mem wn' Vn := (common.image w').mpr
    ⟨w,(common.carrier w).mpr ⟨source.member,hwU⟩,digits.1⟩
  have omega : Xn.IsOmega wn := source.omega_l I (ZF.modelsKP hZF) hΩ hX.1
  have omega' : Yn.IsOmega wn' := target.omega_l I (ZF.modelsKP hZF) hΩ hY.1
  let nu : Nonempty {x : Xn.Domain // Xn.mem x Un} := ⟨⟨wn,hwU⟩⟩
  let nv : Nonempty {y : Yn.Domain // Yn.mem y Vn} := ⟨⟨wn',hwV⟩⟩
  -- 名字域也由同一共同图进入目标；有界名字公式识别其完整成员。
  obtain ⟨A',hA',AA⟩ := common.injection.1.2.2 A.val ((common.carrier A.val).mpr ⟨A.property,hA⟩)
  let An : Yn.Domain := ⟨A',hA'⟩
  have hAV : Yn.mem An Vn := (common.image A').mpr ⟨A.val,
    (common.carrier A.val).mpr ⟨A.property,hA⟩,AA⟩
  let a : Env (rt_model_l Un nu) 3 :=
    ⟨Fin.cases ⟨A,hA⟩ (Fin.cases ⟨(ρ.bound 3).val,low 3⟩ (fun _ => ⟨(ρ.bound 2).val,low 2⟩)),fun _ => ⟨wn,hwU⟩⟩
  let a' : Env Yn 3 := ⟨Fin.cases An (Fin.cases (η.bound 3).val (fun _ => (η.bound 2).val)),fun _ => wn'⟩
  have names' : Tn_names_d (η.bound 2).val (η.bound 3).val An :=
    (tn_names0_sat_l hY a' (.bound 2) (.bound 1) .newest).mp
      ((rr_native_delta_l I mx.2.1 my.2.1 Un ut nu common.carrier common.injection common.pred
        (tn_names0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs)
        (tn_names0_delta_l ..) a a' (Fin.cases AA (Fin.cases (points 3) (fun _ => points 2)))).mp
          ((tn_names0_sat_l hX _ (.bound 2) (.bound 1) .newest).mpr names))
  have hAD : Yn.mem An D := inside An.val hAV
  simp only [ee_numeric0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at valid
  refine valid.elim fun l₀ h => h.elim fun v h => h.elim fun d₀ h => h.elim fun e h =>
    h.elim fun zg h => h.elim fun zh h => h.elim fun zi h => h.elim fun ze h =>
    h.elim fun kw facts => ?_
  have pg := facts.1
  have cg := facts.2.1
  have ph := facts.2.2.1
  have ch := facts.2.2.2.1
  have pi := facts.2.2.2.2.1
  have pair := facts.2.2.2.2.2.1
  have ci := facts.2.2.2.2.2.2.1
  have pe := facts.2.2.2.2.2.2.2.1
  have ce := facts.2.2.2.2.2.2.2.2
  let ε := ρ.push l₀ |>.push v |>.push d₀ |>.push e |>.push zg |>.push zh |>.push zi |>.push ze |>.push kw
  have metaG := pg
  simp only [ee_largest_program_m,Formula.satisfies_bind,ee_largest_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaG
  have hg : Xn.mem zg.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem zg.val a) hω) metaG.1
  have metaI := pi
  simp only [ee_inacc_program_m,Formula.satisfies_bind,ee_inacc_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaI
  have hi : Xn.mem zi.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem zi.val a) hω) metaI.1
  have metaH := ph
  simp only [tg_guard_program_m,Formula.satisfies_bind,tg_guard_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaH
  have hl : Xn.mem l₀.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem l₀.val a) hω) metaH.1
  have hh : Xn.mem zh.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem zh.val a) hω) metaH.2.1
  have metaE := pe
  simp only [ee_stretch_program_m,Formula.satisfies_bind,ee_stretch_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaE
  obtain ⟨hn,hv,hd,he,hz,_⟩ := metaE
  have hn : Xn.mem (ρ.bound 2).val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem (ρ.bound 2).val a) hω) hn
  have hv : Xn.mem v.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem v.val a) hω) hv
  have hd : Xn.mem d₀.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem d₀.val a) hω) hd
  have he : Xn.mem e.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem e.val a) hω) he
  have hz : Xn.mem ze.val wn := Eq.mp (congrArg (fun a : Xn.Domain => Xn.mem ze.val a) hω) hz
  have cg₀ := tt_code0_source_l hX ct nc ε (.bound 11) (.bound 12) (.bound 4) (.bound 13) cg
  have ch₀ := tg_guard_code_source_l hX ct nc ε (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) ch
  have ci₀ := tt_code2_source_l hX ct nc ε (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) ci
  have ce₀ := ee_stretch_code_source_l hX.1 ct nc ε (.bound 9) (.bound 11) (.bound 10) (.bound 7)
    (.bound 6) (.bound 5) (.bound 1) (.bound 16) ce
  have hkw : Xn.mem kw.val Un := by
    obtain ⟨_,F,_,_,_,_,cp,slots⟩ := ci₀
    have hF := (cp.mem_l Xn ut (low 6)).2
    obtain ⟨i,ni⟩ := num_exists_l hX 1
    exact (rd_entry_transitive_l ut hF (slots 1 i ni)).2
  have all : ∀ i, Xn.mem (ε.bound i).val Un :=
    Fin.cases hkw (Fin.cases (ut wn hwU _ hz) (Fin.cases (ut wn hwU _ hi)
      (Fin.cases (ut wn hwU _ hh) (Fin.cases (ut wn hwU _ hg) (Fin.cases (ut wn hwU _ he)
        (Fin.cases (ut wn hwU _ hd) (Fin.cases (ut wn hwU _ hv) (Fin.cases (ut wn hwU _ hl) low))))))))
  let εU : Env (rt_model_l Un nu) 17 := ⟨fun i => ⟨(ε.bound i).val,all i⟩,fun _ => ⟨wn,hwU⟩⟩
  have values (i : Fin 9) : ∃ y : (rt_model_l D nd).Domain,
      Rd_entry_d (ε.bound (i.castAdd 8)).val.val y.val.val t := by
    obtain ⟨y,hy,xy⟩ := common.injection.1.2.2 (ε.bound (i.castAdd 8)).val.val
      ((common.carrier _).mpr ⟨(ε.bound _).val.property,all _⟩)
    exact ⟨⟨⟨y,hy⟩,inside y ((common.image y).mpr
      ⟨_,(common.carrier _).mpr ⟨(ε.bound _).val.property,all _⟩,xy⟩)⟩,xy⟩
  obtain ⟨v',images⟩ := Classical.axiomOfChoice values
  let υ := η.push (v' 8) |>.push (v' 7) |>.push (v' 6) |>.push (v' 5) |>.push (v' 4)
    |>.push (v' 3) |>.push (v' 2) |>.push (v' 1) |>.push (v' 0)
  have linked : ∀ i, Rd_entry_d (ε.bound i).val.val (υ.bound i).val.val t :=
    Fin.cases (images 0) (Fin.cases (images 1) (Fin.cases (images 2) (Fin.cases (images 3)
      (Fin.cases (images 4) (Fin.cases (images 5) (Fin.cases (images 6)
        (Fin.cases (images 7) (Fin.cases (images 8) points))))))))
  have targetLow i : Yn.mem (υ.bound i).val Vn := (common.image _).mpr
    ⟨_,common.injection.1.input_mem_of_pairMember (linked i),linked i⟩
  let υV : Env (rt_model_l Vn nv) 17 := ⟨fun i => ⟨(υ.bound i).val,targetLow i⟩,fun _ => ⟨wn',hwV⟩⟩
  have column (φ : Formula 1 17) (closed : φ.FreeClosed) :
      Formula.satisfies εU φ → Formula.satisfies υV φ :=
    (rr_native_slice_l I mx.2.1 my.2.1 Un Vn nu nv common.carrier common.injection common.image
      common.pred φ closed εU υV linked).mp
  have move {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (ix : Fin n → Fin 17)
      (f : Fin n → Term 17) (coords : ∀ i, f i = .bound (ix i))
      (low : ∀ i, (ε.bound (ix i)).val = wn ∨ Xn.mem (ε.bound (ix i)).val wn)
      (truth : Formula.satisfies ε (φ.bind f)) : Formula.satisfies υ (φ.bind f) := by
    have eqρ : (Definitional.Env.substitute ε f).bound = (ε.reindex ix).bound := by
      funext i
      change (f i).eval ε = ε.bound (ix i)
      rw [coords i]
      rfl
    have eqυ : (Definitional.Env.substitute υ f).bound = (υ.reindex ix).bound := by
      funext i
      change (f i).eval υ = υ.bound (ix i)
      rw [coords i]
      rfl
    have truth := (Formula.closed_env_l φ closed eqρ).mp ((Formula.satisfies_bind ε f φ).mp truth)
    have moved := (smap_numeric_slice_peer_l hZF hΩ mb mx my left right eb ex ey root source target
      C D ct dt nc nd iC iD φ closed (ε.reindex ix) (υ.reindex ix) (fun i => by
        rcases low i with eq | hi
        · have eq₀ := congrArg Subtype.val eq
          have point : Rd_entry_d w (υ.bound (ix i)).val.val t :=
            Eq.mp (congrArg (fun x => Rd_entry_d x (υ.bound (ix i)).val.val t) eq₀) (linked (ix i))
          exact Or.inl ⟨eq₀,common.injection.1.1.2 w _ w' point digits.1⟩
        · obtain ⟨a,_,ha⟩ := (source.image _).mp hi
          exact Or.inr ⟨a,ha,(digits.2 a _).mpr ⟨_,ha,linked (ix i)⟩⟩)).mp truth
    exact (Formula.satisfies_bind υ f φ).mpr ((Formula.closed_env_l φ closed eqυ).mpr moved)
  have hω' : (η.bound 0).val = wn' := Subtype.ext hwη
  have hwD : Yn.mem wn' D := hω' ▸ (η.bound 0).property
  simp only [ee_numeric0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff]
  refine ⟨v' 8,v' 7,v' 6,v' 5,v' 4,v' 3,v' 2,v' 1,v' 0,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · let ix : Fin 2 → Fin 17 := Fin.cases 9 (fun _ => 4)
    let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 4)
    exact move ee_largest_program0_m ee_largest_program0_closed_l ix f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hω) (fun _ => Or.inr hg)) pg
  · have q := column _ (by simp -implicitDefEqProofs)
      (tt_code0_reflect_l hX ut nu omega hwU εU (.bound 11) (.bound 12) (.bound 4) (.bound 13) hA names cg₀)
    exact tt_code0_reflect_l hY dt nd omega' hwD υ (.bound 11) (.bound 12) (.bound 4) (.bound 13) hAD names'
      (tt_code0_source_l hY vt nv υV (.bound 11) (.bound 12) (.bound 4) (.bound 13) q)
  · let ix : Fin 3 → Fin 17 := Fin.cases 9 (Fin.cases 8 (fun _ => 3))
    let f : Fin 3 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 8) (fun _ => .bound 3))
    exact move tg_guard_program0_m tg_guard_program0_closed_l ix f
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      (Fin.cases (Or.inl hω) (Fin.cases (Or.inr hl) (fun _ => Or.inr hh))) ph
  · have q := column _ (by simp -implicitDefEqProofs)
      (tg_guard_code_reflect_l hX ut nu εU (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) hA names ch₀)
    exact tg_guard_code_reflect_l hY dt nd υ (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) hAD names'
      (tg_guard_code_source_l hY vt nv υV (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) q)
  · let ix : Fin 2 → Fin 17 := Fin.cases 9 (fun _ => 2)
    let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 2)
    exact move ee_inacc_program0_m ee_inacc_program0_closed_l ix f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hω) (fun _ => Or.inr hi)) pi
  · let φ : Formula 1 17 := kpair0_m (.bound 0) (.bound 9) (.bound 9)
    have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
    have q := (rt_model_delta_l ct nc (kpair0_delta_l (.bound 0) (.bound 9) (.bound 9)) ε).mp pair
    have qU : Formula.satisfies (image_env_l (M := rt_model_l Un nu) (N := Xn) Subtype.val εU) φ :=
      (Formula.closed_env_l φ closed
        (ρ := image_env_l (M := rt_model_l C nc) (N := Xn) Subtype.val ε)
        (η := image_env_l (M := rt_model_l Un nu) (N := Xn) Subtype.val εU) rfl).mp q
    have qV := column φ closed
      ((rt_model_delta_l ut nu (kpair0_delta_l (.bound 0) (.bound 9) (.bound 9)) εU).mpr qU)
    have qD : Formula.satisfies (image_env_l (M := rt_model_l D nd) (N := Yn) Subtype.val υ) φ :=
      (Formula.closed_env_l φ closed
        (ρ := image_env_l (M := rt_model_l Vn nv) (N := Yn) Subtype.val υV)
        (η := image_env_l (M := rt_model_l D nd) (N := Yn) Subtype.val υ) rfl).mp
          ((rt_model_delta_l vt nv (kpair0_delta_l (.bound 0) (.bound 9) (.bound 9)) υV).mp qV)
    exact (rt_model_delta_l dt nd (kpair0_delta_l (.bound 0) (.bound 9) (.bound 9)) υ).mpr qD
  · have q := column _ (by simp -implicitDefEqProofs)
      (tt_code2_reflect_l hX ut nu omega hwU εU (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) hA names ci₀)
    exact tt_code2_reflect_l hY dt nd omega' hwD υ (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) hAD names'
      (tt_code2_source_l hY vt nv υV (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) q)
  · let ix : Fin 6 → Fin 17 := Fin.cases 9 (Fin.cases 11 (Fin.cases 7 (Fin.cases 6 (Fin.cases 5 (fun _ => 1)))))
    let f : Fin 6 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 11) (Fin.cases (.bound 7)
      (Fin.cases (.bound 6) (Fin.cases (.bound 5) (fun _ => .bound 1)))))
    exact move ee_stretch_program0_m ee_stretch_program0_closed_l ix f
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
      (Fin.cases (Or.inl hω) (Fin.cases (Or.inr hn) (Fin.cases (Or.inr hv) (Fin.cases (Or.inr hd)
        (Fin.cases (Or.inr he) (fun _ => Or.inr hz)))))) pe
  · have q := column _ (by simp -implicitDefEqProofs)
      (ee_stretch_code_reflect_l hX.1 ut nu εU (.bound 9) (.bound 11) (.bound 10) (.bound 7)
        (.bound 6) (.bound 5) (.bound 1) (.bound 16) ce₀)
    exact ee_stretch_code_reflect_l hY.1 dt nd υ (.bound 9) (.bound 11) (.bound 10) (.bound 7)
      (.bound 6) (.bound 5) (.bound 1) (.bound 16)
      (ee_stretch_code_source_l hY.1 vt nv υV (.bound 9) (.bound 11) (.bound 10) (.bound 7)
        (.bound 6) (.bound 5) (.bound 1) (.bound 16) q)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两个根像之间保持原弹性查询

低自然数程序经共同根往返；含新 κ 常量的实际列图经传递层读取和回收。
两条路线在同一原查询处汇合，不把一边的全称语义直接当成另一边的语义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_numeric_transfer_l {ω r B R w z x X S y Y T π σ C₀ C D A : M.Domain}
    (hω : M.IsOmega ω) (numbers : Rr_layer_d I ω B R w z) (rootExt : Rf_ext_d I B R)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smdl_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    (ρ : Env (rt_model_l C nc) 8) (η : Env (rt_model_l D nd) 8)
    (same : ∀ i, (ρ.bound i).val = (η.bound i).val) (hωρ : (ρ.bound 0).val = ω)
    (hA : M.mem A D) (names : Tn_names_d (η.bound 2).val (η.bound 3).val A)
    (valid : Formula.satisfies ρ ee_numeric0_m) : Formula.satisfies η ee_numeric0_m := by
  simp only [ee_numeric0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨l, v, d, e, zg, zh, zi, ze, kw, pg, cg, ph, ch, pi, pair, ci, pe, ce⟩ := valid
  let ε := ρ.push l |>.push v |>.push d |>.push e |>.push zg |>.push zh |>.push zi |>.push ze |>.push kw
  have metaG := pg
  simp only [ee_largest_program_m, Formula.satisfies_bind, ee_largest_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaG
  have hg : M.mem zg.val ω := hωρ ▸ metaG.1
  have metaI := pi
  simp only [ee_inacc_program_m, Formula.satisfies_bind, ee_inacc_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaI
  have hi : M.mem zi.val ω := hωρ ▸ metaI.1
  have metaH := ph
  simp only [tg_guard_program_m, Formula.satisfies_bind, tg_guard_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaH
  have hl : M.mem l.val ω := hωρ ▸ metaH.1
  have hh : M.mem zh.val ω := hωρ ▸ metaH.2.1
  have metaE := pe
  simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaE
  obtain ⟨hn, hv, hd, he, hz, _⟩ := metaE
  have hn : M.mem (ρ.bound 2).val ω := hωρ ▸ hn
  have hv : M.mem v.val ω := hωρ ▸ hv
  have hd : M.mem d.val ω := hωρ ▸ hd
  have he : M.mem e.val ω := hωρ ▸ he
  have hz : M.mem ze.val ω := hωρ ▸ hz
  have cgM := tt_code0_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 12) (.bound 4) (.bound 13) cg
  have chM := tg_guard_code_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) ch
  have ciM := tt_code2_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) ci
  have ceM := ee_stretch_code_source_l hZF.1 ct nc ε (.bound 9) (.bound 11) (.bound 10) (.bound 7)
    (.bound 6) (.bound 5) (.bound 1) (.bound 16) ce
  have pairM := (rt_model_delta_l ct nc (kpair0_delta_l ..) _).mp pair
  simp only [kpair0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at pairM
  have hwη : (η.bound 0).val = ω := (same 0).symm.trans hωρ
  have hωD : M.mem ω D := hwη ▸ (η.bound 0).property
  have num a (ha : M.mem a ω) := dt ω hωD a ha
  have hkw : M.mem kw.val D := by
    obtain ⟨_, F, _, _, _, _, cp, slots⟩ := ciM
    have hF := (cp.mem_l M dt ((same 6).symm ▸ (η.bound 6).property)).2
    obtain ⟨i, ni⟩ := num_exists_l (ZF.modelsKP hZF) 1
    exact (rd_entry_transitive_l dt hF (slots 1 i ni)).2
  let l' : (rt_model_l D nd).Domain := ⟨l.val, num _ hl⟩
  let v' : (rt_model_l D nd).Domain := ⟨v.val, num _ hv⟩
  let d' : (rt_model_l D nd).Domain := ⟨d.val, num _ hd⟩
  let e' : (rt_model_l D nd).Domain := ⟨e.val, num _ he⟩
  let zg' : (rt_model_l D nd).Domain := ⟨zg.val, num _ hg⟩
  let zh' : (rt_model_l D nd).Domain := ⟨zh.val, num _ hh⟩
  let zi' : (rt_model_l D nd).Domain := ⟨zi.val, num _ hi⟩
  let ze' : (rt_model_l D nd).Domain := ⟨ze.val, num _ hz⟩
  let kw' : (rt_model_l D nd).Domain := ⟨kw.val, hkw⟩
  let υ := η.push l' |>.push v' |>.push d' |>.push e' |>.push zg' |>.push zh' |>.push zi' |>.push ze' |>.push kw'
  have equal : ∀ i, (ε.bound i).val = (υ.bound i).val :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl same))))))))
  have move {a} (φ : Formula 1 a) (hc : φ.FreeClosed) (f : Fin a → Term 17)
      (closed : ∀ i, (f i).freeSupport = [])
      (low : ∀ i, ((f i).eval ε).val = ω ∨ M.mem ((f i).eval ε).val ω)
      (truth : Formula.satisfies ε (φ.bind f)) : Formula.satisfies υ (φ.bind f) := by
    have same' i : ((f i).eval ε).val = ((f i).eval υ).val := by
      have eq := term_closed_env_l (f i) (closed i)
        (ρ := image_env_l (M := rt_model_l C nc) (N := M) Subtype.val ε)
        (η := image_env_l (M := rt_model_l D nd) (N := M) Subtype.val υ) (funext equal)
      simpa only [@eval_image_env_l (rt_model_l C nc) M Subtype.val,
        @eval_image_env_l (rt_model_l D nd) M Subtype.val] using eq
    apply (Formula.satisfies_bind υ f φ).mpr
    exact (smap_numeric_peer_l hZF hω numbers rootExt xt yt mb mx my j k iC iD ct dt nc nd φ hc
      (Definitional.Env.substitute ε f) (Definitional.Env.substitute υ f) same' low).mp ((Formula.satisfies_bind ε f φ).mp truth)
  simp only [ee_numeric0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff]
  refine ⟨l', v', d', e', zg', zh', zi', ze', kw', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 4)
    exact move ee_largest_program0_m ee_largest_program0_closed_l f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hωρ) (fun _ => Or.inr hg)) pg
  · apply tt_code0_reflect_l (ZF.modelsKP hZF) dt nd hω hωD υ (.bound 11) (.bound 12) (.bound 4) (.bound 13) hA names
    exact (same 2) ▸ (same 3) ▸ (same 4) ▸ cgM
  · let f : Fin 3 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 8) (fun _ => .bound 3))
    exact move tg_guard_program0_m tg_guard_program0_closed_l f (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      (Fin.cases (Or.inl hωρ) (Fin.cases (Or.inr hl) (fun _ => Or.inr hh))) ph
  · apply tg_guard_code_reflect_l (ZF.modelsKP hZF) dt nd υ (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) hA names
    exact (same 2) ▸ (same 1) ▸ (same 3) ▸ (same 5) ▸ chM
  · let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 2)
    exact move ee_inacc_program0_m ee_inacc_program0_closed_l f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hωρ) (fun _ => Or.inr hi)) pi
  · apply (rt_model_delta_l dt nd (kpair0_delta_l ..) υ).mpr
    apply (kpair0_sat_l hZF.1 ..).mpr
    simp only [@eval_image_env_l (rt_model_l D nd) M Subtype.val, υ,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact (same 0) ▸ pairM
  · apply tt_code2_reflect_l (ZF.modelsKP hZF) dt nd hω hωD υ (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) hA names
    exact (same 2) ▸ (same 3) ▸ (same 6) ▸ ciM
  · let f : Fin 6 → Term 17 :=
      Fin.cases (.bound 9) (Fin.cases (.bound 11) (Fin.cases (.bound 7) (Fin.cases (.bound 6) (Fin.cases (.bound 5) (fun _ => .bound 1)))))
    exact move ee_stretch_program0_m ee_stretch_program0_closed_l f
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
      (Fin.cases (Or.inl hωρ) (Fin.cases (Or.inr hn) (Fin.cases (Or.inr hv) (Fin.cases (Or.inr hd)
        (Fin.cases (Or.inr he) (fun _ => Or.inr hz)))))) pe
  · apply ee_stretch_code_reflect_l hZF.1 dt nd υ (.bound 9) (.bound 11) (.bound 10) (.bound 7)
      (.bound 6) (.bound 5) (.bound 1) (.bound 16)
    exact (same 0) ▸ (same 2) ▸ (same 1) ▸ (same 7) ▸ ceM

end YesMetaZFC.SetTheory.LargeCardinal
