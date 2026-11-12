import YesMetaZFC.Model.SetTheory.Types.MoveRead
import YesMetaZFC.SetTheory.Ord.UnboundedFiber
import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.Model.SetTheory.Internal.FiniteTailSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Types.MoveQuote
import YesMetaZFC.SetTheory.CumulativeFinite

/-! # Neeman 定义 3.27：实际局部不可分辨序数

所有 V(ν+ω) 中的指定序数类型共用一个查询域，其值属于该域的幂集。
ZF 收集给出一个无界重复的完整类型；由此可在任意下界以上选择一对，
并使两者相隔至少 ω。参数域恰为 V(δ+ω)，没有缩为外部标准公式族。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 两个指定序数在各自 V(ν+ω) 中实现同一完整内部类型。 -/
def Li_pair_d (ω e U D ν μ : M.Domain) : Prop :=
  M.IsOrdinal ν ∧ M.IsOrdinal μ ∧ M.mem ν μ ∧
    ∃ t, Li_type_d I ω e U D ν t ∧ Li_type_d I ω e U D μ t

def li_pair_m {d} (ω e U D ν μ : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜ν⌝ₛ) ∧ ⌜Formula.isOrdinal⌝ₚ(⌜μ⌝ₛ) ∧ ⌜ν⌝ₛ ∈ ⌜μ⌝ₛ ∧
  (∃ t, ⌜li_type_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜ν⌝ₛ, t) ∧
    ⌜li_type_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜μ⌝ₛ, t))⟫
derive_free_closed li_pair_m

theorem li_pair_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e U D ν μ : Term d) :
    Formula.satisfies ρ (li_pair_m ω e U D ν μ) ↔
      Li_pair_d I (ω.eval ρ) (e.eval ρ) (U.eval ρ) (D.eval ρ) (ν.eval ρ) (μ.eval ρ) := by
  simp only [li_pair_m, Li_pair_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, li_type_sat_l I hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)

include hZF in
/-- 一个实际完整类型在无界多个高度重复；参数秩与所有内部查询均固定。 -/
theorem li_unbounded_l {ω e γ U D : M.Domain} (hω : M.IsOmega ω) (hU : V_d I γ U) :
    ∃ t, ∀ β, M.IsOrdinal β → ∃ ν, M.IsOrdinal ν ∧ M.mem γ ν ∧ M.mem β ν ∧
      Li_type_d I ω e U D ν t := by
  obtain ⟨P, power⟩ := ZF.exists_powerSet hZF D
  let φ : BinarySchema 4 := { body := li_type_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let ρ : Env M 4 := ⟨Fin.cases D (Fin.cases U (Fin.cases e (fun _ => ω))), fun _ => ω⟩
  have read ν t : φ.denote ρ ν t ↔ Li_type_d I ω e U D ν t := li_type_sat_l I (ZF.modelsKP hZF) ..
  obtain ⟨t, _, all⟩ := ZF.ordinal_unbounded_fiber_l hZF φ ρ (v_ordinal_l I hU) (P := P) (by
    intro ν hν hγν
    obtain ⟨t, h⟩ := li_type_exists_l I hZF hω hU hν hγν
    have sub : M.MemberSubset t D := by
      obtain ⟨_, _, _, _, _, _, _, _, _, truth⟩ := h
      exact fun p hp => ((truth p).mp hp).1
    exact ⟨t, (power t).mpr sub, (read ν t).mpr h⟩)
  exact ⟨t, fun β hβ => (all β hβ).imp fun ν h => ⟨h.1, h.2.1, h.2.2.1, (read ν t).mp h.2.2.2⟩⟩

include hZF in
/-- 自动构造原参数带及无界多对局部不可分辨序数，并保留 ν+ω<μ 的明确间隔。 -/
theorem li_indiscernibles_l {ω δ : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) :
    ∃ e γ U D, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition I γ δ ω ∧
      V_d I γ U ∧ Tt_pool_d I ω e U D ∧ ∀ α, M.IsOrdinal α →
        ∃ ν μ ξ, M.mem α ν ∧ M.mem δ ν ∧ M.IsOrdinalAddition I ξ ν ω ∧ M.mem ξ μ ∧
          Li_pair_d I ω e U D ν μ := by
  obtain ⟨e, he, heω⟩ := hω.1.1
  obtain ⟨γ, sum, _⟩ := ZF.ordinalAddition_existsUnique hZF I δ (hω.isOrdinal (ZF.modelsKP hZF))
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hδ).1.2 _ _ (hω.isOrdinal (ZF.modelsKP hZF)) sum
  have hδγ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal (ZF.modelsKP hZF)) sum).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hγ
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω e U
  obtain ⟨t, all⟩ := li_unbounded_l I hZF (e := e) (D := D) hω hU
  refine ⟨e, γ, U, D, he, heω, sum, hU, pool, fun α hα => ?_⟩
  obtain ⟨ν, hν, hγν, hαν, low⟩ := all α hα
  obtain ⟨ξ, next, _⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal (ZF.modelsKP hZF))
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hν).1.2 _ _ (hω.isOrdinal (ZF.modelsKP hZF)) next
  have hνξ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal (ZF.modelsKP hZF)) next).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  obtain ⟨μ, hμ, _, hξμ, high⟩ := all ξ hξ
  exact ⟨ν, μ, ξ, hαν, hν.transitive γ hγν δ hδγ, next, hξμ,
    hν, hμ, hμ.transitive ξ hξμ ν hνξ, t, low, high⟩

/-- 原定义的逐公式读取：同一完整类型使 (ν,a₀,…,aₖ₋₁) 与 (μ,a₀,…,aₖ₋₁) 真值相同。 -/
theorem Li_pair_d.read_l {ω e U D ν μ : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω) (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) ω e U D)
    (h : Li_pair_d (kp_pair_l (ZF.modelsKP hZF)) ω e U D ν μ) :
    let Q := kp_pair_l (ZF.modelsKP hZF)
    ∃ ξ ζ X Y c R d S t,
      M.IsOrdinalAddition Q ξ ν ω ∧ M.IsOrdinalAddition Q ζ μ ω ∧ V_d Q ξ X ∧ V_d Q ζ Y ∧
      Smem_d Q c X R ∧ Smem_d Q d Y S ∧
      ∃ l : Tt_realized_d Q ω c X R e e ν U D t, ∃ r : Tt_realized_d Q ω d Y S e e μ U D t,
        ∀ k (φ : Formula 1 (k+1)), φ.FreeClosed → ∀ a : Fin k → M.Domain, ∀ ha : ∀ i, M.mem (a i) U,
          Formula.satisfies (l.point_env_l Q a ha) φ ↔ Formula.satisfies (r.point_env_l Q a ha) φ := by
  obtain ⟨_, _, _, t, low, high⟩ := h
  obtain ⟨ξ, X, c, R, sum, hX, model, l⟩ := low.realized_l _ he heω pool
  obtain ⟨ζ, Y, d, S, sum', hY, model', r⟩ := high.realized_l _ he heω pool
  exact ⟨ξ, ζ, X, Y, c, R, d, S, t, sum, sum', hX, hY, model, model', l, r,
    fun _ φ hφ a ha => l.point_congr_l hZF hω r φ hφ a ha⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 局部不可分辨对象的字典序最小选取

按类型游戏的原约定，先最小化第二坐标，再在其纤维内最小化第一坐标。
两个最小化均施于实际原公式；不选择宿主序数，不添加规范选择公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Li_least_d (ω e U D δ ν μ : M.Domain) : Prop :=
  M.mem δ ν ∧ Li_pair_d I ω e U D ν μ ∧ ∀ a b, M.mem δ a → Li_pair_d I ω e U D a b →
    ¬ M.mem b μ ∧ (b = μ → ¬ M.mem a ν)

def li_least_m {d} (ω e U D δ ν μ : Term d) : Formula 1 d := set[d] ⟪
  ⌜δ⌝ₛ ∈ ⌜ν⌝ₛ ∧ ⌜li_pair_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜ν⌝ₛ, ⌜μ⌝ₛ) ∧
  (∀ a b, ⌜δ⌝ₛ ∈ a → ⌜li_pair_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, a, b) →
    (¬ (b ∈ ⌜μ⌝ₛ)) ∧ (b = ⌜μ⌝ₛ → ¬ (a ∈ ⌜ν⌝ₛ)))⟫
derive_free_closed li_least_m

theorem li_least_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e U D δ ν μ : Term d) :
    Formula.satisfies ρ (li_least_m ω e U D δ ν μ) ↔
      Li_least_d I (ω.eval ρ) (e.eval ρ) (U.eval ρ) (D.eval ρ) (δ.eval ρ) (ν.eval ρ) (μ.eval ρ) := by
  simp only [li_least_m, Li_least_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, li_pair_sat_l I hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
include hZF

/-- 任意实际不可分辨序数对给出原定义中的字典序最小对。 -/
theorem li_least_l {ω e U D δ ν μ : M.Domain} (hδν : M.mem δ ν) (h : Li_pair_d I ω e U D ν μ) :
    ∃ a b, Li_least_d I ω e U D δ a b := by
  let φ : BinarySchema 5 := {
    body := .conj (.mem (.bound 6) .newest)
      (li_pair_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 5 := ⟨Fin.cases D (Fin.cases U (Fin.cases e (Fin.cases ω (fun _ => δ)))), fun _ => ω⟩
  have read b a : φ.denote ρ b a ↔ M.mem δ a ∧ Li_pair_d I ω e U D a b := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      li_pair_sat_l I (ZF.modelsKP hZF)]
    rfl
  let ψ : UnarySchema 5 := { body := .existsE φ.body }
  have domain b : ψ.denote ρ b ↔ ∃ a, φ.denote ρ b a := Formula.satisfies_exists_iff ..
  obtain ⟨b, _, hb, first⟩ := ZF.ordinal_min_l hZF ψ ρ h.2.1 ((domain μ).mpr ⟨ν, (read μ ν).mpr ⟨hδν, h⟩⟩)
  obtain ⟨a, hab⟩ := (domain b).mp hb
  let χ : UnarySchema 6 := { body := φ.body }
  obtain ⟨a', _, ha', second⟩ := ZF.ordinal_min_l hZF χ (ρ.push b) ((read b a).mp hab).2.1 hab
  have chosen := (read b a').mp ha'
  refine ⟨a', b, chosen.1, chosen.2, fun x y hx hxy => ⟨?_, ?_⟩⟩
  · exact fun hyb => first y hyb ((domain y).mpr ⟨x, (read y x).mpr ⟨hx, hxy⟩⟩)
  · intro eq hxa
    exact second x hxa ((read b x).mpr ⟨hx, eq ▸ hxy⟩)

/-- 同一固定语言下的最小序数对字面唯一。 -/
theorem Li_least_d.unique_l {ω e U D δ ν μ a b : M.Domain}
    (h : Li_least_d I ω e U D δ ν μ) (k : Li_least_d I ω e U D δ a b) : ν = a ∧ μ = b := by
  have eqμ : μ = b := by
    rcases h.2.1.2.1.trichotomy hZF.1 k.2.1.2.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) μ b) with eq | lt | gt
    · exact hZF.1.eq_of_same_members μ b eq
    · exact ((k.2.2 ν μ h.1 h.2.1).1 lt).elim
    · exact ((h.2.2 a b k.1 k.2.1).1 gt).elim
  subst b
  refine ⟨?_, rfl⟩
  rcases h.2.1.1.trichotomy hZF.1 k.2.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) ν a) with eq | lt | gt
  · exact hZF.1.eq_of_same_members ν a eq
  · exact ((k.2.2 ν μ h.1 h.2.1).2 rfl lt).elim
  · exact ((h.2.2 a μ k.1 k.2.1).2 rfl gt).elim

/-- 给定 δ 后自动构造原参数带、查询域及字典序最小局部不可分辨对。 -/
theorem li_canonical_l {ω δ : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) :
    ∃ e γ U D ν μ, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition I γ δ ω ∧
      V_d I γ U ∧ Tt_pool_d I ω e U D ∧ Li_least_d I ω e U D δ ν μ := by
  obtain ⟨e, γ, U, D, he, heω, sum, hU, pool, pairs⟩ := li_indiscernibles_l I hZF hω hδ
  obtain ⟨ν, μ, _, _, hδν, _, _, pair⟩ := pairs δ hδ
  obtain ⟨a, b, least⟩ := li_least_l I hZF hδν pair
  exact ⟨e, γ, U, D, a, b, he, heω, sum, hU, pool, least⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原局部不可分辨点之间的实际高度间隔

两点的有限后继尾长由共同参数域中的内部自然数命名。
类型相同使尾长相同，故低点的任意有限后继仍严格低于高点。
不修改原最小对的定义，也不向游戏参数另加间隔条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Li_pair_d.finite_gap_l {ω e γ U D ν μ k β : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hU : V_d I γ U) (hwU : M.mem ω U) (pool : Tt_pool_d I ω e U D)
    (pair : Li_pair_d I ω e U D ν μ) (hk : M.mem k ω) (sum : M.IsOrdinalAddition I β ν k) : M.mem β μ := by
  obtain ⟨ξ, ζ, X, Y, c, R, d, S, t, sx, sy, hx, hy, mx, my, low, high, _⟩ := pair.read_l hZF hω he heω pool
  have lx := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I pair.1).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sx
  have ly := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I pair.2.1).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sy
  obtain ⟨n, tail⟩ := ZF.ot_tail_exists_l I hZF hω pair.1
  let a : Fin 2 → M.Domain := Fin.cases ω (fun _ => n)
  have ha : ∀ i, M.mem (a i) U := Fin.cases hwU (fun _ => v_transitive_l I hU ω hwU n tail.1)
  let φ : Formula 1 3 := ot_tail_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 2) (.bound 0)
  have read {η Z b H v} (hη : M.IsLimitOrdinal η) (hZ : V_d I η Z)
      (model : Smem_d I b Z H) (type : Tt_realized_d I ω b Z H e e v U D t) :
      Formula.satisfies (type.point_env_l I a ha) φ ↔ Ot_tail_d I ω n v := by
    let nz : Nonempty {x // M.mem x Z} := ⟨⟨v, type.point⟩⟩
    let ρ : Env (rt_model_l Z nz) 3 := ⟨Fin.cases ⟨v, type.point⟩
      (fun i => ⟨a i, type.constants _ (ha i)⟩), fun _ => ⟨v, type.point⟩⟩
    exact (smem_formula_l I model nz φ ρ).symm.trans
      (ot_tail_source_l hZF hη hZ nz ρ (.bound 1) (.bound 2) (.bound 0))
  have same := low.point_congr_l hZF hω high φ (by simp -implicitDefEqProofs [φ]) a ha
  have tail' := (read ly hy my high).mp (same.mp ((read lx hx mx low).mpr tail))
  exact ZF.ot_tail_gap_l I hZF hω tail tail' pair.2.2.1 hk sum

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 局部不可分辨序数间有限后继秩层的完整类型搬运

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
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hδ.1).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) band
  have hδγ := (ZF.ordinalAddition_mem_iff hZF Q (hω.isOrdinal (ZF.modelsKP hZF)) band).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  have wt := v_transitive_l Q hW
  have hδW := ZF.v_ordinal_mem_l Q hZF hW hδγ
  have hωW := wt δ hδW ω hωδ
  obtain ⟨C, P, hC, hPW, params⟩ := tt_constants_exists_l hZF hW hγ hδγ
  have hCW := ZF.v_mem_l Q hZF hC hW hδγ
  have ct := v_transitive_l Q hC
  have hωC := ZF.v_ordinal_mem_l Q hZF hC hωδ
  obtain ⟨Z, names⟩ := tn_names_exists_l hZF e P
  have hZW := names.rank_mem_l (ZF.modelsKP hZF) hω hW hγ hωW heω hPW
  obtain ⟨G, seq⟩ := ZF.fseq_space_exists_l Q hZF hω Z
  have hGW := ZF.v_fseq_mem_l Q hZF hW hγ hω hωW hZW seq
  refine ⟨C, P, Z, hC, params, names, fun κ k n E hκδ hk hek hn column => ?_⟩
  have hEW := wt G hGW E ((seq E).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) column⟩)
  have ho := hω.members_areOrdinals (ZF.modelsKP hZF) k hk
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
  have hDC := pool.rank_mem_l (ZF.modelsKP hZF) hω hC hδ hωC hn hUC
  obtain ⟨t, truth, _⟩ := tt_truth_exists_l Q hZF ω c n s δ D
  have htW := wt C hCW t (v_subset_mem_l Q hC hDC (fun p hp => ((truth p).mp hp).1))
  have ha : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W :=
    Fin.cases hωW (Fin.cases hCW (Fin.cases (wt δ hδW κ hκδ)
      (Fin.cases (wt ω hωW k hk) (Fin.cases (wt ω hωW n hn) (Fin.cases hZW
        (Fin.cases hEW (Fin.cases hδW (Fin.cases (wt ω hωW e heω) (fun _ => htW)))))))))
  obtain ⟨ξ, ζ, X, Y, a, H, b, K, u, sx, sy, hx, hy, mx, my, l, r, _⟩ := h.read_l hZF hω he heω pool₀
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hν).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sx
  have hζ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sy
  have hβξ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k ω ho (hω.isOrdinal (ZF.modelsKP hZF)) hk β ξ sum sx
  have hβζ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hμ k ω ho (hω.isOrdinal (ZF.modelsKP hZF)) hk β' ζ sum' sy
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

/-! ## 已有完整类型的自动元组搬运接口

调用者给出实际秩层、元组和原 κ 型。整个共同参数带中的对象保持原值，
只替换出现的高度对象。参数带与指定常量 δ 独立，允许另行覆盖树的秩。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意内部有限元组均自动命名；原常量域、全部查询及完整类型集合字面不变。 -/
theorem Li_pair_d.transport_l {ω e γ W F δ ν μ κ k n β C A c R s B U D t : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) (hγ : M.IsLimitOrdinal γ)
    (hW : V_d Q γ W) (hδW : M.mem δ W) (pool₀ : Tt_pool_d Q ω e W F)
    (h : Li_pair_d Q ω e W F ν μ) (hκδ : M.mem κ δ) (hk : M.mem k ω) (hek : M.mem e k)
    (sum : M.IsOrdinalAddition Q β ν k) (hA : V_d Q β A) (model : Smem_d Q c A R)
    (hC : V_d Q δ C) (hB : V_d Q κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (type : Tt_realized_d Q ω c A R n s δ U D t)
    (values : ∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x W) :
    ∃ β' A' c' R' s', M.IsOrdinalAddition Q β' μ k ∧ V_d Q β' A' ∧ Smem_d Q c' A' R' ∧
      Tm_move_d ν μ s s' ∧ Tt_realized_d Q ω c' A' R' n s' δ U D t := by
  have hν := h.1
  have hμ := h.2.1
  have ho := hω.members_areOrdinals (ZF.modelsKP hZF) k hk
  have wt := v_transitive_l Q hW
  have hωW := wt δ hδW ω hωδ
  have hCW := ZF.v_mem_l Q hZF hC hW (ZF.v_ordinal_height_l hZF hW hδ.1 hδW)
  obtain ⟨β', sum', _⟩ := ZF.ordinalAddition_existsUnique hZF Q μ ho
  have hb' := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).1.2 _ _ ho sum'
  obtain ⟨A', ha'⟩ := ZF.v_exists_l Q hZF hb'
  -- ν≤μ 推出 ν+k≤μ+k；这里只用加法余项、结合律和右参数单调性。
  have sub : M.MemberSubset A A' := by
    obtain ⟨j, add, _⟩ := ZF.ordinalAddition_existsUnique_rightRemainder hZF Q hν hμ h.2.2.1
    obtain ⟨l, plus, _⟩ := ZF.ordinalAddition_existsUnique hZF Q j ho
    have hj := add.right_isOrdinal
    have hl := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hj).1.2 _ _ ho plus
    obtain ⟨b, comb, _⟩ := ZF.ordinalAddition_existsUnique hZF Q ν hl
    have eq := ZF.ordinalAddition_assoc hZF Q hν hj ho add plus comb sum'
    have le : M.MemberSubset β β' := by
      rcases ZF.ordinalAddition_right_eq_or_mem hZF Q hj ho plus with eqk | lt
      · subst l
        obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF Q ν ho
        exact (unique β sum).trans ((unique b comb).symm.trans eq) ▸ (fun _ hx => hx)
      · exact hb'.transitive β (eq ▸ ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k l ho hl lt β b sum comb)
    exact ZF.v_mono_l Q hZF hA ha' le
  obtain ⟨N, names⟩ := tn_names_exists_l hZF e A
  obtain ⟨E, column, assign, quote, move⟩ := tm_quote_l hZF he names type.tuple
    (fun i x hx => Or.inr ((fn0_function_l (ZF.modelsKP hZF) type.tuple).output_mem_of_pairMember hx))
  -- 名字列的值全在共同参数带中；内部有限闭包给出列本身及一个源内名字界。
  have name_mem i a (ha : Rd_entry_d i a E) : M.mem a W := by
    obtain ⟨x, hx, ⟨_, eq⟩ | ⟨hne, code⟩⟩ := (quote i a).mp ha
    · exact eq.symm ▸ wt ω hωW e heω
    · have hxW := (values i x hx).resolve_left hne
      obtain ⟨P, hp, pair⟩ := sc_v_pair_l (ZF.modelsKP hZF) hγ hW x x hxW hxW
      obtain ⟨Z, nz⟩ := tn_names_exists_l hZF e P
      exact wt Z (nz.rank_mem_l (ZF.modelsKP hZF) hω hW hγ hωW heω hp) a
        ((nz a).mpr (Or.inr (Or.inr ⟨x, (pair x).mpr (Or.inl rfl), code⟩)))
  have ew := fn0_function_l (ZF.modelsKP hZF) (column.retarget_l name_mem)
  obtain ⟨Z, hZW, ez, hEW⟩ := ZF.v_finite_function_l hZF hω hγ hW hωW type.finite ew
  have empty : Fn0_d e A' e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  have hμβ' := (ZF.ordinalAddition_mem_iff hZF Q ho sum').mpr
    (Or.inr ⟨e, hek, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  obtain ⟨s', assign', tuple'⟩ := tn_assign_exists_l hZF (Structure.IsOrdinal.of_no_members he) empty
    (ZF.v_ordinal_mem_l Q hZF ha' hμβ') sub names column
  have point' := sub δ type.point
  obtain ⟨c', R', model'⟩ := smdl_membership_l Q hZF ⟨δ, point'⟩
  have hUC := tt_constants_rank_l hZF hC hδ hκδ hB constants
  have hDC := type.pool.rank_mem_l (ZF.modelsKP hZF) hω hC hδ (ZF.v_ordinal_mem_l Q hZF hC hωδ) type.finite hUC
  have htW := wt C hCW t (v_subset_mem_l Q hC hDC (fun p hp => ((type.truth p).mp hp).1))
  have params : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W :=
    Fin.cases hωW (Fin.cases hCW (Fin.cases (wt δ hδW κ hκδ)
      (Fin.cases (wt ω hωW k hk) (Fin.cases (wt ω hωW n type.finite) (Fin.cases hZW
        (Fin.cases hEW (Fin.cases hδW (Fin.cases (wt ω hωW e heω) (fun _ => htW)))))))))
  obtain ⟨ξ, ζ, X, Y, a, H, b, K, u, sx, sy, hx, hy, mx, my, l, r, _⟩ := h.read_l hZF hω he heω pool₀
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hν).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sx
  have hζ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sy
  have hβξ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k ω ho (hω.isOrdinal (ZF.modelsKP hZF)) hk β ξ sum sx
  have hβζ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hμ k ω ho (hω.isOrdinal (ZF.modelsKP hZF)) hk β' ζ sum' sy
  have wb : M.MemberSubset ω β := fun i hi => (v_ordinal_l Q hA).transitive δ
    (ZF.v_ordinal_height_l hZF hA hδ.1 type.point) i (hδ.1.transitive ω hωδ i hi)
  have wb' : M.MemberSubset ω β' := fun i hi => hb'.transitive δ
    (ZF.v_ordinal_height_l hZF ha' hδ.1 point') i (hδ.1.transitive ω hωδ i hi)
  have low := l.move_read_l hZF mx hω hξ hx hν hk sum hβξ hA wb
    (v_transitive_l Q hA δ type.point κ hκδ) hC hδ hωδ hκδ hB constants type.pool model type.finite
    (fn0_of_function_l (ZF.modelsKP hZF) ez) assign type.tuple type.point params
  have high := r.move_read_l hZF my hω hζ hy hμ hk sum' hβζ ha' wb'
    (v_transitive_l Q ha' δ point' κ hκδ) hC hδ hωδ hκδ hB constants type.pool model' type.finite
    (fn0_of_function_l (ZF.modelsKP hZF) ez) assign' tuple' point' params
  have same := l.point_congr_l hZF hω r tm_type_f tm_type_closed_l (tm_params_l ω C κ k n Z E δ e t) params
  exact ⟨β', A', c', R', s', sum', ha', model', move μ s' assign',
    ⟨model'.1, type.finite, tuple', point', fun x hx => sub x (type.constants x hx), type.pool,
      high.mp (same.mp (low.mpr type.truth))⟩⟩

/-- 最小局部不可分辨对自动具备全部内部有限后继层的类型搬运实例。 -/
theorem li_canonical_finite_l {ω δ : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) :
    ∃ e γ W F ν μ C P Z, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition Q γ δ ω ∧
      V_d Q γ W ∧ Tt_pool_d Q ω e W F ∧ Li_least_d Q ω e W F δ ν μ ∧ V_d Q δ C ∧
      (∀ x, M.mem x P ↔ M.mem x C ∨ x = δ) ∧ Tn_names_d e P Z ∧
      ∀ κ k n E, M.mem κ δ → M.mem k ω → M.mem e k → M.mem n ω → Fn0_d n Z E →
        ∃ B U D t, V_d Q κ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧ Tt_pool_d Q ω n U D ∧
          Li_finite_d Q ω e δ ν k n E U D t ∧ Li_finite_d Q ω e δ μ k n E U D t := by
  obtain ⟨e, γ, W, F, ν, μ, he, heω, band, hw, pool, least⟩ := li_canonical_l Q hZF hω hδ.1
  obtain ⟨C, P, Z, hc, params, names, all⟩ :=
    least.2.1.finite_types_l hZF hω he heω hδ hωδ band hw pool least.1
  exact ⟨e, γ, W, F, ν, μ, C, P, Z, he, heω, band, hw, pool, least, hc, params, names, all⟩

/-- 参数带可取任意 θ≥δ；自动选出最小对后，直接搬运已有元组和原完整类型。 -/
theorem li_canonical_transport_l {ω δ θ : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) (hθ : M.IsOrdinal θ) (hδθ : δ = θ ∨ M.mem δ θ) :
    ∃ e γ W F ν μ C, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition Q γ θ ω ∧
      V_d Q γ W ∧ Tt_pool_d Q ω e W F ∧ Li_least_d Q ω e W F θ ν μ ∧ V_d Q δ C ∧
      ∀ κ k n β A c R s B U D t, M.mem κ δ → M.mem k ω → M.mem e k →
        M.IsOrdinalAddition Q β ν k → V_d Q β A → Smem_d Q c A R → V_d Q κ B →
        (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) → Tt_realized_d Q ω c A R n s δ U D t →
        (∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x W) →
        ∃ β' A' c' R' s', M.IsOrdinalAddition Q β' μ k ∧ V_d Q β' A' ∧ Smem_d Q c' A' R' ∧
          Tm_move_d ν μ s s' ∧ Tt_realized_d Q ω c' A' R' n s' δ U D t := by
  obtain ⟨e, γ, W, F, ν, μ, he, heω, band, hw, pool, least⟩ := li_canonical_l Q hZF hω hθ
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hθ).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) band
  have hθγ := (ZF.ordinalAddition_mem_iff hZF Q (hω.isOrdinal (ZF.modelsKP hZF)) band).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  have hδγ := hδθ.elim (fun eq => eq.symm ▸ hθγ) (hγ.1.transitive θ hθγ δ)
  obtain ⟨C, hc⟩ := ZF.v_exists_l Q hZF hδ.1
  refine ⟨e, γ, W, F, ν, μ, C, he, heω, band, hw, pool, least, hc,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hκδ hk hek sum ha model hb constants type values => ?_⟩
  exact least.2.1.transport_l hZF hω he heω hδ hωδ hγ hw (ZF.v_ordinal_mem_l Q hZF hw hδγ)
    pool hκδ hk hek sum ha model hc hb constants type values

end YesMetaZFC.SetTheory.LargeCardinal
