import YesMetaZFC.Model.SetTheory.Internal.LocalTypeRead
import YesMetaZFC.SetTheory.Ord.UnboundedFiber

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
  obtain ⟨γ, sum, _⟩ := ZF.ordinalAddition_existsUnique hZF I δ (hω.isOrdinal hZF)
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hδ).1.2 _ _ (hω.isOrdinal hZF) sum
  have hδγ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal hZF) sum).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hγ
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω e U
  obtain ⟨t, all⟩ := li_unbounded_l I hZF (e := e) (D := D) hω hU
  refine ⟨e, γ, U, D, he, heω, sum, hU, pool, fun α hα => ?_⟩
  obtain ⟨ν, hν, hγν, hαν, low⟩ := all α hα
  obtain ⟨ξ, next, _⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal hZF)
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hν).1.2 _ _ (hω.isOrdinal hZF) next
  have hνξ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal hZF) next).mpr
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
