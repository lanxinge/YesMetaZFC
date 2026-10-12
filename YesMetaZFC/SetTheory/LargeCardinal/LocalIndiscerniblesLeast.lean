import YesMetaZFC.SetTheory.LargeCardinal.LocalIndiscernibles
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # 局部不可分辨对象的字典序最小选取

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
