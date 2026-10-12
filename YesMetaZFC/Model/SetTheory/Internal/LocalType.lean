import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

/-! # V(ν+ω) 中指定序数的完整类型

查询域固定，指定常量解释为 ν；零个自由变量的全部查询仍允许任意内部
有限参数列。类型值由同一条原公式定义，以便在 ZF 内收集其高度界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Li_type_d (ω e U D ν t : M.Domain) : Prop := ∃ η X c R,
  M.IsOrdinalAddition I η ν ω ∧ V_d I η X ∧ Smem_d I c X R ∧ M.mem ν X ∧ M.MemberSubset U X ∧
    Tt_truth_d I ω c e e ν D t

def li_type_m {d} (ω e U D ν t : Term d) : Formula 1 d := set[d] ⟪∃ η X c R,
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(η, ⌜ν⌝ₛ, ⌜ω⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(η, X) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) ∧
  ⌜ν⌝ₛ ∈ X ∧ ⌜U⌝ₛ ⊆ X ∧ (∀ p, p ∈ ⌜t⌝ₛ ↔
    (p ∈ ⌜D⌝ₛ ∧ ⌜tt_query_m⌝ₚ(⌜ω⌝ₛ, c, ⌜e⌝ₛ, ⌜e⌝ₛ, ⌜ν⌝ₛ, p)))⟫
derive_free_closed li_type_m

theorem li_type_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e U D ν t : Term d) :
    Formula.satisfies ρ (li_type_m ω e U D ν t) ↔
      Li_type_d I (ω.eval ρ) (e.eval ρ) (U.eval ρ) (D.eval ρ) (ν.eval ρ) (t.eval ρ) := by
  simp only [li_type_m, Li_type_d, Tt_truth_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOrdinalAddition_iff I hKP.1,
    v_sat_l I hKP.1, smem_sat_l I, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, tt_query_sat_l I hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable (hZF : M.Models ZF)

include hZF in
/-- 任意超过参数秩的序数都有实际类型；没有使用外部真值或外部序数递归。 -/
theorem li_type_exists_l {ω e γ U D ν : M.Domain} (hω : M.IsOmega ω)
    (hU : V_d I γ U) (hν : M.IsOrdinal ν) (hγν : M.mem γ ν) :
    ∃ t, Li_type_d I ω e U D ν t := by
  obtain ⟨η, sum, _⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal hZF)
  have hη := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I hν).1.2 _ _ (hω.isOrdinal hZF) sum
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  have hνη := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal hZF) sum).mpr
    (Or.inr ⟨z, hzω, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩)
  obtain ⟨X, hX⟩ := ZF.v_exists_l I hZF hη
  have point := ZF.v_ordinal_mem_l I hZF hX hνη
  obtain ⟨c, R, model⟩ := smdl_membership_l I hZF ⟨ν, point⟩
  obtain ⟨t, truth, _⟩ := tt_truth_exists_l I hZF ω c e e ν D
  exact ⟨t, η, X, c, R, sum, hX, model, point,
    ZF.v_mono_l I hZF hU hX (hη.transitive γ (hη.transitive ν hνη γ hγν)), truth⟩

include hZF in
/-- 每个固定高度的完整类型唯一，包含全部内部公式码。 -/
theorem Li_type_d.unique_l {ω e U D ν t u : M.Domain} (hω : M.IsOmega ω)
    (h : Li_type_d I ω e U D ν t) (k : Li_type_d I ω e U D ν u) : t = u := by
  obtain ⟨η, X, c, R, sum, hX, model, _, _, truth⟩ := h
  obtain ⟨θ, Y, d, S, sum', hY, model', _, _, truth'⟩ := k
  obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I ν (hω.isOrdinal hZF)
  have eqη := (unique η sum).trans (unique θ sum').symm
  subst θ
  have eqX := ZF.v_unique_l I hZF hX hY
  subst Y
  obtain ⟨eqc, eqR⟩ := smem_unique_l I hZF.1 model' model
  subst d S
  exact hZF.1.eq_of_same_members t u (fun p => (truth p).trans (truth' p).symm)

/-- 零变量与空元组的真实实现；参数域和指定序数来自原类型公式的守卫。 -/
theorem Li_type_d.realized_l {ω e U D ν t : M.Domain} (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (pool : Tt_pool_d I ω e U D) (h : Li_type_d I ω e U D ν t) :
    ∃ η X c R, M.IsOrdinalAddition I η ν ω ∧ V_d I η X ∧ Smem_d I c X R ∧
      Tt_realized_d I ω c X R e e ν U D t := by
  obtain ⟨η, X, c, R, sum, hX, model, point, constants, truth⟩ := h
  have tuple : Fn0_d e X e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  exact ⟨η, X, c, R, sum, hX, model, model.1, heω, tuple, point, constants, pool, truth⟩

end YesMetaZFC.SetTheory.Internal
