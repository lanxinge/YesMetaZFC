import YesMetaZFC.Model.Forcing.Proper.Preservation.CoverValue
import YesMetaZFC.Model.Forcing.Internal.Ground.Cofinality
import YesMetaZFC.SetTheory.Card.SmallBound

/-! # proper 泛型扩张的可数共尾性保持

新可数共尾集的旧可数覆盖仍共尾，ZF 的严格共尾列构造因此反射精确共尾度 ω。
若旧共尾度大于 ω，则旧覆盖已有严格旧界，扩张中的新可数子集也被同一旧界控制。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

/-- 对每个旧集合，共尾度等于 ω 在 proper 扩张前后精确等价。 -/
theorem proper_cf_omega_l {ω b α} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) :
    (E).IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α := by
  have hE := preserves_zf_l O hZF hU
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  have mem {a b} := image_member_l e hi he (a := a) (b := b)
  rw [ZF.cf_omega_countable_l J hE hw, ZF.cf_omega_countable_l I hZF hω]
  constructor
  · rintro ⟨Y, hY, hc⟩
    obtain ⟨A, hAα, hAc, hYA⟩ := proper_set_cover_l O hZFC hU hω hPr hb e hv hY.2.1 hc
    have hα := image_ordinal_reflect_l e hi he hE.1 hY.1.1
    have hl : M.IsLimitOrdinal α := by
      refine ⟨hα, ?_, ?_⟩
      · obtain ⟨y, hy⟩ := hY.1.2.1
        obtain ⟨x, hx, _⟩ := (he α y).mp hy
        exact ⟨x, hx⟩
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := hY.1.2.2 (e x) (mem.mpr hx)
        obtain ⟨z, hz, rfl⟩ := (he α y).mp hy
        exact ⟨z, hz, mem.mp hxy⟩
    refine ⟨A, ⟨hl, hAα, fun x => ⟨?_, ?_⟩⟩, hAc⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (hY.2.2 (e x)).mp (mem.mpr hx)
      obtain ⟨a, ha, rfl⟩ := (he A y).mp (hYA y hy)
      exact ⟨a, ha, mem.mp hxy⟩
    · rintro ⟨a, ha, hxa⟩
      exact hα.transitive a (hAα a ha) x hxa
  · rintro ⟨A, hA, F, hF⟩
    exact ⟨e A, image_cofinal_subset_l e hi he hZF.1 (internal_foundation_l O hZF hU) hA, e F,
      image_injection_l (hEN := hE.1) (hPN := internal_pair_l O hZF hU) e hi he hF⟩

/-- 旧共尾度大于 ω 时，每个新可数子集都有严格的旧序数界；无需目标序数正则。 -/
theorem proper_countable_bounded_l {ω b α cf} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (e : M.Domain → (E).Domain) (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (hcf : M.IsCofinality I cf α) (hωcf : M.mem ω cf) {Y : (E).Domain}
    (hY : (E).MemberSubset Y (e α)) (hc : (E).CardinalLessOrEqual J Y (e ω)) :
    ∃ β, M.mem β α ∧ (E).MemberSubset Y (e β) := by
  obtain ⟨A, hAα, hAc, hYA⟩ := proper_set_cover_l O hZFC hU hω hPr hb e hv hY hc
  obtain ⟨β, hβ, hAb⟩ := (ZF.small_subset_bounded_l I hZF hcf hAα hωcf hAc).exists_bound
  obtain ⟨F, hF⟩ := hcf.hasCofinalSequence
  obtain ⟨γ, hγ, hβγ⟩ := hF.isLimitOrdinal.2.2 β hβ
  refine ⟨γ, hγ, fun y hy => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (he A y).mp (hYA y hy)
  exact (he γ (e a)).mpr ⟨a, (hAb a ha).elim (fun h => h.symm ▸ hβγ)
    (fun h => (hF.isLimitOrdinal.1.mem hγ).transitive β hβγ a h), rfl⟩

end YesMetaZFC.Model.Forcing.Internal
