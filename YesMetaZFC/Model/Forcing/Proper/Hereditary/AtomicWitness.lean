import YesMetaZFC.Model.Forcing.Proper.Hereditary.NameBound
import YesMetaZFC.Model.Forcing.Internal.Atomic.Equivalence

/-! # H(χ) 中的名称支撑与等号力迫证书

把已有闭支撑限制到端点的传递闭包，得到遗传小支撑。其上的双模拟图是三个
遗传小集合之积的子集，因此等号力迫的证书也确实属于 H(χ)。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H : M.Domain} (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ) (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
include hω hχ hωχ hH

/-- 遗传小名称可取共同的遗传小闭支撑。 -/
theorem h_support_l {B s t} (hs : Name_d M B s) (ht : Name_d M B t) (hsH : M.mem s H) (htH : M.mem t H) :
    ∃ S, M.mem s S ∧ M.mem t S ∧ Supp_d M B S ∧ M.mem S H := by
  obtain ⟨A, hsA, htA, hA⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF)) (KP.exists_union (ZF.modelsKP hZF)) hs ht
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) s t
  obtain ⟨T, μ, hT, hμ, hTc⟩ := (hH P).mp (h_pair_l hZFC hω hχ hωχ hH hP hsH htH)
  have hTH := (hH T).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal hT.1 (fun _ h => h) hμ hTc)
  obtain ⟨S, hS⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) A T
  refine ⟨S, (hS s).mpr ⟨hsA, hT.1 P hT.2.1 s ((hP s).mpr (Or.inl rfl))⟩,
    (hS t).mpr ⟨htA, hT.1 P hT.2.1 t ((hP t).mpr (Or.inr rfl))⟩, ?_,
    ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hTH S (fun a ha => ((hS a).mp ha).2)⟩
  intro u hu p hp
  obtain ⟨huA, huT⟩ := (hS u).mp hu
  obtain ⟨a, b, hpa, haA, hb⟩ := hA u huA p hp
  obtain ⟨v, hvp, hav⟩ := (kpair_union_l M hpa a).mpr (Or.inl rfl)
  exact ⟨a, b, hpa, (hS a).mpr ⟨haA, hT.1 v (hT.1 p (hT.1 u huT p hp) v hvp) a hav⟩, hb⟩

/-- 有界三元关系只占据 B×(S×S)；这是其遗传小性的精确集合界。 -/
theorem h_triple_relation_l {B S F} (hB : M.mem B H) (hS : M.mem S H)
    (hF : ∀ v, M.mem v F → ∃ p s t, M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Triple_d M v p s t) : M.mem F H := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I S S
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I B P
  apply ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH
    (h_product_l hZFC hω hχ hωχ hH hB (h_product_l hZFC hω hχ hωχ hH hS hS hP) hQ) F
  intro v hv
  obtain ⟨p, s, t, hp, hs, ht, a, ha, hv⟩ := hF v hv
  exact (hQ v).mpr ⟨p, hp, a, (hP a).mpr ⟨s, hs, t, ht, ha⟩, hv⟩

/-- 等号力迫的双模拟证书可取在 H(χ) 中。 -/
theorem h_eq_witness_l {B R z p s t} (hB : M.mem B H) (hs : Name_d M B s) (ht : Name_d M B t)
    (hsH : M.mem s H) (htH : M.mem t H) (h : Eq_force_d M B R z p s t) :
    ∃ F, M.mem F H ∧ Bisim_d M B R z F ∧ Rel_d M F p s t := by
  obtain ⟨S, hsS, htS, hS, hSH⟩ := h_support_l hZFC hω hχ hωχ hH hs ht hsH htH
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : BinarySchema 4 := { body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨F, hBound, hF⟩ := rel_separation_bound_l hZF φ ρ B S
  have hf p s t : Rel_d M F p s t ↔ M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Eq_force_d M B R z p s t := by
    simpa only [BinarySchema.denote, φ, eq_force_sat_l M hZF.1] using! hF p s t
  refine ⟨F, h_triple_relation_l hZFC hω hχ hωχ hH hB hSH hBound, ?_,
    (hf p s t).mpr ⟨h.1, hsS, htS, h⟩⟩
  intro q a b hab
  obtain ⟨_, ha, hb, hab⟩ := (hf q a b).mp hab
  obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF ⟨S, ha, hS⟩ ⟨S, hb, hS⟩).mp hab
  constructor
  · intro v d hv r hq hrd
    obtain ⟨u, w, e, hur, hw, hue, hvw⟩ := hl v d hv r hq hrd
    exact ⟨u, w, e, hur, hw, hue, (hf u v w).mpr
      ⟨hur.1, (supp_entry_l M hS ha hv).1, (supp_entry_l M hS hb hw).1, hvw⟩⟩
  · intro v d hv r hq hrd
    obtain ⟨u, w, e, hur, hw, hue, hwv⟩ := hr v d hv r hq hrd
    exact ⟨u, w, e, hur, hw, hue, (hf u w v).mpr
      ⟨hur.1, (supp_entry_l M hS ha hw).1, (supp_entry_l M hS hb hv).1, hwv⟩⟩

end YesMetaZFC.Model.Forcing.Internal
