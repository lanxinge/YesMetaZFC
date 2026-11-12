import YesMetaZFC.Model.Forcing.Boolean.NameHomData
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 名字诱导图的有限参数反射公式 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def nh_m {n} (B R z b p Q T w 𝒟 τ K S e C L V d F : Term n) : Formula 1 n := set[n] ⟪
  ⌜cond_order_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ) ∧ ⌜cond_order_m⌝ₚ(⌜Q⌝ₛ,⌜T⌝ₛ,⌜w⌝ₛ) ∧
  ⌜b⌝ₛ ∈ ⌜B⌝ₛ ∧ ⌜p⌝ₛ ∈ ⌜B⌝ₛ ∧ ⌜p⌝ₛ ≠ ⌜z⌝ₛ ∧ ⌜entry_m⌝ₚ(⌜p⌝ₛ,⌜b⌝ₛ,⌜R⌝ₛ) ∧
  ⌜Formula.isPowerSet⌝ₚ(⌜𝒟⌝ₛ,⌜Q⌝ₛ) ∧ ⌜gn_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜Q⌝ₛ,⌜T⌝ₛ,⌜w⌝ₛ,⌜𝒟⌝ₛ,⌜τ⌝ₛ,⌜p⌝ₛ) ∧
  (∀ U, U ∈ ⌜K⌝ₛ ↔ ⌜ropen_m⌝ₚ(⌜Q⌝ₛ,⌜T⌝ₛ,⌜w⌝ₛ,U)) ∧ (∀ q, ¬ q ∈ ⌜e⌝ₛ) ∧
  (∀ U, ∀ W, ⌜entry_m⌝ₚ(U,W,⌜S⌝ₛ) ↔ (U ∈ ⌜K⌝ₛ ∧ W ∈ ⌜K⌝ₛ ∧ U ⊆ W)) ∧
  ⌜(BooleanZF.cba_m kpair_convention_l)⌝ₚ(⌜K⌝ₛ,⌜S⌝ₛ,⌜e⌝ₛ) ∧
  ⌜ropen_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜C⌝ₛ) ∧ ⌜p⌝ₛ ∈ ⌜C⌝ₛ ∧
  (∀ U, ⌜ropen_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,U) → ⌜p⌝ₛ ∈ U → ⌜C⌝ₛ ⊆ U) ∧
  (∀ X, X ∈ ⌜L⌝ₛ ↔ (⌜ropen_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,X) ∧ X ⊆ ⌜C⌝ₛ)) ∧ (∀ q, ¬ q ∈ ⌜d⌝ₛ) ∧
  (∀ X ∈ ⌜L⌝ₛ, ∀ Y ∈ ⌜L⌝ₛ, ⌜entry_m⌝ₚ(X,Y,⌜V⌝ₛ) ↔ X ⊆ Y) ∧
  ⌜(BooleanZF.cba_m kpair_convention_l)⌝ₚ(⌜L⌝ₛ,⌜V⌝ₛ,⌜d⌝ₛ) ∧
  ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜F⌝ₛ,⌜K⌝ₛ,⌜L⌝ₛ) ∧
  (∀ U, ∀ X, ⌜entry_m⌝ₚ(U,X,⌜F⌝ₛ) → ∃ W,
    ⌜bv_hit_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜τ⌝ₛ,U,W) ∧ (∀ q, q ∈ X ↔ (q ∈ W ∧ q ∈ ⌜C⌝ₛ)))⟫
derive_free_closed nh_m

theorem nh_sat_l {n} (ρ : Env M n) (B R z b p Q T w 𝒟 τ K S e C L V d F : Term n) :
    Formula.satisfies ρ (nh_m B R z b p Q T w 𝒟 τ K S e C L V d F) ↔
      Nh_d hZF (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (p.eval ρ) (Q.eval ρ) (T.eval ρ) (w.eval ρ)
        (𝒟.eval ρ) (τ.eval ρ) (K.eval ρ) (S.eval ρ) (e.eval ρ) (C.eval ρ) (L.eval ρ) (V.eval ρ) (d.eval ρ) (F.eval ρ) := by
  simp only [nh_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.extensionalNe,
    Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,cond_order_sat_l hZF.1,
    Formula.satisfies_isPowerSet_iff,gn_sat_l hZF.1,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_subset_iff,entry_sat_l M hZF.1,ropen_sat_l hZF,BooleanZF.cba_sat_l I hZF.1,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1,bv_hit_sat_l hZF,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨big,small,base,hp,hz,pb,power,name,family,empty,order,source,cone,point,minimal,
      localFamily,localEmpty,localOrder,target,fn,graph⟩
    exact ⟨big,small,base,⟨hp,hz⟩,pb,power,name,family,empty,order,source,cone,point,minimal,
      localFamily,localEmpty,(fun X Y hx hy => localOrder X hx Y hy),target,fn,graph⟩
  · intro h
    exact ⟨h.big,h.small,h.base,h.positive.1,h.positive.2,h.below,h.power,h.name,h.family,h.empty,h.order,
      h.source,h.cone,h.point,h.minimal,h.localFamily,h.localEmpty,
      (fun X hx Y hy => h.localOrder X Y hx hy),h.target,h.function,h.graph⟩

end YesMetaZFC.Model.Forcing.Internal
