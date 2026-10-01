import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Internal.ElementarySyntax
import YesMetaZFC.SetTheory.Hereditary
import YesMetaZFC.SetTheory.Card.Properties.Basic

/-! # 内部可数初等 H(χ) 子模型的原公式

载体、真值码与初等性均使用已实现的内部模型编码。这个有界环境的性质可
作为一条原公式用于力迫和内部递归，不以元层的泛型量化替代对象理论证书。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Hsub_d (ω χ X N : M.Domain) : Prop := M.IsOmega ω ∧ M.IsRegularCardinal I χ ∧ M.mem ω χ ∧
  H_d I χ X ∧ M.CardinalLessOrEqual I N ω ∧
    ∃ c R d S, Smem_d I c X R ∧ Ssub_d I c d X R N S ∧ Selem_d I ω c d

def hsub_m {n} (ω χ X N : Term n) : Formula 1 n :=
  .conj (Formula.isOmega ω) (.conj (Formula.isRegularCardinal 𝒞 χ) (.conj (.mem ω χ)
    (.conj (h_m (𝒞 := 𝒞) χ X) (.conj (Formula.cardinalLessOrEqual 𝒞 N ω)
      (.existsE (.existsE (.existsE (.existsE
        (.conj (smem_m (𝒞 := 𝒞) (.bound 3) X.weaken.weaken.weaken.weaken (.bound 2))
        (.conj (ssub_m (𝒞 := 𝒞) (.bound 3) (.bound 1) X.weaken.weaken.weaken.weaken (.bound 2)
          N.weaken.weaken.weaken.weaken .newest)
          (selem_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))))))))))))
derive_free_closed hsub_m

theorem hsub_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω χ X N : Term n) :
    Formula.satisfies ρ (hsub_m (𝒞 := 𝒞) ω χ X N) ↔ Hsub_d I (ω.eval ρ) (χ.eval ρ) (X.eval ρ) (N.eval ρ) := by
  simp only [hsub_m, Hsub_d, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isRegularCardinal_iff I hE, Formula.satisfies_mem_iff, h_sat_l I hE,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Formula.satisfies_exists_iff,
    smem_sat_l I, ssub_sat_l I, selem_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
