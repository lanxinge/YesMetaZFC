import YesMetaZFC.Model.SetTheory.Internal.FormulaCode

/-! # 内部程序行上的原公式强归纳

归纳性质必须给出实际一元 schema。反例集由原分离取得，再使用模型内序数归纳；
不要求程序在外部良基，也不允许把任意宿主谓词当作可分离性质。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_induction_l (hZF : M.Models ZF) {ω n F} (hF : Sfm_d I ω n F)
    {d} (φ : UnarySchema d) (ρ : Env M d)
    (hp : ∀ r, M.mem r n → (∀ i, M.mem i r → φ.denote ρ i) → φ.denote ρ r)
    {r} (hr : M.mem r n) : φ.denote ρ r := by
  apply (hF.2.1.1.mem hr).inductionWithin (fun i => φ.denote ρ i)
  · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ.neg ρ r
    exact ⟨D, fun i => by simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hD i⟩
  · intro i _ hi ih
    apply hp i ?_ ih
    rcases hi with rfl | hi
    · exact hr
    · exact hF.2.1.1.transitive r hr i hi

end YesMetaZFC.SetTheory.Internal
