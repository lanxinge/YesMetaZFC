import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 可定义纤维的集合函数

对参数化二元公式逐参数分离，再以替换构造到幂集的内部函数图。
此接口统一服务于小纤维覆盖与泛型二元函数的实数截面。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def fiber_m {n m} (φ : BinarySchema n) (e : Definitional.TermVector n m) (X i D : Term m) : Formula 1 m :=
  .forallE (.iff (.mem .newest D.weaken) (.conj (.mem .newest X.weaken)
    (Formula.related φ e.weaken i.weaken .newest)))
derive_free_closed fiber_m

theorem fiber_sat_l {n m} (φ : BinarySchema n) (e : Definitional.TermVector n m) (ρ : Env M m) (X i D : Term m) :
    Formula.satisfies ρ (fiber_m φ e X i D) ↔
      ∀ x, M.mem x (D.eval ρ) ↔ M.mem x (X.eval ρ) ∧ φ.denote (e.evalEnv ρ) (i.eval ρ) x := by
  simp only [fiber_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_related_iff,
    Definitional.TermVector.evalEnv_weaken, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

namespace ZF

/-- 每个参数的精确纤维自动组成一个模型内的集合函数。 -/
theorem fiber_function_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n) (A X : M.Domain) :
    ∃ P, M.IsPowerSetOf P X ∧ ∃ f, M.IsSetFunctionFromTo I f A P ∧
      ∀ i D, M.PairMember I i D f ↔ M.mem i A ∧
        ∀ x, M.mem x D ↔ M.mem x X ∧ φ.denote ρ i x := by
  let ψ : BinarySchema (n + 1) := {
    body := fiber_m φ (Definitional.TermVector.boundParameters n 3) (.bound 2) (.bound 1) .newest }
  have hψ i D : ψ.denote (ρ.push X) i D ↔
      ∀ x, M.mem x D ↔ M.mem x X ∧ φ.denote ρ i x := by
    simp only [BinarySchema.denote, ψ, fiber_sat_l, Definitional.TermVector.evalEnv_boundParameters_three]
    rfl
  obtain ⟨P, hP⟩ := exists_powerSet hZF X
  obtain ⟨f, hf, he⟩ := exists_setFunctionFromTo_of_denote hZF I ψ (ρ.push X)
    (source := A) (target := P) (by
      intro i _
      obtain ⟨D, hD⟩ := separation_exists_d hZF (⟨φ.body, φ.freeClosed⟩ : UnarySchema (n+1)) (ρ.push i) X
      exact ⟨D, (hψ i D).mpr hD⟩) (by
      intro i _ D E hD hE
      exact hZF.1.eq_of_same_members D E (fun x => ((hψ i D).mp hD x).trans ((hψ i E).mp hE x).symm)) (by
      intro i D _ hD
      exact (hP D).mpr (fun x hx => ((hψ i D).mp hD x).mp hx |>.1))
  exact ⟨P, hP, f, hf, fun i D => (he i D).trans (and_congr_right fun _ => hψ i D)⟩

end ZF
end YesMetaZFC.SetTheory
