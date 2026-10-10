import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 编码理论的内部模型性

理论是公式码的内部集合；开放公式按全部内部赋值解释，即取其全称闭包。
统一模型性也是实际原公式。给定结构的全部有效公式由分离构造为模型内理论，
从而模型性接口具有实际实例，不要求地模型证明另一个 ZFC 模型存在。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smodels_d (ω c T : M.Domain) : Prop := ∃ X R E C,
  Smdl_d I c X R ∧ M.IsFunctionSpace I E ω X ∧ Scode_d I ω C ∧ M.MemberSubset T C ∧
    ∀ a, M.mem a T → ∀ f, M.mem f E → Satisfies_d I ω c a f

def smodels_m {n} (ω c T : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (smdl_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.conj (Formula.isFunctionSpace 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken (.bound 3))
        (.conj (scode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken .newest)
          (.conj (Formula.subset T.weaken.weaken.weaken.weaken .newest)
            (Formula.forallMem T.weaken.weaken.weaken.weaken (Formula.forallMem (.bound 2)
              (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
                c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest))))))))))

@[simp] theorem smodels_closed_l {n} (ω c T : Term n)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hT : T.freeSupport = []) :
    (smodels_m (𝒞 := 𝒞) ω c T).FreeClosed := by
  simp -implicitDefEqProofs [smodels_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace, hω, hc, hT]

theorem smodels_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c T : Term n) :
    Formula.satisfies ρ (smodels_m (𝒞 := 𝒞) ω c T) ↔ Smodels_d I (ω.eval ρ) (c.eval ρ) (T.eval ρ) := by
  simp only [smodels_m, Smodels_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smdl_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE, scode_sat_l I hE,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, satisfies_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 给定结构的全部内部有效公式组成实际理论，结构码确实满足这套理论。 -/
theorem smodels_theory_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) : ∃ T, Smodels_d I ω c T ∧ ∀ a, M.mem a T ↔
      (∃ n F k, Sformula_d I ω a n F k) ∧
        ∀ E, M.IsFunctionSpace I E ω X → ∀ f, M.mem f E → Satisfies_d I ω c a f := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push c).push E
  let φ : UnarySchema 3 := {
    body := Formula.forallMem (.bound 1)
      (satisfies_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have hφ a : φ.denote ρ a ↔ ∀ f, M.mem f E → Satisfies_d I ω c a f := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forallMem_iff, satisfies_sat_l I hZF.1]
    rfl
  obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ C
  have ht a : M.mem a T ↔ M.mem a C ∧ ∀ f, M.mem f E → Satisfies_d I ω c a f :=
    (hT a).trans (and_congr_right fun _ => hφ a)
  refine ⟨T, ⟨X, R, E, C, hM, hE, hC, fun a ha => ((ht a).mp ha).1,
    fun a ha => ((ht a).mp ha).2⟩, fun a => ?_⟩
  refine (ht a).trans (and_congr (hC a) ?_)
  constructor
  · intro h D hD f hf
    have he := hZF.1.eq_of_same_members D E (fun g => (hD g).trans (hE g).symm)
    exact h f (he ▸ hf)
  · exact fun h => h E hE

end YesMetaZFC.SetTheory.Internal
