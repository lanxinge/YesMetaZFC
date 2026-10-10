import YesMetaZFC.Model.SetTheory.Internal.FormulaCode

/-! # 结构码与公式码上的统一内部满足关系

调用只提供模型内的结构码、公式码和赋值。解码、赋值空间与真值递归均由
已实现的原公式刻画，所选中间集合不改变结果；全部满足对还能收集成一个内部集合。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Satisfies_d (ω c a f : M.Domain) : Prop := ∃ X R E n F k,
  Smdl_d I c X R ∧ Sformula_d I ω a n F k ∧ M.IsFunctionSpace I E ω X ∧ Ssat_d I X R E F n k f

def satisfies_m {n} (ω c a f : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (smdl_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4))
      (.conj (sformula_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
        a.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.conj (Formula.isFunctionSpace 𝒞 (.bound 3) ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
          (ssat_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2) .newest
            f.weaken.weaken.weaken.weaken.weaken.weaken)))))))))
@[simp] theorem satisfies_closed_l {n} (ω c a f : Term n)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (ha : a.freeSupport = []) (hf : f.freeSupport = []) :
    (satisfies_m (𝒞 := 𝒞) ω c a f).FreeClosed := by
  simp -implicitDefEqProofs [satisfies_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace, hω, hc, ha, hf]

theorem satisfies_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c a f : Term n) :
    Formula.satisfies ρ (satisfies_m (𝒞 := 𝒞) ω c a f) ↔
      Satisfies_d I (ω.eval ρ) (c.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [satisfies_m, Satisfies_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smdl_sat_l I, sformula_sat_l I hE, Formula.satisfies_isFunctionSpace_iff I hE, ssat_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 统一满足关系精确还原为已指定解码上的真值，不依赖任何任选的中间见证。 -/
theorem satisfies_decode_l (hE : Extensional M) {ω c a X R E n F k f}
    (hM : Smdl_d I c X R) (hF : Sformula_d I ω a n F k) (hA : M.IsFunctionSpace I E ω X) :
    Satisfies_d I ω c a f ↔ Ssat_d I X R E F n k f := by
  constructor
  · rintro ⟨Y, S, D, m, G, j, hN, hG, hD, h⟩
    obtain ⟨hx, hr⟩ := smdl_unique_l I hM hN
    obtain ⟨hn, hf, hk⟩ := sformula_unique_l I hE hF hG
    subst Y
    subst S
    subst m
    subst G
    subst j
    have hd := hE.eq_of_same_members D E (fun g => (hD g).trans (hA g).symm)
    exact hd ▸ h
  · exact fun h => ⟨X, R, E, n, F, k, hM, hF, hA, h⟩

/-- 一次构造完整赋值空间、唯一真值表及指定公式的真值集。 -/
theorem smdl_table_l (hZF : M.Models ZF) {ω c a X R n F k}
    (hM : Smdl_d I c X R) (hF : Sformula_d I ω a n F k) : ∃ E H Y,
    M.IsFunctionSpace I E ω X ∧ Seval_d I X R E F n H ∧ M.PairMember I k Y H ∧
      M.MemberSubset Y E ∧ (∀ f, Satisfies_d I ω c a f ↔ M.mem f Y) ∧
      ∀ D J, M.IsFunctionSpace I D ω X → Seval_d I X R D F n J → D = E ∧ J = H := by
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.2.1.1
  obtain ⟨Y, hY⟩ := (hH.1.2.2 k).mp hF.2.2
  obtain ⟨P, _, hStep⟩ := hH.2 k hF.2.2 Y hY
  refine ⟨E, H, Y, hE, hH, hY, fun f hf => ((hStep f).mp hf).1, fun f => ?_, ?_⟩
  · exact (satisfies_decode_l I hZF.1 hM hF hE).trans (ssat_value_l I hZF hH hY f)
  · intro D J hD hJ
    have he := hZF.1.eq_of_same_members D E (fun f => (hD f).trans (hE f).symm)
    subst D
    exact ⟨rfl, seval_unique_l I hZF hJ hH⟩

/-- 一个实际内部集合同时记录给定结构对全部内部有限公式及赋值的满足关系。 -/
theorem smdl_satisfaction_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) : ∃ C E S,
    Scode_d I ω C ∧ M.IsFunctionSpace I E ω X ∧ M.IsSetRelation I S ∧
      ∀ a f, M.PairMember I a f S ↔ M.mem a C ∧ M.mem f E ∧ Satisfies_d I ω c a f := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) C E
  let ρ : Env M 4 := (((⟨fun _ => c, fun _ => c⟩ : Env M 1).push ω).push C).push E
  let φ : BinarySchema 4 := {
    body := .conj (.mem (.bound 1) (.bound 3)) (.conj (.mem .newest (.bound 2))
      (satisfies_m (𝒞 := 𝒞) (.bound 4) (.bound 5) (.bound 1) .newest)) }
  have hφ a f : φ.denote ρ a f ↔ M.mem a C ∧ M.mem f E ∧ Satisfies_d I ω c a f := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, satisfies_sat_l I hZF.1]
    rfl
  obtain ⟨S, hS, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ U
  refine ⟨C, E, S, hC, hE, hS.1, fun a f => (hs a f).trans ?_⟩
  rw [hφ a f]
  exact ⟨fun h => h.2.2, fun h => ⟨(hU a).mpr (Or.inl h.1), (hU f).mpr (Or.inr h.2.1), h⟩⟩

end YesMetaZFC.SetTheory.Internal
