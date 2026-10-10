import YesMetaZFC.Model.SetTheory.Internal.CanonicalCode
import YesMetaZFC.Model.SetTheory.Internal.Compiler

/-! # 规范自然数码上的统一满足关系

自然数码通过唯一解码接入原内部满足关系。原 Project 公式可直接编译到这一
接口，语义对应对全部实际编码结构成立。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_sat_d (ω c z f : M.Domain) : Prop := ∃ a, Sc_num_d I ω a z ∧ Satisfies_d I ω c a f

def sc_sat_m {d} (ω c z f : Term d) : Formula 1 d := .existsE
  (.conj (sc_num_m (𝒞 := 𝒞) ω.weaken .newest z.weaken)
    (satisfies_m (𝒞 := 𝒞) ω.weaken c.weaken .newest f.weaken))
derive_free_closed sc_sat_m

theorem sc_sat_formula_l (hE : Extensional M) {d} (ρ : Env M d) (ω c z f : Term d) :
    Formula.satisfies ρ (sc_sat_m (𝒞 := 𝒞) ω c z f) ↔ Sc_sat_d I (ω.eval ρ) (c.eval ρ) (z.eval ρ) (f.eval ρ) := by
  simp only [sc_sat_m, Sc_sat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sc_num_sat_l I hE, satisfies_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sc_sat_decode_l (hZF : M.Models ZF) {ω c z a f} (hω : M.IsOmega ω) (ha : Sc_num_d I ω a z) :
    Sc_sat_d I ω c z f ↔ Satisfies_d I ω c a f := by
  refine ⟨fun ⟨b, hb, h⟩ => ?_, fun h => ⟨a, ha, h⟩⟩
  exact sc_num_injective_l I hZF hω hb ha ▸ h

/-- 给定原公式和实际模型参数，自动生成自然数码、赋值及精确真值等价。 -/
theorem source_nat_satisfaction_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hM.2.1) d) : ∃ z E f,
      M.mem z ω ∧ M.IsFunctionSpace I E ω X ∧ M.mem f E ∧
        (Sc_sat_d I ω c z f ↔ Formula.satisfies ρ φ) := by
  obtain ⟨a, E, f, ⟨n, F, k, ha⟩, hE, hf, hs⟩ := source_satisfaction_l I hZF hω hM φ hφ ρ
  obtain ⟨z, hz⟩ := sc_num_exists_l I hZF hω ha
  exact ⟨z, E, f, sc_num_natural_l I hZF hω hz, hE, hf, (sc_sat_decode_l I hZF hω hz).trans hs⟩

end YesMetaZFC.SetTheory.Internal
