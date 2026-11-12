import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.SetTheory.Filter.Projection
import YesMetaZFC.SetTheory.Filter.Source
import YesMetaZFC.Model.SetTheory.Internal.FunctionCode

/-! # 源中的实际逆像与代表相等集

两种集合都用固定有界公式在源中分离，供测度协调与商映射的良定义性消费。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sc_pull_l (hZF : M.Models ZF) {ω c X R E t A}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hE : M.mem E X) (ht : M.mem t X) (hA : M.mem A X) : ∃ B, M.mem B X ∧ Pull_d E t A B := by
  let ρ : Env M 2 := ⟨Fin.cases t (fun _ => A), fun _ => A⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨B, hBX, hB⟩ := sc_separate_source_l I hZF hω hX hm theory φ
    (.existsMem _ (rd_entry0_delta_l ..)) ρ (Fin.cases ht (fun _ => hA)) hE
  refine ⟨B, hBX, fun v => (hB v).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]
  rfl

theorem sc_equalizer_l (hZF : M.Models ZF) {ω c X R D f g}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hf : Sfun_d X D f) (hg : M.mem g X) : ∃ A, M.mem A X ∧
      ∀ v, M.mem v A ↔ M.mem v D ∧ ∃ x, M.mem x X ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g := by
  obtain ⟨hfX, C, hC, hFC⟩ := hf
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases g (fun _ => C)), fun _ => C⟩
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 3)
      (.conj (rd_entry0_m (.bound 1) .newest (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3))) }
  obtain ⟨A, hAX, hA⟩ := sc_separate_source_l I hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) ρ (Fin.cases hfX (Fin.cases hg (fun _ => hC))) hD
  refine ⟨A, hAX, fun v => (hA v).trans (and_congr_right fun _ => ?_)⟩
  have read : φ.denote ρ v ↔ ∃ x, M.mem x C ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]
    rfl
  exact read.trans ⟨fun ⟨x, hx, hf, hg⟩ => ⟨x, hX C hC x hx, hf, hg⟩,
    fun ⟨x, _, hf, hg⟩ => ⟨x, (hFC.bound_l hf).2, hf, hg⟩⟩

end YesMetaZFC.SetTheory.Internal
