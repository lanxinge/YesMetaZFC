import YesMetaZFC.Model.SetTheory.Internal.SkolemSyntax

/-! # 完整内部赋值上的 Tarski–Vaught 条件

量化全部内部公式码及全部 ω→N 赋值，要求大结构中的存在见证可取在 N 中。
这里已经不限制赋值列外为固定基点。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Stv_d (ω c X C N : M.Domain) : Prop := ∀ a i f,
  M.mem a C → M.mem i ω → M.IsSetFunctionFromTo I f ω N →
    (∃ x g, M.mem x X ∧ Senv_update_d I f i x g ∧ Satisfies_d I ω c a g) →
      ∃ x g, M.mem x N ∧ Senv_update_d I f i x g ∧ Satisfies_d I ω c a g

private def tv_wit_m {d} (ω c A a i f : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) A.weaken.weaken)
    (.conj (senv_update_m (𝒞 := 𝒞) f.weaken.weaken i.weaken.weaken (.bound 1) .newest)
      (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken c.weaken.weaken a.weaken.weaken .newest))))
derive_free_closed tv_wit_m

def stv_m {d} (ω c X C N : Term d) : Formula 1 d :=
  Formula.forallMem C (Formula.forallMem ω.weaken (.forallE (.imp
    (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken N.weaken.weaken.weaken)
    (.imp (tv_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken c.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
      (tv_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken c.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))
derive_free_closed stv_m

theorem stv_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X C N : Term d) :
    Formula.satisfies ρ (stv_m (𝒞 := 𝒞) ω c X C N) ↔
      Stv_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (C.eval ρ) (N.eval ρ) := by
  simp only [stv_m, Stv_d, tv_wit_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_mem_iff, senv_update_sat_l I hE,
    satisfies_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h a i f ha hi hf => h a ha i hi f hf, fun h a ha i hi f hf => h a i f ha hi hf⟩

end YesMetaZFC.SetTheory.Internal
