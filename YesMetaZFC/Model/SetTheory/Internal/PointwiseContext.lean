import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 逐点编译的实际解释环境

编译程序与模型无关。解释存在量词只需源中的常值函数；这里把这一
已由源理论构造的性质写成原公式，供同时量化所有模型的内部归纳使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_context_d (ω c X R D E : M.Domain) : Prop := M.TransitiveSet X ∧ Smem_d I c X R ∧
  M.IsFunctionSpace I E ω X ∧ M.mem D X ∧
  ∀ x, M.mem x X → ∃ f, Sfun_d X D f ∧ ∀ v, M.mem v D → Rd_entry_d v x f

def pe_context_m {d} (ω c X R D E : Term d) : Formula 1 d :=
  .conj (Formula.isTransitive X) (.conj (smem_m (𝒞 := 𝒞) c X R)
    (.conj (Formula.isFunctionSpace 𝒞 E ω X) (.conj (.mem D X)
      (Formula.forallMem X (.existsE (.conj (sfun_m X.weaken.weaken D.weaken.weaken .newest)
        (Formula.forallMem D.weaken.weaken (rd_entry0_m .newest (.bound 2) (.bound 1)))))))))

@[simp] theorem pe_context_closed_l {d} (ω c X R D E : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hD : D.freeSupport = []) (hE : E.freeSupport = []) :
    (pe_context_m (𝒞 := 𝒞) ω c X R D E).FreeClosed := by
  simp -implicitDefEqProofs [pe_context_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hc, hX, hR, hD, hE]

theorem pe_context_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X R D E : Term d) :
    Formula.satisfies ρ (pe_context_m (𝒞 := 𝒞) ω c X R D E) ↔
      Pe_context_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (D.eval ρ) (E.eval ρ) := by
  simp only [pe_context_m, Pe_context_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    smem_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, sfun_sat_l hE,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem sc_pe_context_l (hZF : M.Models ZF) {ω c X R D E : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hD : M.mem D X) (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E ω X) :
    Pe_context_d (kp_pair_l (ZF.modelsKP hZF)) ω c X R D E := by
  refine ⟨hX, hm, hE, hD, fun x hx => ?_⟩
  obtain ⟨f, C, hf, hC, hg, hs⟩ := sc_constant_l hZF hω hX hm theory hD hx
  exact ⟨f, ⟨hf, C, hC, hg⟩, fun v hv => (hs v x).mpr ⟨hv, rfl⟩⟩

end YesMetaZFC.SetTheory.Internal
