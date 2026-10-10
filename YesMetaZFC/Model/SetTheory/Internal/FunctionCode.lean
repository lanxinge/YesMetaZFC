import YesMetaZFC.Model.SetTheory.Internal.DeltaCode

/-! # 源内部函数域及其公式代码

函数和一个值域界都属于源；这个定义有实际统一化与常值实例。代码中值域界
是局部存在变量，后续翻译可以量化函数对象并仍覆盖源的每个对象值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sfun_d (X D f : M.Domain) : Prop := M.mem f X ∧ ∃ C, M.mem C X ∧ Fn0_d D C f

def sfun_m {d} (X D f : Term d) : Formula 1 d := .conj (.mem f X)
  (Formula.existsMem X (fn0_m D.weaken .newest f.weaken))
derive_free_closed sfun_m

theorem sfun_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X D f : Term d) :
    Formula.satisfies ρ (sfun_m X D f) ↔ Sfun_d (X.eval ρ) (D.eval ρ) (f.eval ρ) := by
  simp only [sfun_m, Sfun_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, fn0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Sfun_d.function_l {X D f : M.Domain} (h : Sfun_d X D f) (hX : M.TransitiveSet X) : Fn0_d D X f :=
  h.2.elim fun C hC => hC.2.mono_target_l (hX C hC.1)

theorem sfm_function_l (hZF : M.Models ZF) {ω n F i s u σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hσ : M.mem σ ω) (hi : M.mem i σ) (hs : M.mem s σ) (hu : M.mem u σ)
    (hus : u ≠ s) (hui : u ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f B D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I i B f → M.PairMember I s D f → (Ssat_d I X R E G m k f ↔ Sfun_d X D B) := by
  let q : Fin 3 → M.Domain := Fin.cases s (Fin.cases u (fun _ => i))
  let φ : Formula 1 3 := fn0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, r, h, hh⟩ := sfm_delta_l I hZF hω hF φ (by simp -implicitDefEqProofs [φ]) (fn0_delta_l ..)
    q hσ (Fin.cases hs (Fin.cases hu (fun _ => hi)))
  have huω := hω.transitive hZF σ hσ u hu
  obtain ⟨m, G, k, g, hg⟩ := sfm_ex_l I hZF hω h.program huω h.root
  refine ⟨m, G, k, h.comp I g, fun X R E c f B D hX hm hE hf hiB hsD => ?_⟩
  have read C a (hC : M.mem C X) (ha : Senv_update_d I f u C a) :
      Ssat_d I X R E J v r a ↔ Fn0_d D C B := by
    let ρ : Env M 3 := ⟨Fin.cases D (Fin.cases C (fun _ => B)), fun _ => B⟩
    have hp : ∀ z, M.PairMember I (q z) (ρ.bound z) a := Fin.cases
      ((ha.2 s D).mpr (Or.inr ⟨Ne.symm hus, hsD⟩)) (Fin.cases ((ha.2 u C).mpr (Or.inl ⟨rfl, rfl⟩))
        (fun _ => (ha.2 i B).mpr (Or.inr ⟨Ne.symm hui, hiB⟩)))
    exact (hh X R E c a ρ hX hm hE ((hE a).mpr (ha.function_l I ((hE f).mp hf) huω hC)) hp).trans
      (fn0_sat_l hZF.1 ..)
  rw [hg X R E f hf]
  constructor
  · rintro ⟨C, a, hC, ha, ht⟩
    exact ⟨((hE f).mp hf).output_mem_of_pairMember hiB, C, hC, (read C a hC ha).mp ht⟩
  · rintro ⟨_, C, hC, ht⟩
    obtain ⟨a, ha, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) huω hC
    exact ⟨C, a, hC, ha, (read C a hC ha).mpr ht⟩

end YesMetaZFC.SetTheory.Internal
