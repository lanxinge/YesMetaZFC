import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource
import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax

/-! # 有限支撑源证书的一阶编码

证书仍是实际的全内部分离、小定义域统一化、有限列空间与塌缩性质。
同一个编码供历史分离使用，初等传输和复制继续消费原证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem ep_closure_closed_l : (Definitional.Formula.conj sc_algebra_m sc_collapse_m).FreeClosed := by
  simp -implicitDefEqProofs [sc_algebra_m, sc_collapse_m, Definitional.Formula.FreeClosed]

def ep_closure_m {d} (X : Term d) : Formula 1 d := lr_rel_m (.conj sc_algebra_m sc_collapse_m) X Fin.elim0

@[simp] theorem ep_closure_free_closed_l {d} (X : Term d) (hx : X.freeSupport = []) : (ep_closure_m X).FreeClosed :=
  lr_rel_closed_l _ ep_closure_closed_l X Fin.elim0 hx (fun i => Fin.elim0 i)

def ep_source_m {d} (ω κ K X R : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ Trans(⌜X⌝ₛ) ∧ ⌜ω⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜ω⌝ₛ ⊆ ⌜κ⌝ₛ ∧ ⌜K⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜sc_small0_m⌝ₚ(⌜X⌝ₛ, ⌜κ⌝ₛ) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜K⌝ₛ) ∧
  (∃ c, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜X⌝ₛ, ⌜R⌝ₛ)) ∧
  ⌜ep_closure_m⌝ₚ(⌜X⌝ₛ) ∧ ⌜sc_separation_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜sc_collection0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧ ⌜sc_sequences0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ)⟫
derive_free_closed ep_source_m

theorem ep_source_sat_l {d} (ρ : Env M d) (ω κ K X R : Term d) :
    Formula.satisfies ρ (ep_source_m ω κ K X R) ↔ Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have closure (hX : M.TransitiveSet (X.eval ρ)) (hω : M.mem (ω.eval ρ) (X.eval ρ))
      : Formula.satisfies ρ (ep_closure_m X) ↔
        Sc_algebra_d (X.eval ρ) ∧ Sc_collapse_d (X.eval ρ) := by
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, hω⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 0 := ⟨Fin.elim0, fun _ => ⟨ω.eval ρ, hω⟩⟩
    exact (sc_relative_sat_l hX nx _ ep_closure_closed_l η ρ X Fin.elim0 rfl (fun i => Fin.elim0 i)).trans
      ((Formula.satisfies_conj_iff ..).trans (and_congr
        (sc_algebra_sat_l (ZF.modelsKP hZF) hX nx η) (sc_collapse_sat_l (ZF.modelsKP hZF) hX nx η)))
  simp only [ep_source_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    sc_small0_sat_l (ZF.modelsKP hZF), fseq_space_sat_l I hZF.1, Formula.satisfies_exists_iff,
    smem_sat_l I, sc_separation_sat_l hZF.1 I, sc_collection0_sat_l (ZF.modelsKP hZF),
    sc_sequences0_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hw, ht, hω, hκ, below, hk, small, seq, code, hc, sep, collect, sequences⟩
    obtain ⟨algebra, collapse⟩ := (closure ht hω).mp hc
    exact ⟨hw, below, ht, hω, hκ, small, hk, seq, code, ⟨sep, algebra⟩, collect, sequences, collapse⟩
  · intro h
    exact ⟨h.omega, h.transitive, h.omega_mem, h.cardinal_mem, h.below, h.finite_mem, h.cardinal_small,
      h.finite, h.code, (closure h.transitive h.omega_mem).mpr ⟨h.theory.algebra, h.collapse⟩,
      h.theory.separation, h.collection, h.sequences⟩

end YesMetaZFC.SetTheory.LargeCardinal
