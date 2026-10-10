import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 传递集合上的有界公式程序

在任意已有内部程序之后编译固定的 Δ₀ 模板。解码隶属结构并用传递性取得
背景中的同一原公式，因此函数图和有序对条件无需另造语义提供器。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Scompile_d.delta_l {d ω n F k v X R E c f} {φ : Formula 1 d}
    (h : Scompile_d I ω n F k v φ) (hφ : φ.FreeClosed) (hd : φ.IsDelta0) (ρ : Env M d)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hE : M.IsFunctionSpace I E ω X)
    (hf : M.mem f E) (hp : ∀ i, M.PairMember I (v i) (ρ.bound i) f) :
    Ssat_d I X R E F n k f ↔ Formula.satisfies ρ φ := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  let η : Env (rt_model_l X hn) d := ⟨fun i => ⟨ρ.bound i, ((hE f).mp hf).output_mem_of_pairMember (hp i)⟩,
    fun _ => ⟨x, hx⟩⟩
  let θ : Env (smdl_structure_l I (R := R) hm.1.2.1) d := ⟨η.bound, η.free⟩
  have hh : Formula.satisfies θ φ ↔ Formula.satisfies ρ φ :=
    (smem_formula_l I hm hn φ η).symm.trans ((rt_model_delta_l hX hn hd η).trans (Formula.closed_env_l φ hφ rfl))
  exact (h X R hm.1.2.1 E hE f hf θ hp).trans hh

theorem sfm_delta_l (hZF : M.Models ZF) {ω n F σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed) (hd : φ.IsDelta0)
    (v : Fin d → M.Domain) (hσ : M.mem σ ω) (hv : ∀ i, M.mem (v i) σ) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E c f (ρ : Env M d), M.TransitiveSet X → Smem_d I c X R →
      M.IsFunctionSpace I E ω X → M.mem f E → (∀ i, M.PairMember I (v i) (ρ.bound i) f) →
      (Ssat_d I X R E G m k f ↔ Formula.satisfies ρ φ) := by
  obtain ⟨m, G, k, hg, hc⟩ := source_compile_core_l I hZF hω (source_core_l φ) (source_core_closed_l φ hφ) v hσ hv hF
  have h : Scompile_d I ω m G k v φ := fun X R hX E hE f hf ρ hp =>
    (hc X R hX E hE f hf ρ hp).trans (source_core_sat_l φ ρ)
  exact ⟨m, G, k, hg, fun _ _ _ _ _ ρ hX hm hE hf hp => h.delta_l I hφ hd ρ hX hm hE hf hp⟩

end YesMetaZFC.SetTheory.Internal
