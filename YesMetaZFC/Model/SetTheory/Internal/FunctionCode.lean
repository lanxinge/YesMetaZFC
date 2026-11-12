import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
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

/-- 固定模板的原关系语义；传递性只在下方读取背景 Δ₀ 公式时使用。 -/
theorem sfm_template_l (hZF : M.Models ZF) {ω n F σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (v : Fin d → M.Domain) (hσ : M.mem σ ω) (hv : ∀ i, M.mem (v i) σ) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ Scompile_d I ω m G k v φ := by
  obtain ⟨m, G, k, hg, hc⟩ := source_compile_core_l I hZF hω (source_core_l φ) (source_core_closed_l φ hφ) v hσ hv hF
  have sem : Scompile_d I ω m G k v φ := fun X R hX E hE f hf ρ hp =>
    (hc X R hX E hE f hf ρ hp).trans (source_core_sat_l φ ρ)
  exact ⟨m, G, k, hg, sem⟩

theorem sfm_delta_l (hZF : M.Models ZF) {ω n F σ} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed) (hd : φ.IsDelta0)
    (v : Fin d → M.Domain) (hσ : M.mem σ ω) (hv : ∀ i, M.mem (v i) σ) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E c f (ρ : Env M d), M.TransitiveSet X → Smem_d I c X R →
      M.IsFunctionSpace I E ω X → M.mem f E → (∀ i, M.PairMember I (v i) (ρ.bound i) f) →
      (Ssat_d I X R E G m k f ↔ Formula.satisfies ρ φ) := by
  obtain ⟨m, G, k, hg, h⟩ := sfm_template_l I hZF hω hF φ hφ v hσ hv
  exact ⟨m, G, k, hg, fun _ _ _ _ _ ρ hX hm hE hf hp => h.delta_l I hφ hd ρ hX hm hE hf hp⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部函数域及其公式代码

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
  have huω := hω.transitive (ZF.modelsKP hZF) σ hσ u hu
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
