import YesMetaZFC.Model.SetTheory.Internal.SourceCollection
import YesMetaZFC.Model.SetTheory.Internal.SourceSequences
import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.SetTheory.Notation

/-! # 源闭包在背景模型中的单一公式

量化源自身的全部内部程序码、赋值和集合参数。具名量词直接编译到已有公式，
因此有限历史可用背景的分离及依赖选择处理，也覆盖非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

@[simp] private theorem sc_space_closed_l {d} (E ω X : Term d)
    (he : E.freeSupport = []) (hw : ω.freeSupport = []) (hx : X.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l E ω X).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace, Definitional.Formula.FreeClosed, he, hw, hx]

/-- 相对化直接读取已有实际隶属模型；不改变原公式或其量词强度。 -/
theorem sc_relative_sat_l (I : kpair_convention_l.Interpretation M) {c X R : M.Domain}
    (hm : Smem_d I c X R) (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
    {n d} (φ : Formula 1 n) (hc : φ.FreeClosed) (η : Env (rt_model_l X nx) n)
    (ρ : Env M d) (T : Term d) (e : Fin n → Term d)
    (ht : T.eval ρ = X) (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (lr_rel_m φ T e) ↔ Formula.satisfies η φ :=
  (lr_rel_decode_l I hm.1 hm.2 hX φ hc ⟨η.bound, η.free⟩ ρ T e ht he).trans
    (smem_formula_l I hm nx φ η).symm

def sc_small0_m {d} (X A : Term d) : Formula 1 d := set[d] ⟪
  ∃ μ ∈ ⌜X⌝ₛ, ∃ f ∈ ⌜X⌝ₛ, ⌜sc_index_m⌝ₚ(μ, ⌜A⌝ₛ, f)⟫
derive_free_closed sc_small0_m

theorem sc_small0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X A : Term d) :
    Formula.satisfies ρ (sc_small0_m X A) ↔ Sc_small_d (X.eval ρ) (A.eval ρ) := by
  simp only [sc_small0_m, Formula.satisfies_existsMem_iff, sc_index_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨μ, hμ, f, hf, idx⟩ => ⟨μ, f, hμ, hf, idx⟩,
    fun ⟨μ, f, hμ, hf, idx⟩ => ⟨μ, hμ, f, hf, idx⟩⟩

def sc_separation_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → f ∈ E → D ∈ ⌜X⌝ₛ → ∃ A ∈ ⌜X⌝ₛ,
      ∀ x, x ∈ A ↔ x ∈ D ∧ (∃ g,
        ⌜senv_update_m (𝒞 := kpair_convention_l)⌝ₚ(f, i, x, g) ∧
        ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, g))⟫
derive_free_closed sc_separation_m

theorem sc_separation_sat_l (hE : Extensional M) (I : kpair_convention_l.Interpretation M)
    {d} (ρ : Env M d) (ω X R : Term d) : Formula.satisfies ρ (sc_separation_m ω X R) ↔
      ∀ E F n r i f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem f E → M.mem D (X.eval ρ) →
          ∃ A, M.mem A (X.eval ρ) ∧ Ssep_d I (X.eval ρ) (R.eval ρ) E F n r i f D A := by
  simp only [sc_separation_m, Ssep_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    sfm_sat_l I hE, senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def sc_uniform0_m {d} (ω X R A : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i j f,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → j ∈ ⌜ω⌝ₛ → i ≠ j → f ∈ E →
    (∀ x ∈ ⌜A⌝ₛ, ∃ y ∈ ⌜X⌝ₛ,
      ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)) →
    ∃ B ∈ ⌜X⌝ₛ, ∃ C ∈ ⌜X⌝ₛ, ⌜fn0_m⌝ₚ(⌜A⌝ₛ, C, B) ∧ (∀ x y,
      ⌜rd_entry0_m⌝ₚ(x, y, B) →
        ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y))⟫
derive_free_closed sc_uniform0_m

def sc_collection0_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ A ∈ ⌜X⌝ₛ, ⌜sc_small0_m⌝ₚ(⌜X⌝ₛ, A) → ⌜sc_uniform0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, A)⟫
derive_free_closed sc_collection0_m

theorem sc_collection0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω X R : Term d) :
    Formula.satisfies ρ (sc_collection0_m ω X R) ↔ Sc_collection_d (kp_pair_l hKP) (ω.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [sc_collection0_m, sc_uniform0_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isFunctionSpace_iff (kp_pair_l hKP) hKP.1,
    sfm_sat_l (kp_pair_l hKP) hKP.1, Formula.satisfies_mem_iff, Formula.extensionalNe,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, fn0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    sbin_sat_l (kp_pair_l hKP) hKP.1, sc_small0_sat_l hKP, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h D _ small E F n r i j f A hE hF hr hi hj hij hf hA sub total
    obtain ⟨B, hB, C, hC, fn, select⟩ := h A hA (small.mono_l sub) E F n r i j f hE hF hr hi hj hij hf total
    exact ⟨B, C, hB, hC, fn, select⟩
  · intro h A hA small E F n r i j f hE hF hr hi hj hij hf total
    obtain ⟨B, C, hB, hC, fn, select⟩ := h A hA small E F n r i j f A hE hF hr hi hj hij hf hA (fun _ h => h) total
    exact ⟨B, hB, C, hC, fn, select⟩

def sc_sequences0_m {d} (ω X : Term d) : Formula 1 d := set[d] ⟪
  (∀ A ∈ ⌜X⌝ₛ, ∃ K ∈ ⌜X⌝ₛ, ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, A, K)) ∧
  (∀ A ∈ ⌜X⌝ₛ, ∀ K ∈ ⌜X⌝ₛ, ∀ μ ∈ ⌜X⌝ₛ, ∀ e ∈ ⌜X⌝ₛ,
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, A, K) → ⌜ω⌝ₛ ⊆ μ →
    ⌜sc_index_m⌝ₚ(μ, A, e) → ∃ f ∈ ⌜X⌝ₛ, ⌜sc_index_m⌝ₚ(μ, K, f))⟫
derive_free_closed sc_sequences0_m

theorem sc_sequences0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω X : Term d) :
    Formula.satisfies ρ (sc_sequences0_m ω X) ↔ Sc_sequences_d (kp_pair_l hKP) (ω.eval ρ) (X.eval ρ) := by
  simp only [sc_sequences0_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
    fseq_space_sat_l (kp_pair_l hKP) hKP.1, sc_index_sat_l hKP, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨s, i⟩ => ⟨s, fun A K μ e hA hK hμ he => i A hA K hK μ hμ e he⟩,
    fun h => ⟨h.space, fun A hA K hK μ hμ e he => h.index A K μ e hA hK hμ he⟩⟩

end YesMetaZFC.SetTheory.Internal
