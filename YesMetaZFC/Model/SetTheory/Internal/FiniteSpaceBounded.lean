import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.Notation

/-! # 已有完整有限列空间的有界识别

源包含实际完整有限列空间时，有界检查唯一识别该空间。
覆盖全部内部非标准长度；不额外要求源满足集合论公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def fs_space0_m {d} (ω X A K : Term d) : Formula 1 d := set[d] ⟪
  ⌜K⌝ₛ ⊆ ⌜X⌝ₛ ∧ (∀ f ∈ ⌜X⌝ₛ, f ∈ ⌜K⌝ₛ ↔ ∃ n ∈ ⌜ω⌝ₛ, ⌜fn0_m⌝ₚ(n, ⌜A⌝ₛ, f))⟫
derive_free_closed fs_space0_m

theorem fs_space0_delta_l {d} (ω X A K : Term d) : (fs_space0_m ω X A K).IsDelta0 :=
  .conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.existsMem _ (fn0_delta_l ..))))

theorem fs_space0_iff_l (hKP : M.Models KP) {d K₀} (ρ : Env M d) (ω X A K : Term d)
    (space : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (A.eval ρ) K₀) (sub : M.MemberSubset K₀ (X.eval ρ)) :
    Formula.satisfies ρ (fs_space0_m ω X A K) ↔ K.eval ρ = K₀ := by
  have read f : M.mem f K₀ ↔ ∃ n, M.mem n (ω.eval ρ) ∧ Fn0_d n (A.eval ρ) f :=
    (space f).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l hKP, fn0_function_l hKP⟩)
  simp only [fs_space0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, fn0_sat_l hKP.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨bound, all⟩
    exact hKP.1.eq_of_same_members _ _ fun f => ⟨fun hf => (read f).mpr ((all f (bound f hf)).mp hf),
      fun hf => (all f (sub f hf)).mpr ((read f).mp hf)⟩
  · intro eq
    exact eq.symm ▸ ⟨sub, fun f _ => read f⟩

end YesMetaZFC.SetTheory.Internal
