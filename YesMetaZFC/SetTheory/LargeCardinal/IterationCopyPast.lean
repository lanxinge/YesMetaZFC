import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax

/-! # 含恒等步的复制历史一致性

两行之间尚无活动步时保留同一行；否则记录区间内一个真实支撑及共同秩段。
若左端本身活动，见证必须取该左端，故原扩展器的最大强度不被弱化。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_past_d (L i j X A π Y B σ : M.Domain) : Prop :=
  (X = Y ∧ A = B ∧ π = σ ∧ ∀ ρ, ¬ Rd_entry_d i ρ L) ∨
  ∃ k ρ φ, (i = k ∨ M.mem i k) ∧ M.mem k j ∧ Rd_entry_d k ρ L ∧
    (∀ ν, Rd_entry_d i ν L → i = k) ∧ Pn_agree_d X A π Y B σ ρ φ ∧ Es_strength_d X ρ Y

def ic_past_m {d} (L i j X A π Y B σ : Term d) : Formula 1 d := set[d] ⟪
  (⌜X⌝ₛ = ⌜Y⌝ₛ ∧ ⌜A⌝ₛ = ⌜B⌝ₛ ∧ ⌜π⌝ₛ = ⌜σ⌝ₛ ∧
    (∀ ρ, ¬ ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ))) ∨
  (∃ k ρ φ, (⌜i⌝ₛ = k ∨ ⌜i⌝ₛ ∈ k) ∧ k ∈ ⌜j⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(k, ρ, ⌜L⌝ₛ) ∧
    (∀ ν, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ν, ⌜L⌝ₛ) → ⌜i⌝ₛ = k) ∧
    ⌜pn_agree_m⌝ₚ(⌜X⌝ₛ, ⌜A⌝ₛ, ⌜π⌝ₛ, ⌜Y⌝ₛ, ⌜B⌝ₛ, ⌜σ⌝ₛ, ρ, φ) ∧
    ⌜es_strength0_m⌝ₚ(⌜X⌝ₛ, ρ, ⌜Y⌝ₛ))⟫
derive_free_closed ic_past_m

theorem ic_past_sat_l (hKP : M.Models KP) {d} (η : Env M d) (L i j X A π Y B σ : Term d) :
    Formula.satisfies η (ic_past_m L i j X A π Y B σ) ↔
      Ic_past_d (L.eval η) (i.eval η) (j.eval η) (X.eval η) (A.eval η) (π.eval η)
        (Y.eval η) (B.eval η) (σ.eval η) := by
  simp only [ic_past_m, Ic_past_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, pn_agree_sat_l hKP, es_strength0_sat_l, Definitional.Term.eval_weaken]; rfl

theorem Ic_past_d.prior_l {L i j X A π Y B σ : M.Domain} (h : Ic_past_d L i j X A π Y B σ) :
    (X = Y ∧ A = B ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X A π Y B σ ρ φ ∧ Es_strength_d X ρ Y := by
  rcases h with ⟨a, b, c, _⟩ | ⟨_, ρ, φ, _, _, _, _, h, e⟩
  · exact Or.inl ⟨a, b, c⟩
  · exact Or.inr ⟨ρ, φ, h, e⟩

theorem Ic_past_d.active_l (hKP : M.Models KP) {L i j X A π Y B σ ρ : M.Domain}
    (h : Ic_past_d L i j X A π Y B σ) (hf : M.IsSetFunction (kp_pair_l hKP) L)
    (hi : Rd_entry_d i ρ L) : ∃ φ, Pn_agree_d X A π Y B σ ρ φ ∧ Es_strength_d X ρ Y := by
  rcases h with ⟨_, _, _, no⟩ | ⟨k, μ, φ, _, _, hk, first, same, exactness⟩
  · exact (no ρ hi).elim
  · have eq := first ρ hi
    subst k
    exact ⟨φ, hf.2 i μ ρ hk hi ▸ same, hf.2 i μ ρ hk hi ▸ exactness⟩

end YesMetaZFC.SetTheory.LargeCardinal
