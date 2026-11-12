import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCode
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Truncation
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel

/-! # 正规性在子集一致的源之间传递

正规性只测试施加源中的 κ 值代表。有限列图编码证明这些代表属于原来
的所属模型，因此跨模型施加保留实际正规性，而不额外假设正规性操作。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def En_source_d (ω κ L X F : M.Domain) : Prop := ∀ n a U D f i α A,
  M.mem n ω → Fn0_d n L a → Rd_entry_d a U F → Ep_space_d κ n D →
  M.mem f X → Fn0_d D κ f → Rd_entry_d i α a → M.mem A U →
  (∀ s, M.mem s A → ∀ x y, Rd_entry_d s x f → Rd_entry_d i y s → M.mem x y) →
  ∃ m b V β B, M.mem m ω ∧ M.SuccessorOf m n ∧ Fn0_d m L b ∧ M.MemberSubset a b ∧
    Rd_entry_d n β b ∧ M.mem β α ∧ Rd_entry_d b V F ∧ M.mem B V ∧
    ∀ s, M.mem s B → En_graph_d n κ A f s

def en_source_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪
  ∀ n a U D f i α A, n ∈ ⌜ω⌝ₛ → ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, a) → ⌜rd_entry0_m⌝ₚ(a, U, ⌜F⌝ₛ) →
    ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) → f ∈ ⌜X⌝ₛ → ⌜fn0_m⌝ₚ(D, ⌜κ⌝ₛ, f) →
    ⌜rd_entry0_m⌝ₚ(i, α, a) → A ∈ U →
    (∀ s ∈ A, ∀ x y, ⌜rd_entry0_m⌝ₚ(s, x, f) → ⌜rd_entry0_m⌝ₚ(i, y, s) → x ∈ y) →
    ∃ m b V β B, m ∈ ⌜ω⌝ₛ ∧ ⌜Formula.isSuccessor⌝ₚ(m, n) ∧ ⌜fn0_m⌝ₚ(m, ⌜L⌝ₛ, b) ∧ a ⊆ b ∧
      ⌜rd_entry0_m⌝ₚ(n, β, b) ∧ β ∈ α ∧ ⌜rd_entry0_m⌝ₚ(b, V, ⌜F⌝ₛ) ∧ B ∈ V ∧
      (∀ s ∈ B, ⌜en_graph_m⌝ₚ(n, ⌜κ⌝ₛ, A, f, s))⟫
derive_free_closed en_source_m

theorem en_source_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X F : Term d) :
    Formula.satisfies ρ (en_source_m ω κ L X F) ↔
      En_source_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  simp only [en_source_m, En_source_d, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry0_sat_l hE, ep_space_sat_l hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, en_graph_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem En_normal_d.source_l {ω κ L F : M.Domain} (h : En_normal_d ω κ L F) (X : M.Domain) :
    En_source_d ω κ L X F := fun n a U D f i α A hn ha hu hd _ => h n a U D f i α A hn ha hu hd

theorem En_source_d.transfer_l (hZF : M.Models ZF) {ω κ K N R K' X S L F : M.Domain}
    (h : En_source_d ω κ L N F) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K N R)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' X S) (subsets : Ea_subset_d ω κ X N) : En_source_d ω κ L X F := by
  intro n a U D f i α A hn ha hu hd hf hfn
  exact h n a U D f i α A hn ha hu hd
    (subsets.function_l hZF source owner hn hd hf hfn) hfn

end YesMetaZFC.SetTheory.LargeCardinal
