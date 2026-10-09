import YesMetaZFC.Model.SetTheory.Internal.TypeMinusSemantics
import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 完整类型的前驱算子

只改变查询的公式码，保留原名字列。查询之间的关系由实际语法证书定义，
不量化真值保持条件；前驱类型是上一级类型在这条关系下的逆像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tm_code_d (ω z z' : M.Domain) : Prop := ∃ a a' n F r m G u,
  Sc_num_d I ω a z ∧ Sc_num_d I ω a' z' ∧
    Sformula_d I ω a n F r ∧ Sformula_d I ω a' m G u ∧ Sr_minus_d I ω F n r G m u

def tm_code_m {d} (ω z z' : Term d) : Formula 1 d := set[d] ⟪∃ a a' n F r m G u,
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜z⌝ₛ) ∧
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a', ⌜z'⌝ₛ) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, n, F, r) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a', m, G, u) ∧
  ⌜sr_minus_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, F, n, r, G, m, u)⟫
derive_free_closed tm_code_m

theorem tm_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z z' : Term d) :
    Formula.satisfies ρ (tm_code_m ω z z') ↔ Tm_code_d I (ω.eval ρ) (z.eval ρ) (z'.eval ρ) := by
  simp only [tm_code_m, Tm_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sc_num_sat_l I hE, sformula_sat_l I hE, sr_minus_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem Tm_code_d.natural_l (hZF : M.Models ZF) {ω z w : M.Domain} (hω : M.IsOmega ω)
    (h : Tm_code_d I ω z w) : M.mem z ω ∧ M.mem w ω := by
  obtain ⟨_, _, _, _, _, _, _, _, hz, hw, _⟩ := h
  exact ⟨sc_num_natural_l I hZF hω hz, sc_num_natural_l I hZF hω hw⟩

def Tm_query_d (ω p q : M.Domain) : Prop := ∃ z e z', I.Codes p z e ∧ I.Codes q z' e ∧ Tm_code_d I ω z z'

def tm_query_m {d} (ω p q : Term d) : Formula 1 d := set[d] ⟪∃ z e z',
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ, z, e) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ, z', e) ∧
    ⌜tm_code_m⌝ₚ(⌜ω⌝ₛ, z, z')⟫
derive_free_closed tm_query_m

theorem tm_query_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω p q : Term d) :
    Formula.satisfies ρ (tm_query_m ω p q) ↔ Tm_query_d I (ω.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [tm_query_m, Tm_query_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, tm_code_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Tm_minus_d (ω D t u : M.Domain) : Prop :=
  ∀ p, M.mem p u ↔ M.mem p D ∧ ∃ q, Tm_query_d I ω p q ∧ M.mem q t

def tm_minus_m {d} (ω D t u : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜u⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ (∃ q, ⌜tm_query_m⌝ₚ(⌜ω⌝ₛ, p, q) ∧ q ∈ ⌜t⌝ₛ)⟫
derive_free_closed tm_minus_m

theorem tm_minus_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D t u : Term d) :
    Formula.satisfies ρ (tm_minus_m ω D t u) ↔
      Tm_minus_d I (ω.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [tm_minus_m, Tm_minus_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    tm_query_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem tm_minus_exists_l (hZF : M.Models ZF) (ω D t : M.Domain) : ∃ u, Tm_minus_d I ω D t u := by
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (tm_query_m (.bound 3) (.bound 1) .newest) (.mem .newest (.bound 2))) }
  let ρ : Env M 2 := ⟨Fin.cases t (fun _ => ω), fun _ => ω⟩
  obtain ⟨u, sep⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨u, fun p => (sep p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, tm_query_sat_l I hZF.1,
    Formula.satisfies_mem_iff]; rfl

theorem Tm_minus_d.unique_l (hE : Extensional M) {ω D t u v : M.Domain}
    (h : Tm_minus_d I ω D t u) (k : Tm_minus_d I ω D t v) : u = v :=
  hE.eq_of_same_members u v (fun p => (h p).trans (k p).symm)

end YesMetaZFC.SetTheory.Internal
