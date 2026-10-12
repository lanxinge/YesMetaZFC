import YesMetaZFC.Model.SetTheory.Internal.TypeDropNames

/-! # 裸类型的原语法投影与 dcp

投影是实际查询重编码的逆像，公式自然数码保持不变。定义适用于任意
查询集合，不把语义实现或真值保持作为投影条件；dcp 取紧邻的前缀元数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Td_query_d (n m p q : M.Domain) : Prop := ∃ z E F,
  I.Codes p z E ∧ I.Codes q z F ∧ Td_column_d I n m E F

def td_query_m {d} (n m p q : Term d) : Formula 1 d := set[d] ⟪∃ z E F,
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ, z, E) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ, z, F) ∧
    ⌜td_column_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, E, F)⟫
derive_free_closed td_query_m

theorem td_query_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m p q : Term d) :
    Formula.satisfies ρ (td_query_m n m p q) ↔ Td_query_d I (n.eval ρ) (m.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [td_query_m, Td_query_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, td_column_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem Td_query_d.unique_l (hE : Extensional M) {n m p q r : M.Domain}
    (h : Td_query_d I n m p q) (k : Td_query_d I n m p r) : q = r := by
  obtain ⟨z, E, F, cp, cq, cf⟩ := h
  obtain ⟨z', E', F', cp', cr, cf'⟩ := k
  obtain ⟨ez, ee⟩ := I.injective cp' cp
  subst z' E'
  exact I.unique cq (cf'.unique_l I hE cf ▸ cr)

theorem td_query_exists_l (hZF : M.Models ZF) {ω n m U D P p : M.Domain}
    (sub : M.MemberSubset n m) (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω m U P) (hp : M.mem p D) :
    ∃ q, M.mem q P ∧ Td_query_d I n m p q := by
  obtain ⟨N, E, names, seq, prod⟩ := small
  obtain ⟨N', E', names', seq', prod'⟩ := large
  obtain ⟨z, hz, f, hf, cp⟩ := (prod p).mp hp
  obtain ⟨b, hb, ff⟩ := (seq f).mp hf
  obtain ⟨g, cg, fg⟩ := td_column_exists_l I hZF sub names names' ff
  obtain ⟨q, cq⟩ := I.total z g
  exact ⟨q, (prod' q).mpr ⟨z, hz, g, (seq' g).mpr ⟨b, hb, fg⟩, cq⟩, z, f, g, cp, cq, cg⟩

def Td_project_d (n m D t u : M.Domain) : Prop :=
  ∀ p, M.mem p u ↔ M.mem p D ∧ ∃ q, Td_query_d I n m p q ∧ M.mem q t

def td_project_m {d} (n m D t u : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜u⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ (∃ q, ⌜td_query_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, p, q) ∧ q ∈ ⌜t⌝ₛ)⟫
derive_free_closed td_project_m

theorem td_project_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m D t u : Term d) :
    Formula.satisfies ρ (td_project_m n m D t u) ↔
      Td_project_d I (n.eval ρ) (m.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [td_project_m, Td_project_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    td_query_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem td_project_exists_l (hZF : M.Models ZF) (n m D t : M.Domain) : ∃ u, Td_project_d I n m D t u := by
  let φ : UnarySchema 3 := {
    body := set[4] ⟪∃ q, ⌜td_query_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ, ⌜(.bound 2 : Term 4)⌝ₛ,
      ⌜(.newest : Term 4)⌝ₛ, q) ∧ q ∈ ⌜(.bound 1 : Term 4)⌝ₛ⟫ }
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases m (fun _ => n)), fun _ => n⟩
  obtain ⟨u, sep⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨u, fun p => (sep p).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    td_query_sat_l I hZF.1, Formula.satisfies_mem_iff]
  rfl

theorem Td_project_d.unique_l (hE : Extensional M) {n m D t u v : M.Domain}
    (h : Td_project_d I n m D t u) (k : Td_project_d I n m D t v) : u = v :=
  hE.eq_of_same_members u v (fun p => (h p).trans (k p).symm)

def Td_dcp_d (n m D t u : M.Domain) : Prop := M.SuccessorOf m n ∧ Td_project_d I n m D t u

def td_dcp_m {d} (n m D t u : Term d) : Formula 1 d :=
  .conj (Formula.isSuccessor m n) (td_project_m n m D t u)
derive_free_closed td_dcp_m

theorem td_dcp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m D t u : Term d) :
    Formula.satisfies ρ (td_dcp_m n m D t u) ↔
      Td_dcp_d I (n.eval ρ) (m.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  simp only [td_dcp_m, Td_dcp_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, td_project_sat_l I hE]

theorem Td_dcp_d.unique_l (hE : Extensional M) {n m D t u v : M.Domain}
    (h : Td_dcp_d I n m D t u) (k : Td_dcp_d I n m D t v) : u = v := h.2.unique_l I hE k.2

end YesMetaZFC.SetTheory.Internal
