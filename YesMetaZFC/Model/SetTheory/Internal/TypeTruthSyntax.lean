import YesMetaZFC.Model.SetTheory.Internal.TypePoolBounded

/-! # 有限历史中完整类型的原公式

把已有查询域、真值集合及实现关系写回原语言，供集合内分离合法局面。
原元数和名字列仍取遍内部自然数，不用宿主有限列表代替历史。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def tt_pool_m {d} (ω n U D : Term d) : Formula 1 d := set[d] ⟪∃ N E,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, N, E) ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜D⌝ₛ, ⌜ω⌝ₛ, E)⟫
derive_free_closed tt_pool_m

theorem tt_pool_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n U D : Term d) :
    Formula.satisfies ρ (tt_pool_m ω n U D) ↔ Tt_pool_d I (ω.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) := by
  simp only [tt_pool_m, Tt_pool_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l hKP, fseq_space_sat_l I hKP.1, Formula.satisfies_isCartesianProduct_iff I,
    Definitional.Term.eval_weaken]
  rfl

def tt_truth_m {d} (ω c n s δ D t : Term d) : Formula 1 d := set[d] ⟪∀ p,
  p ∈ ⌜t⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ ⌜tt_query_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, p)⟫
derive_free_closed tt_truth_m

theorem tt_truth_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c n s δ D t : Term d) :
    Formula.satisfies ρ (tt_truth_m ω c n s δ D t) ↔
      Tt_truth_d I (ω.eval ρ) (c.eval ρ) (n.eval ρ) (s.eval ρ) (δ.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [tt_truth_m, Tt_truth_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, tt_query_sat_l I hKP, Definitional.Term.eval_weaken]
  rfl

def tt_realized0_m : Formula 1 10 :=
  let p : Fin 10 → Term 10 := Term.bound
  set[10] ⟪⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ) ∧ ⌜p 4⌝ₛ ∈ ⌜p 0⌝ₛ ∧
    ⌜fn0_m⌝ₚ(⌜p 4⌝ₛ, ⌜p 2⌝ₛ, ⌜p 5⌝ₛ) ∧ ⌜p 6⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 7⌝ₛ ⊆ ⌜p 2⌝ₛ ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 4⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ) ∧
    ⌜tt_truth_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ)⟫

theorem tt_realized0_closed_l : tt_realized0_m.FreeClosed := by
  simp -implicitDefEqProofs [tt_realized0_m, Definitional.Formula.FreeClosed]

def tt_realized_m {d} (ω c X R n s δ U D t : Term d) : Formula 1 d :=
  tt_realized0_m.bind (fun i => [ω, c, X, R, n, s, δ, U, D, t].get i)

@[simp] theorem tt_realized_closed_l {d} (ω c X R n s δ U D t : Term d)
    (hw : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hn : n.freeSupport = []) (hs : s.freeSupport = []) (hδ : δ.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (ht : t.freeSupport = []) :
    (tt_realized_m ω c X R n s δ U D t).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tt_realized0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hc, hX, hR, hn, hs, hδ, hU, hD, ht, fun i => Fin.elim0 i⟩

theorem tt_realized_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c X R n s δ U D t : Term d) :
    Formula.satisfies ρ (tt_realized_m ω c X R n s δ U D t) ↔
      Tt_realized_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (n.eval ρ) (s.eval ρ)
        (δ.eval ρ) (U.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_mem_iff, fn0_sat_l hKP.1, Formula.satisfies_subset_iff,
    tt_pool_sat_l I hKP, tt_truth_sat_l I hKP]
  exact ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
    fun h => ⟨h.model, h.finite, h.tuple, h.point, h.constants, h.pool, h.truth⟩⟩

end YesMetaZFC.SetTheory.Internal
