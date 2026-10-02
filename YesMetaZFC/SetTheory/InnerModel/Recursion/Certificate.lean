import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.Transitive
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # Σ₁ 算子的内部成员递归证书

证书载体是传递集合 A。所有值、函数图和前段限制有同一个传递界 T，
因此证书检查是 Δ₀，存在一个证书的值关系是实际 Σ₁ 正规形。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure Rc_cert_d {n} (φ : S1_binary n) (ρ : Env M n) (A F T : M.Domain) : Prop where
  trans : M.TransitiveSet T
  domain : M.mem A T
  graph : M.mem F T
  hereditary : M.TransitiveSet A
  function : Fn0_d A T F
  step : ∀ a, M.mem a A → ∃ R, M.mem R T ∧ Res0_d R F a T ∧
    ∀ y, M.mem y T → Rd_entry_d a y F → ∃ w, M.mem w T ∧ φ.matrix_binary.toBinarySchema.denote (ρ.push R) y w

def rc_cert_m {n d} (φ : S1_binary n) (e : Fin n → Term d) (A F T : Term d) : Formula 1 d :=
  .conj (Formula.isTransitive T) (.conj (.mem A T) (.conj (.mem F T)
    (.conj (Formula.isTransitive A) (.conj (fn0_m A T F)
      (Formula.forallMem A (Formula.existsMem T.weaken
        (.conj (res0_m .newest F.weaken.weaken (.bound 1) T.weaken.weaken)
          (Formula.forallMem T.weaken.weaken (.imp (rd_entry0_m (.bound 2) .newest F.weaken.weaken.weaken)
            (Formula.existsMem T.weaken.weaken.weaken
              (φ.matrix_m (fun i => (e i).weaken.weaken.weaken.weaken) (.bound 2) (.bound 1) .newest)))))))))))

@[simp] theorem rc_cert_closed_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (A F T : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hA : A.freeSupport = []) (hF : F.freeSupport = []) (hT : T.freeSupport = []) :
    (rc_cert_m φ e A F T).FreeClosed := by
  simp -implicitDefEqProofs [rc_cert_m, Definitional.Formula.FreeClosed, he, hA, hF, hT]

theorem rc_cert_delta_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (A F T : Term d) :
    (rc_cert_m φ e A F T).IsDelta0 := by
  refine .conj (.forallMem _ (.forallMem _ (.mem _ _))) (.conj (.mem _ _) (.conj (.mem _ _)
    (.conj (.forallMem _ (.forallMem _ (.mem _ _))) (.conj (fn0_delta_l ..)
      (.forallMem _ (.existsMem _ (.conj (res0_delta_l ..) (.forallMem _ (.imp (rd_entry0_delta_l ..) (.existsMem _ ?_))))))))))
  exact φ.matrix.delta0.bind_l _

theorem rc_cert_sat_l (hE : Extensional M) {n d} (φ : S1_binary n) (η : Env M d)
    (e : Fin n → Term d) (A F T : Term d) :
    Formula.satisfies η (rc_cert_m φ e A F T) ↔
      Rc_cert_d φ ⟨fun i => (e i).eval η, η.free⟩ (A.eval η) (F.eval η) (T.eval η) := by
  simp only [rc_cert_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, res0_sat_l hE, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, S1_binary.matrix_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.trans, h.domain, h.graph, h.hereditary, h.function, h.step⟩⟩

def Rc_value_d {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) : Prop :=
  ∃ T A F, Rc_cert_d φ ρ A F T ∧ M.mem x A ∧ Rd_entry_d x y F

def rc_value_s {n} (φ : S1_binary n) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (rc_cert_m φ (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) .newest (.bound 2))
        (.conj (.mem (.bound 4) (.bound 1)) (rd_entry0_m (.bound 4) (.bound 3) .newest))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (rc_cert_delta_l ..) (.conj (.mem _ _) (rd_entry0_delta_l ..)))) }

theorem rc_matrix_sat_l (hE : Extensional M) {n} (φ : S1_binary n) (ρ : Env M n) (x y T : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push T) (rc_value_s φ).matrix.body ↔
      ∃ A F, Rc_cert_d φ ρ A F T ∧ M.mem x A ∧ Rd_entry_d x y F := by
  simp only [rc_value_s,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rc_cert_sat_l hE, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE]
  change (∃ A, M.mem A T ∧ ∃ F, M.mem F T ∧ Rc_cert_d φ ρ A F T ∧ M.mem x A ∧ Rd_entry_d x y F) ↔ _
  exact ⟨fun ⟨A, _, F, _, h, hx, hy⟩ => ⟨A, F, h, hx, hy⟩,
    fun ⟨A, F, h, hx, hy⟩ => ⟨A, h.domain, F, h.graph, h, hx, hy⟩⟩

theorem rc_value_sat_l (hE : Extensional M) {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    (rc_value_s φ).schema.denote ρ x y ↔ Rc_value_d φ ρ x y := by
  rw [S1_binary.sat_l]
  exact exists_congr (fun T => rc_matrix_sat_l hE φ ρ x y T)

/-- 同一递归证书的每个实际条目都给出 Σ₁ 值关系。 -/
theorem Rc_cert_d.value_l {n} {φ : S1_binary n} {ρ : Env M n} {A F T x y : M.Domain}
    (h : Rc_cert_d φ ρ A F T) (hy : Rd_entry_d x y F) : Rc_value_d φ ρ x y :=
  ⟨T, A, F, h, (h.function.bound_l hy).1, hy⟩

end YesMetaZFC.SetTheory.InnerModel
