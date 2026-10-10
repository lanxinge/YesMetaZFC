import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedEvaluation
import YesMetaZFC.SetTheory.Notation

/-! # 有界节点中的常值代表

常值测试只量化所属源内的支撑、定义域和函数，以及已有节点和求值图。
它是原 Δ₀ 公式；任意传递外层都可准确读取这些有限数据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_const_d (X B A e x y : M.Domain) : Prop := ∃ u, M.mem u A ∧
  ∃ a, M.mem a X ∧ ∃ f, M.mem f X ∧ ∃ D, M.mem D X ∧
    KPair_d M u a f ∧ Fn0_d D B f ∧ Rs_const_d D x f ∧ Rd_entry_d u y e

def eb_const_m {d} (X B A e x y : Term d) : Formula 1 d := set[d] ⟪
  ∃ u ∈ ⌜A⌝ₛ, ∃ a ∈ ⌜X⌝ₛ, ∃ f ∈ ⌜X⌝ₛ, ∃ D ∈ ⌜X⌝ₛ,
    ⌜kpair0_m⌝ₚ(u, a, f) ∧ ⌜fn0_m⌝ₚ(D, ⌜B⌝ₛ, f) ∧
    ⌜rs_const_m⌝ₚ(D, ⌜x⌝ₛ, f) ∧ ⌜rd_entry0_m⌝ₚ(u, ⌜y⌝ₛ, ⌜e⌝ₛ)⟫
derive_free_closed eb_const_m

theorem eb_const_delta_l {d} (X B A e x y : Term d) : (eb_const_m X B A e x y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))

theorem eb_const_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X B A e x y : Term d) :
    Formula.satisfies ρ (eb_const_m X B A e x y) ↔
      Eb_const_d (X.eval ρ) (B.eval ρ) (A.eval ρ) (e.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [eb_const_m, Eb_const_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, fn0_sat_l hE, rs_const_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
