import YesMetaZFC.Model.SetTheory.Internal.SourceBranch
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.SetTheory.Notation

/-! # 源对背景内部 ω 序列的闭性

这里量化背景的实际函数图。有界值域闭性在每个包含 ω 的极限秩层中成立，
足以回收已有下降枝；共尾度大于 ω 的秩层进一步对全部 ω 序列封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_omega_closed_d (ω X : M.Domain) : Prop := ∀ f, Fn0_d ω X f → M.mem f X

def Sc_bounded_omega_closed_d (ω X : M.Domain) : Prop :=
  ∀ A, M.mem A X → ∀ f, Fn0_d ω A f → M.mem f X

def sc_omega_closed_m {d} (ω X : Term d) : Formula 1 d := set[d] ⟪
  ∀ f, ⌜fn0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, f) → f ∈ ⌜X⌝ₛ⟫
derive_free_closed sc_omega_closed_m

theorem sc_omega_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X : Term d) :
    Formula.satisfies ρ (sc_omega_closed_m ω X) ↔ Sc_omega_closed_d (ω.eval ρ) (X.eval ρ) := by
  simp only [sc_omega_closed_m, Sc_omega_closed_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def sc_bounded_omega_closed_m {d} (ω X : Term d) : Formula 1 d := set[d] ⟪
  ∀ A ∈ ⌜X⌝ₛ, ∀ f, ⌜fn0_m⌝ₚ(⌜ω⌝ₛ, A, f) → f ∈ ⌜X⌝ₛ⟫
derive_free_closed sc_bounded_omega_closed_m

theorem sc_bounded_omega_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X : Term d) :
    Formula.satisfies ρ (sc_bounded_omega_closed_m ω X) ↔
      Sc_bounded_omega_closed_d (ω.eval ρ) (X.eval ρ) := by
  simp only [sc_bounded_omega_closed_m, Sc_bounded_omega_closed_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]; rfl

theorem Sc_omega_closed_d.bounded_l {ω X : M.Domain} (hX : M.TransitiveSet X)
    (closed : Sc_omega_closed_d ω X) : Sc_bounded_omega_closed_d ω X :=
  fun A hA f hf => closed f (hf.mono_target_l (hX A hA))

theorem Sc_bounded_omega_closed_d.branch_l {ω X : M.Domain}
    (closed : Sc_bounded_omega_closed_d ω X) : Sc_branch_d ω X :=
  fun A _ hA _ ⟨f, hf, desc⟩ => ⟨f, closed A hA f hf, hf, desc⟩

theorem Sc_bounded_omega_closed_d.rank_l (hZF : M.Models ZF) {ω X α V : M.Domain}
    (hX : M.TransitiveSet X) (hV : M.mem V X) (rank : Vr_d X α V)
    (hα : M.IsLimitOrdinal α) (hw : M.mem ω V) (closed : Sc_bounded_omega_closed_d ω X) :
    Sc_bounded_omega_closed_d ω V := by
  intro A hA f hf
  exact rank.relation_mem_l hZF hX hV hα hw hA (closed A (hX V hV A hA) f hf) hf.1

/-- 每个包含定义域的极限秩层都对有界值域序列封闭。 -/
theorem sc_v_bounded_omega_closed_l (hZF : M.Models ZF) {ω δ V : M.Domain}
    (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) (hw : M.mem ω V) :
    Sc_bounded_omega_closed_d ω V := by
  intro A hA f hf
  obtain ⟨B, hB, wb, ab⟩ := ZF.v_joint_bound_l _ hZF hV hw hA
  exact ZF.v_relation_mem_l _ hZF hV hδ hB (fun p hp => by
    obtain ⟨x, hx, y, hy, pair⟩ := hf.1 p hp
    exact ⟨x, wb x hx, y, ab y hy, pair⟩)

theorem sc_v_omega_closed_l (hZF : M.Models ZF) {ω δ ν V : M.Domain}
    (cf : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) ν δ) (hw : M.mem ω ν)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) (hωV : M.mem ω V) : Sc_omega_closed_d ω V := by
  obtain ⟨i, hi⟩ := ZF.exists_identityBijection hZF (kp_pair_l (ZF.modelsKP hZF)) ω
  intro f hf
  obtain ⟨_, _, _, h⟩ := ZF.v_small_function_l hZF cf hw ⟨i, hi.1⟩ hωV hV (fn0_function_l (ZF.modelsKP hZF) hf)
  exact h

end YesMetaZFC.SetTheory.Internal
