import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax

/-! # 原关系迭代树共同核心的一阶编码

同一个活动边公式保存所属扩展器、原测度、完整支撑系统及实际前驱。
树序、节点、嵌入、操作和极限均按原图读取；源闭包不属于共同核心。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def it_tree_core_m {d} (ω c α T Q G E : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ z, ⌜Formula.isEmpty⌝ₚ(z) → ⌜rd_entry0_m⌝ₚ(z, ⌜c⌝ₛ, ⌜Q⌝ₛ)) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜E⌝ₛ) ∧
  (∀ i, (∃ p, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ)) ↔ ∃ j, j ∈ ⌜α⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(j, i)) ∧
  (∀ i j, j ∈ ⌜α⌝ₛ → ⌜KP.succ0_m⌝ₚ(j, i) → ∃ k a b c' f p,
    ⌜it_pred_m⌝ₚ(⌜T⌝ₛ, k, j) ∧ ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(k, b, ⌜Q⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(j, c', ⌜Q⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, k, j, f) ∧ ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) ∧
    ((⌜Formula.isEmpty⌝ₚ(p) ∧ k = i ∧ c' = a ∧ (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, f) → x = y)) ∨
      ⌜it_active_m⌝ₚ(⌜ω⌝ₛ, a, b, c', f, p))) ∧
  (∀ δ, δ ∈ ⌜α⌝ₛ → ⌜Formula.isLimitOrdinal⌝ₚ(δ) → ∀ a X R, ⌜rd_entry0_m⌝ₚ(δ, a, ⌜Q⌝ₛ) →
    ⌜kpair0_m⌝ₚ(a, X, R) → ∀ y ∈ X, ∃ i, i ∈ δ ∧ ⌜rd_entry0_m⌝ₚ(i, δ, ⌜T⌝ₛ) ∧
      (∃ f, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, δ, f) ∧ (∃ x, ⌜rd_entry0_m⌝ₚ(x, y, f))))⟫
derive_free_closed it_tree_core_m

theorem it_tree_core_sat_l {d} (η : Env M d) (ω c α T Q G E : Term d) :
    Formula.satisfies η (it_tree_core_m ω c α T Q G E) ↔
      It_tree_core_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) := by
  simp only [it_tree_core_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, it_diagram_sat_l hZF,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_disj_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isFunction_iff I hZF.1,
    KP.succ0_sat_l hZF.1, it_pred_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    it_map_sat_l hZF.1, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hw, diagram, root, fn, dom, steps, limits⟩
    refine ⟨hw, diagram, root, fn, dom, ?_, limits⟩
    intro i j hj hs
    obtain ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step⟩ := steps i j hj hs
    have active := it_active_sat_l hZF ((((((((η.push i).push j).push k).push a).push b).push c').push f).push p)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push] at active
    exact ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step.imp id active.mp⟩
  · intro tree
    refine ⟨tree.omega, tree.diagram, tree.root, tree.move_function, tree.move_domain, ?_, tree.limits⟩
    intro i j hj hs
    obtain ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step⟩ := tree.steps i j hj hs
    have active := it_active_sat_l hZF ((((((((η.push i).push j).push k).push a).push b).push c').push f).push p)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push] at active
    exact ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step.imp id active.mpr⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 带真实源证书的原迭代树及其后继保持编码

树的共同核心只在 IterationTreeCoreSyntax 定义和解码一次。
完整树在同一核心上附加实际源证书；延伸公式仍精确保存所有旧图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def it_tree_sources_m {d} (ω Q : Term d) : Formula 1 d := set[d] ⟪
  ∀ i a, ⌜rd_entry0_m⌝ₚ(i,a,⌜Q⌝ₛ) → ⌜it_source_m⌝ₚ(⌜ω⌝ₛ,a)⟫
derive_free_closed it_tree_sources_m

theorem it_tree_sources_sat_l {d} (η : Env M d) (ω Q : Term d) :
    Formula.satisfies η (it_tree_sources_m ω Q) ↔
      ∀ i c, Rd_entry_d i c (Q.eval η) → It_source_d hZF (ω.eval η) c := by
  simp only [it_tree_sources_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    rd_entry0_sat_l hZF.1,it_source_sat_l hZF,Definitional.Term.eval_weaken]
  rfl

def it_tree_m {d} (ω c α T Q G E : Term d) : Formula 1 d :=
  .conj (it_tree_core_m ω c α T Q G E) (it_tree_sources_m ω Q)
derive_free_closed it_tree_m

theorem it_tree_sat_l {d} (η : Env M d) (ω c α T Q G E : Term d) :
    Formula.satisfies η (it_tree_m ω c α T Q G E) ↔
      It_tree_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) := by
  simp only [it_tree_m,Formula.satisfies_conj_iff,it_tree_core_sat_l hZF,it_tree_sources_sat_l hZF]
  exact ⟨fun ⟨core,sources⟩ => ⟨core,sources⟩,fun tree => ⟨tree.toIt_tree_core_d,tree.sources⟩⟩

def it_extension_m {d} (α ξ k T Q G E β U Q' G' E' : Term d) : Formula 1 d := set[d] ⟪
  ⌜KP.succ0_m⌝ₚ(⌜β⌝ₛ, ⌜α⌝ₛ) ∧
  (∀ i l, ⌜rd_entry0_m⌝ₚ(i, l, ⌜U⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i, l, ⌜T⌝ₛ) ∨
    l = ⌜α⌝ₛ ∧ (i = ⌜α⌝ₛ ∨ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ))) ∧
  (∀ i a, ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q'⌝ₛ)) ∧
  (∀ i l f, l ∈ ⌜α⌝ₛ → (⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, l, f) ↔ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, l, f))) ∧
  (∀ i a, ⌜rd_entry0_m⌝ₚ(i, a, ⌜E⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, a, ⌜E'⌝ₛ)) ∧
  (∀ i a, ¬ i = ⌜ξ⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, a, ⌜E'⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i, a, ⌜E⌝ₛ)))⟫
derive_free_closed it_extension_m

theorem it_extension_sat_l (hE : Extensional M) {d} (η : Env M d) (α ξ k T Q G E β U Q' G' E' : Term d) :
    Formula.satisfies η (it_extension_m α ξ k T Q G E β U Q' G' E') ↔
      It_extension_d (α.eval η) (ξ.eval η) (k.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η)
        (β.eval η) (U.eval η) (Q'.eval η) (G'.eval η) (E'.eval η) := by
  simp only [it_extension_m, It_extension_d, Formula.satisfies_conj_iff, KP.succ0_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
    rd_entry0_sat_l hE, it_map_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
