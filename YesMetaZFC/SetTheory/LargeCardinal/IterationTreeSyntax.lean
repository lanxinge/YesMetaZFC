import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderQuality
import YesMetaZFC.SetTheory.LargeCardinal.IterationNice

/-! # 含真实 padding 的整棵迭代树的一阶公式

直接编码原树、原超幂和原最大强度。有限列空间由背景集合论构造，语义
等价不要求工作模型满足额外公理，也不把 padding 当作活动扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def it_strength_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪∃ K H,
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, K) ∧
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, H) ∧
  ⌜ex_strength0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ, K, H)⟫
derive_free_closed it_strength_m

theorem it_strength_sat_l {d} (η : Env M d) (ω κ L X F : Term d) (hω : M.IsOmega (ω.eval η)) :
    Formula.satisfies η (it_strength_m ω κ L X F) ↔
      Ex_strength_d hZF (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (F.eval η) := by
  have read K H (sk : Fseq_space_d I (ω.eval η) (κ.eval η) K) (sl : Fseq_space_d I (ω.eval η) (L.eval η) H) :
      Formula.satisfies ((η.push K).push H) (ex_strength0_m ω.weaken.weaken κ.weaken.weaken L.weaken.weaken
        X.weaken.weaken F.weaken.weaken (.bound 1) (.bound 0)) ↔
      Ex_strength_d hZF (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (F.eval η) := by
    simpa only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push, Term.eval_bound_six_push] using
      (ex_strength0_sat_l hZF ((η.push K).push H) ω.weaken.weaken κ.weaken.weaken L.weaken.weaken
        X.weaken.weaken F.weaken.weaken (.bound 1) (.bound 0)
        (by simpa only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push, Term.eval_bound_six_push] using sk)
        (by simpa only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push, Term.eval_bound_six_push] using sl))
  simp only [it_strength_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_space_sat_l I hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨K, H, sk, sl, valid⟩
    exact (read K H sk sl).mp valid
  · intro strength
    obtain ⟨K, sk⟩ := ZF.fseq_space_exists_l I hZF hω (κ.eval η)
    obtain ⟨H, sl⟩ := ZF.fseq_space_exists_l I hZF hω (L.eval η)
    exact ⟨K, H, sk, sl, (read K H sk sl).mpr strength⟩

def it_active_m {d} (ω c a b j p : Term d) : Formula 1 d := set[d] ⟪∃ κ L F X R Y S,
  ⌜it_payload_m⌝ₚ(⌜p⌝ₛ, κ, L, F) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, Y, S) ∧ ⌜ex_local_m⌝ₚ(⌜ω⌝ₛ, κ, L, X, F) ∧
  ⌜ea_agree_m⌝ₚ(⌜ω⌝ₛ, κ, X, Y) ∧ ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, κ, L, F, ⌜a⌝ₛ, ⌜b⌝ₛ, ⌜j⌝ₛ)⟫
derive_free_closed it_active_m

theorem it_active_sat_l {d} (η : Env M d) (ω c a b j p : Term d)
    (trans : ∀ X R, Smem_d I (c.eval η) X R → M.TransitiveSet X) :
    Formula.satisfies η (it_active_m ω c a b j p) ↔
      It_active_d hZF (ω.eval η) (c.eval η) (a.eval η) (b.eval η) (j.eval η) (p.eval η) := by
  have read κ L F X R Y S (model : Smem_d I (c.eval η) X R) := ex_local_sat_l
    (((((((η.push κ).push L).push F).push X).push R).push Y).push S)
    ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 3) (.bound 4) (trans X R model)
  simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push, Term.eval_bound_six_push] at read
  simp only [it_active_m, It_active_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_payload_sat_l hZF.1, smem_sat_l I, ea_agree_sat_l hZF.1, it_ultra_sat_l hZF, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨κ, L, F, X, R, Y, S, pay, model, target, loc, agree, ultra⟩
    exact ⟨κ, L, F, X, R, Y, S, pay, model, target,
      (read κ L F X R Y S model).mp loc, agree, ultra⟩
  · rintro ⟨κ, L, F, X, R, Y, S, pay, model, target, loc, agree, ultra⟩
    exact ⟨κ, L, F, X, R, Y, S, pay, model, target,
      (read κ L F X R Y S model).mpr loc, agree, ultra⟩

def it_tree_m {d} (ω c α T Q G E : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ z, ⌜Formula.isEmpty⌝ₚ(z) → ⌜rd_entry0_m⌝ₚ(z, ⌜c⌝ₛ, ⌜Q⌝ₛ)) ∧
  (∀ i a, ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) → ⌜it_source_m⌝ₚ(⌜ω⌝ₛ, a)) ∧
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
derive_free_closed it_tree_m

theorem it_tree_sat_l {d} (η : Env M d) (ω c α T Q G E : Term d) :
    Formula.satisfies η (it_tree_m ω c α T Q G E) ↔
      It_tree_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) := by
  simp only [it_tree_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, it_diagram_sat_l hZF,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_disj_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isFunction_iff I hZF.1,
    it_source_sat_l hZF, KP.succ0_sat_l hZF.1, it_pred_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    it_map_sat_l hZF.1, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hw, diagram, root, sources, fn, dom, steps, limits⟩
    refine ⟨hw, diagram, root, sources, fn, dom, ?_, limits⟩
    intro i j hj hs
    obtain ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step⟩ := steps i j hj hs
    have active := it_active_sat_l hZF ((((((((η.push i).push j).push k).push a).push b).push c').push f).push p)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
        (by
          intro X R mx
          obtain ⟨Y, S, _, my, sy⟩ := sources i a ha
          obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 mx.1
          exact sy.transitive)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push] at active
    exact ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step.imp id active.mp⟩
  · intro tree
    refine ⟨tree.omega, tree.diagram, tree.root, tree.sources, tree.move_function, tree.move_domain, ?_, tree.limits⟩
    intro i j hj hs
    obtain ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step⟩ := tree.steps i j hj hs
    have active := it_active_sat_l hZF ((((((((η.push i).push j).push k).push a).push b).push c').push f).push p)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
        (by
          intro X R mx
          obtain ⟨Y, S, _, my, sy⟩ := tree.sources i a ha
          obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 mx.1
          exact sy.transitive)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push] at active
    exact ⟨k, a, b, c', f, p, pred, ha, hb, hc, edge, move, step.imp id active.mpr⟩

def it_pnice_m {d} (ω c α T Q G E L : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜L⌝ₛ) ∧
  (∀ i ρ, ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) ↔ ∃ p κ F, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p, κ, ρ, F)) ∧
  (∀ i p κ ρ F a X R, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p, κ, ρ, F) →
    ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(a, X, R) →
    ⌜it_strength_m⌝ₚ(⌜ω⌝ₛ, κ, ρ, X, F) ∧ ⌜ex_inaccessible_m⌝ₚ(⌜ω⌝ₛ, X, ρ)) ∧
  (∀ i j ρ φ, ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, φ, ⌜L⌝ₛ) → i ∈ j → ρ ∈ φ)⟫
derive_free_closed it_pnice_m

theorem it_pnice_sat_l {d} (η : Env M d) (ω c α T Q G E L : Term d) :
    Formula.satisfies η (it_pnice_m ω c α T Q G E L) ↔
      It_pnice_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) := by
  simp only [it_pnice_m, Formula.satisfies_conj_iff, it_tree_sat_l hZF, Formula.satisfies_isFunction_iff I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1, it_payload_sat_l hZF.1, smem_sat_l I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  have trans (tree : It_tree_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η))
      i a X R (ha : Rd_entry_d i a (Q.eval η)) (mx : Smem_d I a X R) : M.TransitiveSet X := by
    obtain ⟨Y, S, _, my, sy⟩ := tree.sources i a ha
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 mx.1
    exact sy.transitive
  constructor
  · rintro ⟨tree, fn, levels, exactness, increasing⟩
    refine ⟨tree, fn, levels, ?_, increasing⟩
    intro i p κ ρ F a X R hp pay ha mx
    obtain ⟨strength, card⟩ := exactness i p κ ρ F a X R hp pay ha mx
    have strong := it_strength_sat_l hZF ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 1) (.bound 3)
        (by simpa only [Definitional.Term.eval_weaken] using tree.omega)
    have inaccessible := ex_inaccessible_sat_l ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 4) (trans tree i a X R ha mx)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push] at strong inaccessible
    exact ⟨strong.mp strength, inaccessible.mp card⟩
  · intro nice
    refine ⟨nice.tree, nice.function, nice.levels, ?_, nice.increasing⟩
    intro i p κ ρ F a X R hp pay ha mx
    obtain ⟨strength, card⟩ := nice.exactness i p κ ρ F a X R hp pay ha mx
    have strong := it_strength_sat_l hZF ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 1) (.bound 3)
        (by simpa only [Definitional.Term.eval_weaken] using nice.tree.omega)
    have inaccessible := ex_inaccessible_sat_l ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 4) (trans nice.tree i a X R ha mx)
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push] at strong inaccessible
    exact ⟨strong.mpr strength, inaccessible.mpr card⟩

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
