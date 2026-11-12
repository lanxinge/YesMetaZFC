import YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # nice 树的强度与支撑列编码

一般原关系树编码由 IterationTreeSyntax 提供；本层记录 nice 条件及其
现有支撑列。每个条件继续读取原扩展器，不把填充步作为活动扩展器。
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
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (F.eval η) := by
  have read K H (sk : Fseq_space_d I (ω.eval η) (κ.eval η) K) (sl : Fseq_space_d I (ω.eval η) (L.eval η) H) :
      Formula.satisfies ((η.push K).push H) (ex_strength0_m ω.weaken.weaken κ.weaken.weaken L.weaken.weaken
        X.weaken.weaken F.weaken.weaken (.bound 1) (.bound 0)) ↔
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (F.eval η) := by
    simpa only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push, Term.eval_bound_six_push] using
      (ex_strength0_sat_l (ZF.modelsKP hZF) ((η.push K).push H) ω.weaken.weaken κ.weaken.weaken L.weaken.weaken
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

/-- 所属模型的不可达性通过同一原关系读取，避免从节点条件推断传递性。 -/
def it_inaccessible_m {d} (ω X R κ : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (sc_inaccessible_m (.bound 1) (.newest : Term 2)) X R
    (Fin.cases κ (fun _ => ω))

@[simp] theorem it_inaccessible_closed_l {d} (ω X R κ : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hr : R.freeSupport = []) (hk : κ.freeSupport = []) :
    (it_inaccessible_m ω X R κ).FreeClosed :=
  rr_truth_closed_l _ (sc_inaccessible_m_freeClosed _ _ rfl rfl) X R _ hx hr (Fin.cases hk (fun _ => hw))

private theorem it_inaccessible_sat_l (J : kpair_convention_l.Interpretation M) {c d}
    (ρ : Env M d) (ω X R κ : Term d) (model : Smem_d J c (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (it_inaccessible_m ω X R κ) ↔ Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) := by
  let φ := sc_inaccessible_m (.bound 1) (.newest : Term 2)
  have closed : φ.FreeClosed := sc_inaccessible_m_freeClosed _ _ rfl rfl
  rw [it_inaccessible_m, rr_truth_sat_l J ρ _ closed]
  constructor
  · rintro ⟨bounds, valid⟩
    refine ⟨bounds 1, bounds 0, ?_⟩
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, bounds 1⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 2 :=
      ⟨Fin.cases ⟨κ.eval ρ, bounds 0⟩ (fun _ => ⟨ω.eval ρ, bounds 1⟩), fun _ => ⟨ω.eval ρ, bounds 1⟩⟩
    apply (smem_formula_l J model nx φ η).mpr
    exact (Formula.closed_env_l φ closed
      (funext (Fin.cases (Subtype.ext rfl) (fun _ => Subtype.ext rfl)))).mp valid
  · rintro ⟨hw, hk, valid⟩
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, hw⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 2 :=
      ⟨Fin.cases ⟨κ.eval ρ, hk⟩ (fun _ => ⟨ω.eval ρ, hw⟩), fun _ => ⟨ω.eval ρ, hw⟩⟩
    refine ⟨Fin.cases hk (fun _ => hw), ?_⟩
    exact (Formula.closed_env_l φ closed
      (funext (Fin.cases (Subtype.ext rfl) (fun _ => Subtype.ext rfl)))).mp
        ((smem_formula_l J model nx φ η).mp valid)

def it_pnice_m {d} (ω c α T Q G E L : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜L⌝ₛ) ∧
  (∀ i ρ, ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) ↔ ∃ p κ F, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p, κ, ρ, F)) ∧
  (∀ i p κ ρ F, ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p, κ, ρ, F) →
    ∃ a X R, ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(a, X, R) ∧
      ⌜Formula.isTransitive⌝ₚ(X) ∧ ⌜it_strength_m⌝ₚ(⌜ω⌝ₛ, κ, ρ, X, F) ∧ ⌜it_inaccessible_m⌝ₚ(⌜ω⌝ₛ, X, R, ρ)) ∧
  (∀ i j ρ φ, ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, φ, ⌜L⌝ₛ) → i ∈ j → ρ ∈ φ)⟫
derive_free_closed it_pnice_m

theorem it_pnice_sat_l {d} (η : Env M d) (ω c α T Q G E L : Term d) :
    Formula.satisfies η (it_pnice_m ω c α T Q G E L) ↔
      It_pnice_d hZF (ω.eval η) (c.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) := by
  simp only [it_pnice_m, Formula.satisfies_conj_iff, it_tree_sat_l hZF, Formula.satisfies_isFunction_iff I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isTransitive_iff, rd_entry0_sat_l hZF.1, it_payload_sat_l hZF.1, smem_sat_l I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨tree, fn, levels, exactness, increasing⟩
    refine ⟨tree, fn, levels, ?_, increasing⟩
    intro i p κ ρ F hp pay
    obtain ⟨a, X, R, ha, mx, trans, strength, card⟩ := exactness i p κ ρ F hp pay
    have strong := it_strength_sat_l hZF ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 1) (.bound 3)
        (by simpa only [Definitional.Term.eval_weaken] using tree.omega)
    have inaccessible := it_inaccessible_sat_l I ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest (.bound 4) mx
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push] at strong inaccessible
    exact ⟨a, X, R, ha, mx, trans, strong.mp strength, inaccessible.mp card⟩
  · intro nice
    refine ⟨nice.tree, nice.function, nice.levels, ?_, nice.increasing⟩
    intro i p κ ρ F hp pay
    obtain ⟨a, X, R, ha, mx, trans, strength, card⟩ := nice.exactness i p κ ρ F hp pay
    have strong := it_strength_sat_l hZF ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 1) (.bound 3)
        (by simpa only [Definitional.Term.eval_weaken] using nice.tree.omega)
    have inaccessible := it_inaccessible_sat_l I ((((((((η.push i).push p).push κ).push ρ).push F).push a).push X).push R)
        ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest (.bound 4) mx
    simp only [Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push, Term.eval_bound_four_push, Term.eval_bound_five_push] at strong inaccessible
    exact ⟨a, X, R, ha, mx, trans, strong.mpr strength, inaccessible.mpr card⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一工作扩展器的所属模型、不可达支撑及最大强度 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_quality_d (ω κ L F u U : M.Domain) : Prop := ∃ R,
  M.IsOmega ω ∧ M.TransitiveSet U ∧ Smem_d I u U R ∧ It_local_d I ω U R κ L F ∧
    Ex_strength_d I ω κ L U F ∧ Sc_inaccessible_d ω U L

def ic_quality_m {d} (ω κ L F u U : Term d) : Formula 1 d := set[d] ⟪∃ R,
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isTransitive⌝ₚ(⌜U⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜u⌝ₛ, ⌜U⌝ₛ, R) ∧
  ⌜it_local_m⌝ₚ(⌜ω⌝ₛ, ⌜U⌝ₛ, R, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ) ∧
  ⌜it_strength_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜U⌝ₛ, ⌜F⌝ₛ) ∧ ⌜ex_inaccessible_m⌝ₚ(⌜ω⌝ₛ, ⌜U⌝ₛ, ⌜L⌝ₛ)⟫
derive_free_closed ic_quality_m

theorem ic_quality_sat_l {d} (η : Env M d) (ω κ L F u U : Term d) :
    Formula.satisfies η (ic_quality_m ω κ L F u U) ↔
      Ic_quality_d hZF (ω.eval η) (κ.eval η) (L.eval η) (F.eval η) (u.eval η) (U.eval η) := by
  simp only [ic_quality_m, Ic_quality_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_isTransitive_iff, smem_sat_l I,
    it_local_sat_l I, Definitional.Term.eval_weaken]
  apply exists_congr
  intro R
  have strong (hw : M.IsOmega (ω.eval η)) := it_strength_sat_l hZF (η.push R)
    ω.weaken κ.weaken L.weaken U.weaken F.weaken (by simpa only [Definitional.Term.eval_weaken] using hw)
  have inaccessible (ht : M.TransitiveSet (U.eval η)) := ex_inaccessible_sat_l (η.push R)
    ω.weaken U.weaken L.weaken (by simpa only [Definitional.Term.eval_weaken] using ht)
  simp only [Definitional.Term.eval_weaken] at strong inaccessible
  constructor
  · rintro ⟨hw, ht, code, loc, strength, card⟩
    exact ⟨hw, ht, code, loc, (strong hw).mp strength, (inaccessible ht).mp card⟩
  · rintro ⟨hw, ht, code, loc, strength, card⟩
    exact ⟨hw, ht, code, loc, (strong hw).mpr strength, (inaccessible ht).mpr card⟩

end YesMetaZFC.SetTheory.LargeCardinal
