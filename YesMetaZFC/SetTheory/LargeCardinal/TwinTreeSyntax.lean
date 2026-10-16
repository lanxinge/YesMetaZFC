import YesMetaZFC.SetTheory.LargeCardinal.TwinTreeDichotomy
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion

/-! # 双树论证的原一阶公式

只编码原数学前提、规范名称和原内部力迫关系，供带参数可数反射使用。
反射返回的是原地模型中的实际获胜策略存在性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def tp_win_m (b positive : Bool) {d} (ω A Y F T : Term d) : Formula 1 d :=
  let payoff {d} (ω A Y F T x : Term d) :=
    if positive then tp_projection_m ω A Y F T x else .neg (tp_projection_m ω A Y F T x)
  set[d] ⟪∃ H J B W σ,
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,H) ∧
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(B,⌜ω⌝ₛ,⌜A⌝ₛ) ∧
    (∀ n, n ∈ J ↔ n ∈ ⌜ω⌝ₛ ∧ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,n)) ∧
    (∀ x, x ∈ W ↔ x ∈ B ∧ ⌜payoff⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ,⌜T⌝ₛ,x)) ∧
    ⌜cg_win_m b⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,H,J,B,W,σ)⟫

@[simp] theorem tp_win_closed_l (b positive : Bool) {d} (ω A Y F T : Term d)
    (hw : ω.freeSupport = []) (ha : A.freeSupport = []) (hy : Y.freeSupport = [])
    (hf : F.freeSupport = []) (ht : T.freeSupport = []) : (tp_win_m b positive ω A Y F T).FreeClosed := by
  cases positive <;> simp -implicitDefEqProofs [tp_win_m, Definitional.Formula.FreeClosed, hw, ha, hy, hf, ht]

theorem tp_win_sat_l (hZF : M.Models ZF) (b positive : Bool) {d} (ρ : Env M d) (ω A Y F T : Term d) :
    Formula.satisfies ρ (tp_win_m b positive ω A Y F T) ↔
    Tp_win_d hZF b positive (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  cases positive <;> simp only [tp_win_m, Tp_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, fseq_space_sat_l I hZF.1,
    Formula.satisfies_isFunctionSpace_iff I hZF.1, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, gm_even_sat_l I hZF.1,
    tp_projection_sat_l I hZF.1, Formula.satisfies_neg_iff, cg_win_sat_l I hZF.1,
    Definitional.Term.eval_weaken] <;> rfl

def td_cover0_m : Formula 1 8 :=
  td_cover_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)

theorem td_cover0_closed_l : td_cover0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_cover0_m]

def td_checks_m {d} (p : Term d) (a t : Fin 8 → Term d) : Formula 1 d :=
  .conj (check_m p (a 0) (t 0)) (.conj (check_m p (a 1) (t 1))
  (.conj (check_m p (a 2) (t 2)) (.conj (check_m p (a 3) (t 3))
  (.conj (check_m p (a 4) (t 4)) (.conj (check_m p (a 5) (t 5))
  (.conj (check_m p (a 6) (t 6)) (check_m p (a 7) (t 7))))))))

@[simp] theorem td_checks_closed_l {d} (p : Term d) (a t : Fin 8 → Term d)
    (hp : p.freeSupport = []) (ha : ∀ i, (a i).freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) :
    (td_checks_m p a t).FreeClosed := by
  simp -implicitDefEqProofs [td_checks_m, Definitional.Formula.FreeClosed, hp, ha, ht]

theorem td_checks_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Term d) (a t : Fin 8 → Term d) :
    Formula.satisfies ρ (td_checks_m p a t) ↔ ∀ i, Check_d M (p.eval ρ) ((a i).eval ρ) ((t i).eval ρ) := by
  simp only [td_checks_m, Formula.satisfies_conj_iff, check_sat_l M hE]
  exact ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ => Fin.cases h0 (Fin.cases h1 (Fin.cases h2
    (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (fun i => by
      have eq : i = 0 := Fin.ext (by omega); exact eq ▸ h7))))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩⟩

def td_order_m {d} (C Q : Term d) : Formula 1 d := set[d] ⟪∀ p q,
  ⌜entry_m⌝ₚ(p,q,⌜Q⌝ₛ) ↔ p ∈ ⌜C⌝ₛ ∧ q ∈ ⌜C⌝ₛ ∧ q ⊆ p⟫
derive_free_closed td_order_m

theorem td_order_sat_l (hE : Extensional M) {d} (ρ : Env M d) (C Q : Term d) :
    Formula.satisfies ρ (td_order_m C Q) ↔
    ∀ p q, Entry_d M p q (Q.eval ρ) ↔ M.mem p (C.eval ρ) ∧ M.mem q (C.eval ρ) ∧ M.MemberSubset q p := by
  simp only [td_order_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, entry_sat_l M hE, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def td_parameters_m : Fin 8 → Term 24 := fun i =>
  [(.bound 0 : Term 24), .bound 2, .bound 6, .bound 7, .bound 8, .bound 10, .bound 11, .bound 12].get i

def td_names_m : Fin 8 → Term 24 := fun i => .bound ⟨i.val + 16, by omega⟩

def td_input_m : Formula 1 24 :=
  let ω := Term.bound 0; let δ := Term.bound 1; let A := Term.bound 2; let X := Term.bound 3
  let a := Term.bound 4; let Γ := Term.bound 5; let Y := Term.bound 6; let F := Term.bound 7
  let T := Term.bound 8; let Λ := Term.bound 9; let Z := Term.bound 10; let G := Term.bound 11
  let S := Term.bound 12; let C := Term.bound 13; let Q := Term.bound 14; let p := Term.bound 15
  .conj (set[24] ⟪⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜δ⌝ₛ) ∧
    ⌜v_m kpair_convention_l⌝ₚ(⌜δ⌝ₛ,⌜X⌝ₛ) ∧ ⌜A⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜a⌝ₛ ∈ ⌜A⌝ₛ ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜A⌝ₛ,⌜Γ⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧ ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜T⌝ₛ) ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Z⌝ₛ,⌜A⌝ₛ,⌜Λ⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Z⌝ₛ,⌜G⌝ₛ) ∧ ⌜tree_m⌝ₚ(⌜G⌝ₛ,⌜S⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜δ⌝ₛ,⌜C⌝ₛ) ∧ ⌜td_order_m⌝ₚ(⌜C⌝ₛ,⌜Q⌝ₛ)⟫)
    (.conj (td_checks_m p td_parameters_m td_names_m) (force_at_m td_cover0_m td_names_m C Q C p))

theorem td_input_closed_l : td_input_m.FreeClosed := by
  have hp : ∀ i, (td_parameters_m i).freeSupport = [] := by simp [td_parameters_m, Fin.forall_fin_succ]
  have hn : ∀ i, (td_names_m i).freeSupport = [] := fun _ => rfl
  simp -implicitDefEqProofs [td_input_m, Definitional.Formula.FreeClosed, hp, hn, td_cover0_closed_l]

def Td_input_d (hZF : M.Models ZF) (ρ : Env M 24) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF); let a := ρ.bound
  (M.IsOmega (a 0) ∧ Woodin_d I (a 1) ∧ V_d I (a 1) (a 3) ∧ M.mem (a 2) (a 3) ∧ M.mem (a 4) (a 2) ∧
    M.IsCartesianProduct I (a 6) (a 2) (a 5) ∧ Fseq_space_d I (a 0) (a 6) (a 7) ∧ Tree_d (a 7) (a 8) ∧
    M.IsCartesianProduct I (a 10) (a 2) (a 9) ∧ Fseq_space_d I (a 0) (a 10) (a 11) ∧ Tree_d (a 11) (a 12) ∧
    Fseq_space_d I (a 0) (a 1) (a 13) ∧
    ∀ p q, Entry_d M p q (a 14) ↔ M.mem p (a 13) ∧ M.mem q (a 13) ∧ M.MemberSubset q p) ∧
  (∀ i, Check_d M (a 15) ((td_parameters_m i).eval ρ) ((td_names_m i).eval ρ)) ∧
  Forces_d M (a 13) (a 14) (a 13) td_cover0_m ⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ (a 15)

theorem td_input_sat_l (hZF : M.Models ZF) (ρ : Env M 24) :
    Formula.satisfies ρ td_input_m ↔ Td_input_d hZF ρ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_input_m, Td_input_d, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    woodin_sat_l I hZF.1, v_sat_l I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isCartesianProduct_iff I, fseq_space_sat_l I hZF.1, tree_sat_l,
    td_order_sat_l hZF.1, td_checks_sat_l hZF.1, force_at_sat_l]; rfl

def td_output_m : Formula 1 24 := .conj
  (td_cover_m (.bound 0) (.bound 2) (.bound 6) (.bound 7) (.bound 8) (.bound 10) (.bound 11) (.bound 12))
  (.disj (tp_win_m true true (.bound 0) (.bound 2) (.bound 6) (.bound 7) (.bound 8))
    (tp_win_m false false (.bound 0) (.bound 2) (.bound 10) (.bound 11) (.bound 12)))

theorem td_output_closed_l : td_output_m.FreeClosed := by
  simp -implicitDefEqProofs [td_output_m, Definitional.Formula.FreeClosed]

theorem td_output_sat_l (hZF : M.Models ZF) (ρ : Env M 24) :
    Formula.satisfies ρ td_output_m ↔
    Td_cover_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7)
      (ρ.bound 8) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12) ∧
    (Tp_win_d hZF true true (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) ∨
      Tp_win_d hZF false false (ρ.bound 0) (ρ.bound 2) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12)) := by
  simp only [td_output_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    td_cover_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tp_win_sat_l hZF]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
