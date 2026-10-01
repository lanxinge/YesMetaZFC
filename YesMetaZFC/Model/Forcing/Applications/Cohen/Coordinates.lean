import YesMetaZFC.Model.Forcing.CCC.Basic
import YesMetaZFC.Model.Forcing.Internal.Functions.Generic

/-! # 参数化 Cohen 坐标的稠密要求

有限支撑总有未使用的自然数列。由此同时赋给两行相反的位，或对地模型给定集合
作逐位对角化；相关稠密集均有实际公式，允许内部自然数在外部非标准。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem fresh_rows_l (hZFC : M.Models ZFC) {ω p} (hω : M.IsOmega ω)
    (hp : Finite_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω p) (i j : M.Domain) :
    ∃ n, M.mem n ω ∧ ∀ a, (KPair_d M a i n ∨ KPair_d M a j n) → ¬ ∃ c, Entry_d M a c p := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 2 := (⟨fun _ => i, fun _ => i⟩ : Env M 1).push j
  let φ : BinarySchema 2 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.disj (kpair_m (.bound 1) (.bound 5) (.bound 3)) (kpair_m (.bound 1) (.bound 4) (.bound 3))))) }
  have hφ n s : φ.denote ρ n s ↔ ∃ a c, KPair_d M s a c ∧ (KPair_d M a i n ∨ KPair_d M a j n) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, kpair_sat_l M hZF.1]
    rfl
  obtain ⟨n, hn, hf⟩ := ZFC.finite_avoid_l I hZFC hω hp φ ρ (by
    intro n m s _ _ _ hn hm
    obtain ⟨a, c, hs, ha⟩ := (hφ n s).mp hn
    obtain ⟨a', c', hs', ha'⟩ := (hφ m s).mp hm
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hs hs'
    exact ha.elim (fun h => ha'.elim (fun k => (kpair_injective_l M h k).2)
      (fun k => (kpair_injective_l M h k).2)) (fun h => ha'.elim
        (fun k => (kpair_injective_l M h k).2) (fun k => (kpair_injective_l M h k).2)))
  refine ⟨n, hn, fun a ha ⟨c, s, hs, hsp⟩ => ?_⟩
  exact hf s hsp ((hφ n s).mpr ⟨a, c, hs, ha⟩)

theorem fn_input_l {B R ω X Y : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hZF : M.Models ZF) (hU : Generic_d M B R B U) (hω : M.IsOmega ω)
    (hB : ∀ p, M.mem p B ↔ Fn_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (hY : ∃ y, M.mem y Y) {a} (ha : M.mem a X) : ∃ p, U p ∧ ∃ y, Entry_d M a y p := by
  classical
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
  have hφ p : φ.denote ρ p ↔ ∃ y, Entry_d M a y p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
    rfl
  apply generic_pick_l hZF hU ⟨1, φ, ρ, hφ⟩ hp₀
  intro p hp
  by_cases hn : ∃ y, Entry_d M a y p
  · exact ⟨p, below_refl_l O hp.1 hp.2.1, hn⟩
  · obtain ⟨y, hy⟩ := hY
    obtain ⟨q, hq, hqp, haq⟩ := ZF.fn_insert_l _ hZF hω ((hB p).mp hp.1) ha hy hn
    exact ⟨q, subset_below_l hZF hR hp.1 ((hB q).mpr hq) hqp, y, haq⟩

def Split_d (M : SetTheory.Structure.{u}) (ω i j o l p : M.Domain) : Prop :=
  ∃ n a c, M.mem n ω ∧ KPair_d M a i n ∧ KPair_d M c j n ∧ Entry_d M a o p ∧ Entry_d M c l p

def split_m {n} (ω i j o l p : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) ω.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 1) i.weaken.weaken.weaken (.bound 2))
      (.conj (kpair_m .newest j.weaken.weaken.weaken (.bound 2))
        (.conj (entry_m (.bound 1) o.weaken.weaken.weaken p.weaken.weaken.weaken)
          (entry_m .newest l.weaken.weaken.weaken p.weaken.weaken.weaken)))))))
derive_free_closed split_m

theorem split_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω i j o l p : Term n) :
    Formula.satisfies ρ (split_m ω i j o l p) ↔
      Split_d M (ω.eval ρ) (i.eval ρ) (j.eval ρ) (o.eval ρ) (l.eval ρ) (p.eval ρ) := by
  simp only [split_m, Split_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, kpair_sat_l M hE, entry_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

variable {B R ω κ P Y o l : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
  (hω : M.IsOmega ω)
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))
include O hZFC hU hω

omit O in
theorem rows_split_l (hP : M.IsCartesianProduct I P κ ω) (hY : Pair_d M Y o l)
    (hB : ∀ p, M.mem p B ↔ Fn_d I ω P Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    {i j} (hi : M.mem i κ) (hj : M.mem j κ) (hne : i ≠ j) : ∃ p, U p ∧ Split_d M ω i j o l p := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push i).push j).push o).push l
  let φ : UnarySchema 5 := { body := split_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  apply generic_pick_l hZF hU ⟨5, φ, ρ, fun p => split_sat_l hZF.1 (ρ.push p) _ _ _ _ _ _⟩ hp₀
  intro p hp
  have hpF := (hB p).mp hp.1
  obtain ⟨n, hn, hnew⟩ := fresh_rows_l hZFC hω hpF.2 i j
  obtain ⟨a, ha⟩ := (I).total i n
  obtain ⟨c, hc⟩ := (I).total j n
  obtain ⟨q, d, hd, hq, hqF, haq⟩ := ZF.pfn_insert_l I hZF hpF.1
    ((hP a).mpr ⟨i, hi, n, hn, ha⟩) ((hY o).mpr (Or.inl rfl)) (hnew a (Or.inl ha))
  have hqN : Fn_d I ω P Y q := ⟨hqF, ZF.finite_insert_l I hZF hω hpF.2 hq⟩
  have hcn : ¬ ∃ v, Entry_d M c v q := by
    rintro ⟨v, d', hd', hd'q⟩
    rcases (hq d').mp hd'q with hd'p | rfl
    · exact hnew c (Or.inr hc) ⟨v, d', hd', hd'p⟩
    · have hca := (kpair_injective_l M hd' hd).1
      exact hne (kpair_injective_l M ha (hca ▸ hc)).1
  obtain ⟨r, hr, hqr, hcr⟩ := ZF.fn_insert_l I hZF hω hqN
    ((hP c).mpr ⟨j, hj, n, hn, hc⟩) ((hY l).mpr (Or.inr rfl)) hcn
  refine ⟨r, subset_below_l hZF hR hp.1 ((hB r).mpr hr)
    (fun x hx => hqr x ((hq x).mpr (Or.inl hx))), n, a, c, hn, ha, hc, ?_, hcr⟩
  exact haq.elim fun d hd => ⟨d, hd.1, hqr d hd.2⟩

def Diagonal_d (M : SetTheory.Structure.{u}) (ω i A o l p : M.Domain) : Prop :=
  ∃ n a, M.mem n ω ∧ KPair_d M a i n ∧
    ((M.mem n A ∧ Entry_d M a o p) ∨ (¬ M.mem n A ∧ Entry_d M a l p))

def diagonal_m {n} (ω i A o l p : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (.mem (.bound 1) ω.weaken.weaken)
    (.conj (kpair_m .newest i.weaken.weaken (.bound 1))
      (.disj (.conj (.mem (.bound 1) A.weaken.weaken) (entry_m .newest o.weaken.weaken p.weaken.weaken))
        (.conj (.neg (.mem (.bound 1) A.weaken.weaken)) (entry_m .newest l.weaken.weaken p.weaken.weaken))))))
derive_free_closed diagonal_m

omit O hZFC hU hω in
theorem diagonal_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω i A o l p : Term n) :
    Formula.satisfies ρ (diagonal_m ω i A o l p) ↔
      Diagonal_d M (ω.eval ρ) (i.eval ρ) (A.eval ρ) (o.eval ρ) (l.eval ρ) (p.eval ρ) := by
  simp only [diagonal_m, Diagonal_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, entry_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

omit O in
theorem row_diagonal_l (hP : M.IsCartesianProduct I P κ ω) (hY : Pair_d M Y o l)
    (hB : ∀ p, M.mem p B ↔ Fn_d I ω P Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    {i} (hi : M.mem i κ) (A : M.Domain) : ∃ p, U p ∧ Diagonal_d M ω i A o l p := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push i).push A).push o).push l
  let φ : UnarySchema 5 := { body := diagonal_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  apply generic_pick_l hZF hU ⟨5, φ, ρ, fun p => diagonal_sat_l hZF.1 (ρ.push p) _ _ _ _ _ _⟩ hp₀
  intro p hp
  have hpF := (hB p).mp hp.1
  obtain ⟨n, hn, hnew⟩ := fresh_rows_l hZFC hω hpF.2 i i
  obtain ⟨a, ha⟩ := (I).total i n
  have extend v (hv : M.mem v Y) : ∃ q, Below_d M B R B q p ∧ Entry_d M a v q := by
    obtain ⟨q, hq, hqp, haq⟩ := ZF.fn_insert_l I hZF hω hpF
      ((hP a).mpr ⟨i, hi, n, hn, ha⟩) hv (hnew a (Or.inl ha))
    exact ⟨q, subset_below_l hZF hR hp.1 ((hB q).mpr hq) hqp, haq⟩
  by_cases hnA : M.mem n A
  · obtain ⟨q, hq, haq⟩ := extend o ((hY o).mpr (Or.inl rfl))
    exact ⟨q, hq, n, a, hn, ha, Or.inl ⟨hnA, haq⟩⟩
  · obtain ⟨q, hq, haq⟩ := extend l ((hY l).mpr (Or.inr rfl))
    exact ⟨q, hq, n, a, hn, ha, Or.inr ⟨hnA, haq⟩⟩

end YesMetaZFC.Model.Forcing.Internal
