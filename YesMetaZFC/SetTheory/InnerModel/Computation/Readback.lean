import YesMetaZFC.SetTheory.InnerModel.Computation.Delta1

/-! # 总搜索程序到 Δ₁ 定义及语义往返 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cs_classify_s {n} (b : Bool) (p : Cs_code (n + 2)) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj ((cs_graph_s p).matrix_m (fun i => .bound ⟨i.val + 4, by omega⟩) (.bound 3) (.bound 1) .newest)
        (if b then Formula.existsMem (.bound 1) .truth else Formula.forallMem (.bound 1) .falsum)))
    freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj ((cs_graph_s p).matrix.delta0.bind_l _)
      (by cases b; exact .forallMem _ .falsum; exact .existsMem _ .truth))) }

theorem cs_classify_sat_l (hKP : M.Models KP) {n} (b : Bool) (p : Cs_code (n + 2)) (ρ : Env M n) (x y : M.Domain) :
    (cs_classify_s b p).schema.denote ρ x y ↔
      ∃ v, Cs_eval_d p ((ρ.push x).push y) v ∧ (if b then ∃ t, M.mem t v else ∀ t, ¬ M.mem t v) := by
  have htest {k} (η : Env M k) (t : Term k) :
      Formula.satisfies η (if b then Formula.existsMem t .truth else Formula.forallMem t .falsum) ↔
        (if b then ∃ z, M.mem z (t.eval η) else ∀ z, ¬ M.mem z (t.eval η)) := by
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Formula.satisfies_existsMem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_truth_iff, Formula.satisfies_falsum_iff, and_true]
  rw [S1_binary.sat_l]
  simp only [cs_classify_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, S1_binary.matrix_sat_l, htest]
  change (∃ T v, M.mem v T ∧ ∃ w, M.mem w T ∧
    (cs_graph_s p).matrix_binary.toBinarySchema.denote ((ρ.push x).push y) v w ∧
    (if b then ∃ t, M.mem t v else ∀ t, ¬ M.mem t v)) ↔ _
  constructor
  · rintro ⟨T, v, _, w, _, hw, ht⟩
    exact ⟨v, (cs_graph_sat_l hKP p (ρ.push x) y v).mp (((cs_graph_s p).sat_l (ρ.push x) y v).mpr ⟨w, hw⟩), ht⟩
  · rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw⟩ := ((cs_graph_s p).sat_l (ρ.push x) y v).mp ((cs_graph_sat_l hKP p (ρ.push x) y v).mpr hv)
    obtain ⟨T, hT⟩ := cp_cover_l hKP [v, w]
    exact ⟨T, v, (hT v (by simp)).2, w, (hT w (by simp)).2, hw, ht⟩

def cs_pair_l {n} (p : Cs_code (n + 2)) : D1_pair n := ⟨cs_classify_s true p, cs_classify_s false p⟩

theorem cs_pair_compl_l (hM : M.Models KPi) {n} (p : Cs_code (n + 2))
    (ht : ∀ (ρ : Env M n) x y, ∃ v, Cs_eval_d p ((ρ.push x).push y) v) : D1_compl_d (M := M) (cs_pair_l p) := by
  let hKP := (KPi.models_iff_l.mp hM).1
  intro ρ x y
  change (cs_classify_s true p).schema.denote ρ x y ↔ ¬ (cs_classify_s false p).schema.denote ρ x y
  simp only [cs_classify_sat_l hKP, if_true, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨v, hv, z, hz⟩ ⟨w, hw, he⟩
    exact he z (cs_eval_unique_l hM hv hw ▸ hz)
  · intro hn
    obtain ⟨v, hv⟩ := ht ρ x y
    exact ⟨v, hv, Classical.byContradiction (fun he => hn ⟨v, hv, fun z hz => he ⟨z, hz⟩⟩)⟩

theorem cd_roundtrip_compl_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) {n}
    (d : D1_pair n) (hc : D1_compl_d (M := M) d) : D1_compl_d (M := M) (cs_pair_l (cd_compile_l d)) :=
  cs_pair_compl_l hM _ (fun ρ x y => cd_eval_total_l hM hVL d ρ x y (hc ρ x y))

theorem cd_roundtrip_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) {n}
    (d : D1_pair n) (ρ : Env M n) (x y : M.Domain)
    (hc : d.pos.schema.denote ρ x y ↔ ¬ d.neg.schema.denote ρ x y) :
    (cs_pair_l (cd_compile_l d)).pos.schema.denote ρ x y ↔ d.pos.schema.denote ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  change (cs_classify_s true (cd_compile_l d)).schema.denote ρ x y ↔ _
  rw [cs_classify_sat_l hKP]
  constructor
  · rintro ⟨v, hv, t, ht⟩
    exact ((cd_eval_sound_l hKP d ρ x y hc hv t).mp ht).2
  · intro hp
    obtain ⟨v, hv⟩ := cd_eval_total_l hM hVL d ρ x y hc
    obtain ⟨e, he⟩ := KP.exists_empty hKP
    exact ⟨v, hv, e, (cd_eval_sound_l hKP d ρ x y hc hv e).mpr ⟨he, hp⟩⟩

def D1_defined_d {n} (R : Env M n → M.Domain → M.Domain → Prop) : Prop :=
  ∃ d : D1_pair n, D1_compl_d (M := M) d ∧ ∀ ρ x y, d.pos.schema.denote ρ x y ↔ R ρ x y

def Cs_computable_d {n} (R : Env M n → M.Domain → M.Domain → Prop) : Prop :=
  ∃ p : Cs_code (n + 2), ∀ ρ x y, (∃ v, Cs_eval_d p ((ρ.push x).push y) v) ∧
    ∀ v, Cs_eval_d p ((ρ.push x).push y) v → Cp_bit_d (R ρ x y) v

/-- Δ₁ 定义恰好对应此内部搜索语言的总布尔计算。 -/
theorem cd_equiv_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) {n}
    (R : Env M n → M.Domain → M.Domain → Prop) : D1_defined_d R ↔ Cs_computable_d R := by
  let hKP := (KPi.models_iff_l.mp hM).1
  constructor
  · rintro ⟨d, hc, hr⟩
    exact ⟨cd_compile_l d, fun ρ x y => ⟨cd_eval_total_l hM hVL d ρ x y (hc ρ x y),
      fun v hv t => (cd_eval_sound_l hKP d ρ x y (hc ρ x y) hv t).trans (and_congr_right fun _ => hr ρ x y)⟩⟩
  · rintro ⟨p, ht⟩
    refine ⟨cs_pair_l p, cs_pair_compl_l hM p (fun ρ x y => (ht ρ x y).1), fun ρ x y => ?_⟩
    change (cs_classify_s true p).schema.denote ρ x y ↔ _
    rw [cs_classify_sat_l hKP]
    constructor
    · rintro ⟨v, hv, t, htv⟩
      exact (((ht ρ x y).2 v hv t).mp htv).2
    · intro hR
      obtain ⟨v, hv⟩ := (ht ρ x y).1
      obtain ⟨e, he⟩ := KP.exists_empty hKP
      exact ⟨v, hv, e, ((ht ρ x y).2 v hv e).mpr ⟨he, hR⟩⟩

end YesMetaZFC.SetTheory.InnerModel
