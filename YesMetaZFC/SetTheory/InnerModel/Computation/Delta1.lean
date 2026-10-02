import YesMetaZFC.SetTheory.InnerModel.Computation.SearchTotal
import YesMetaZFC.SetTheory.InnerModel.Computation.Filter
import YesMetaZFC.SetTheory.InnerModel.Jensen.Constructibility

/-! # Δ₁ 定义到内部搜索程序

每层同时运行正、反 Σ₁ 矩阵的有界验证。找到正见证返回 {1}，找到反见证
返回 {0}，尚无见证则返回 ∅。搜索取首个非空返回值之并，得到布尔结果。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure D1_pair (n : Nat) where
  pos : S1_binary n
  neg : S1_binary n

def D1_compl_d {n} (d : D1_pair n) : Prop :=
  ∀ (ρ : Env M n) x y, d.pos.schema.denote ρ x y ↔ ¬ d.neg.schema.denote ρ x y

def cd_basic_l {n} (p : Cp_code (n + 1)) : D1_pair n := ⟨cp_graph_s p, cp_negative_s p⟩

theorem cd_basic_compl_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) : D1_compl_d (M := M) (cd_basic_l p) := by
  intro ρ x y
  change (cp_graph_s p).schema.denote ρ x y ↔ ¬ (cp_negative_s p).schema.denote ρ x y
  rw [cp_graph_sat_l hKP, cp_negative_sat_l hKP]
  exact Classical.not_not.symm

def Cd_seen_d {n} (φ : S1_binary n) (ρ : Env M n) (x y A : M.Domain) : Prop :=
  ∃ w, M.mem w A ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body

def cd_test_s {n} (d : D1_pair n) : Delta0UnarySchema (n + 3) where
  body := .disj (.conj (Formula.existsMem .newest .truth) (Formula.existsMem (.bound 1)
    (d.pos.matrix_m (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 4) (.bound 3) .newest)))
    (.conj (Formula.forallMem .newest .falsum) (Formula.existsMem (.bound 1)
      (d.neg.matrix_m (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 4) (.bound 3) .newest)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.existsMem _ .truth) (.existsMem _ (d.pos.matrix.delta0.bind_l _)))
    (.conj (.forallMem _ .falsum) (.existsMem _ (d.neg.matrix.delta0.bind_l _)))

theorem cd_test_sat_l {n} (d : D1_pair n) (ρ : Env M n) (x y A t : M.Domain) :
    (cd_test_s d).toUnarySchema.denote (((ρ.push x).push y).push A) t ↔
      ((∃ z, M.mem z t) ∧ Cd_seen_d d.pos ρ x y A) ∨ ((∀ z, ¬ M.mem z t) ∧ Cd_seen_d d.neg ρ x y A) := by
  simp only [UnarySchema.denote, cd_test_s, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_truth_iff,
    Formula.satisfies_falsum_iff, S1_binary.matrix_sat_l, and_true]
  rfl

def cd_compile_l {n} (d : D1_pair n) : Cs_code (n + 2) :=
  ⟨cp_filter_l (cp_pair_l .zero cp_one_l) (cp_delta_l (cd_test_s d))⟩

theorem cd_step_spec_l (hKP : M.Models KP) {n} (d : D1_pair n) (ρ : Env M n) (x y A B : M.Domain)
    (hB : Cp_eval_d (cd_compile_l d).step (((ρ.push x).push y).push A) B) :
    ∃ e o, (∀ t, ¬ M.mem t e) ∧ (∀ t, M.mem t o ↔ t = e) ∧
      ∀ t, M.mem t B ↔ (t = o ∧ Cd_seen_d d.pos ρ x y A) ∨ (t = e ∧ Cd_seen_d d.neg ρ x y A) := by
  let η := ((ρ.push x).push y).push A
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  obtain ⟨o, ho⟩ := KP.exists_pair hKP e e
  have hz : Cp_eval_d .zero η e := he
  have hOne : Cp_eval_d cp_one_l η o := (cp_pair_iff_l hKP hz hz o).mpr ho
  obtain ⟨D, hD⟩ := KP.exists_pair hKP e o
  have hs := (cp_pair_iff_l hKP hz hOne D).mpr hD
  have hb := (cp_filter_iff_l hKP hs (fun t _ v hv => cp_delta_correct_l hKP (cd_test_s d) η t v |>.mp hv) B).mp hB
  have hn : ∃ t, M.mem t o := ⟨e, (ho e).mpr (Or.inl rfl)⟩
  refine ⟨e, o, he, fun t => (ho t).trans ⟨fun h => h.elim id id, Or.inl⟩, fun t => ?_⟩
  rw [hb t, hD t, cd_test_sat_l]
  constructor
  · rintro ⟨ht, hp | hq⟩
    · exact Or.inl ⟨ht.elim (fun h => (hp.1.elim (fun z hz => he z (h ▸ hz))).elim) id, hp.2⟩
    · exact Or.inr ⟨ht.elim id (fun h => (hn.elim (fun z hz => hq.1 z (h.symm ▸ hz))).elim), hq.2⟩
  · rintro (⟨ht, hp⟩ | ⟨ht, hq⟩)
    · exact ⟨Or.inr ht, Or.inl ⟨ht.symm ▸ hn, hp⟩⟩
    · exact ⟨Or.inl ht, Or.inr ⟨ht.symm ▸ he, hq⟩⟩

theorem cd_eval_sound_l (hKP : M.Models KP) {n} (d : D1_pair n) (ρ : Env M n) (x y : M.Domain)
    (hc : d.pos.schema.denote ρ x y ↔ ¬ d.neg.schema.denote ρ x y) {v : M.Domain}
    (hv : Cs_eval_d (cd_compile_l d) ((ρ.push x).push y) v) : Cp_bit_d (d.pos.schema.denote ρ x y) v := by
  obtain ⟨B, ⟨a, _, _, _, ⟨A, _, hA⟩, hn, _⟩, hv⟩ := hv
  obtain ⟨e, o, he, ho, hB⟩ := cd_step_spec_l hKP d ρ x y A B hA
  have pos : Cd_seen_d d.pos ρ x y A → d.pos.schema.denote ρ x y :=
    fun ⟨w, _, hw⟩ => (d.pos.sat_l ρ x y).mpr ⟨w, hw⟩
  have neg : Cd_seen_d d.neg ρ x y A → ¬ d.pos.schema.denote ρ x y :=
    fun ⟨w, _, hw⟩ hp => hc.mp hp ((d.neg.sat_l ρ x y).mpr ⟨w, hw⟩)
  intro t
  rw [hv t]
  constructor
  · rintro ⟨z, hz, ht⟩
    rcases (hB z).mp hz with ⟨hz, hp⟩ | ⟨hz, hq⟩
    · have ht := (ho t).mp (hz ▸ ht)
      exact ⟨ht.symm ▸ he, pos hp⟩
    · exact (he t (hz ▸ ht)).elim
  · rintro ⟨ht, hp⟩
    obtain ⟨z, hz⟩ := hn
    have hpos : Cd_seen_d d.pos ρ x y A := ((hB z).mp hz).elim And.right (fun h => (neg h.2 hp).elim)
    exact ⟨o, (hB o).mpr (Or.inl ⟨rfl, hpos⟩), (ho t).mpr
      (hKP.1.eq_of_same_members t e (fun z => iff_of_false (ht z) (he z)))⟩

theorem cd_eval_total_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) {n}
    (d : D1_pair n) (ρ : Env M n) (x y : M.Domain)
    (hc : d.pos.schema.denote ρ x y ↔ ¬ d.neg.schema.denote ρ x y) :
    ∃ v, Cs_eval_d (cd_compile_l d) ((ρ.push x).push y) v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [Structure.satisfiesSentence_iff] at hVL
  have hL := (vl_sat_l hKP ρ.free).mp (hVL ρ.free)
  have hit : ∃ w, Formula.satisfies (((ρ.push x).push y).push w) d.pos.matrix.body ∨
      Formula.satisfies (((ρ.push x).push y).push w) d.neg.matrix.body := by
    classical
    by_cases hp : d.pos.schema.denote ρ x y
    · exact ((d.pos.sat_l ρ x y).mp hp).imp (fun _ hw => Or.inl hw)
    · have hq := Classical.not_not.mp (fun hq => hp (hc.mpr hq))
      exact ((d.neg.sat_l ρ x y).mp hq).imp (fun _ hw => Or.inr hw)
  obtain ⟨w, hw⟩ := hit
  obtain ⟨a, A, ha, hwA⟩ := hL w
  obtain ⟨B, hB⟩ := cp_eval_total_l hKP (cd_compile_l d).step (((ρ.push x).push y).push A)
  obtain ⟨e, o, _, _, hb⟩ := cd_step_spec_l hKP d ρ x y A B hB
  apply cs_eval_exists_l hM (cd_compile_l d) (ρ.push x) y ha.1 ⟨A, ha.2, hB⟩
  exact hw.elim (fun hp => ⟨o, (hb o).mpr (Or.inl ⟨rfl, w, hwA, hp⟩)⟩)
    (fun hq => ⟨e, (hb e).mpr (Or.inr ⟨rfl, w, hwA, hq⟩)⟩)

/-- Δ₁ 的正反见证编译为总判定；正确性含所有输出的反向刻画。 -/
theorem cd_eval_iff_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) {n}
    (d : D1_pair n) (ρ : Env M n) (x y : M.Domain)
    (hc : d.pos.schema.denote ρ x y ↔ ¬ d.neg.schema.denote ρ x y) (v : M.Domain) :
    Cs_eval_d (cd_compile_l d) ((ρ.push x).push y) v ↔ Cp_bit_d (d.pos.schema.denote ρ x y) v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  refine ⟨cd_eval_sound_l hKP d ρ x y hc, fun hv => ?_⟩
  obtain ⟨z, hz⟩ := cd_eval_total_l hM hVL d ρ x y hc
  exact hKP.1.eq_of_same_members z v (fun t => (cd_eval_sound_l hKP d ρ x y hc hz t).trans (hv t).symm) ▸ hz

/-- 已构造的 Jensen 模型与基础程序图给出无需额外接口假设的实例。 -/
theorem cd_basic_in_j_l (hM : M.Models KPi) {n} (p : Cp_code (n + 1)) (ρ : Env (l_model_l hM) n)
    (x y v : (l_model_l hM).Domain) :
    Cs_eval_d (cd_compile_l (cd_basic_l p)) ((ρ.push x).push y) v ↔ Cp_bit_d (Cp_eval_d p (ρ.push x) y) v := by
  have h := cd_eval_iff_l (l_model_kpi_l hM) (l_model_vl_l hM) (cd_basic_l p) ρ x y
    (cd_basic_compl_l (l_model_kp_l hM) p ρ x y) v
  simpa only [cd_basic_l, cp_graph_sat_l (l_model_kp_l hM)] using h

end YesMetaZFC.SetTheory.InnerModel
