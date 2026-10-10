import YesMetaZFC.SetTheory.InnerModel.Order.HistorySuccessor

/-! # 在较早微层内能看到的真实递归证书

查询只量化给定集合内的索引、状态和 Δ₀ 见证。可见状态的载体也在该层内，
这排除了当前及更高索引，是极限处精确收集历史的关键。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def js_wit_m {n} (a p T : Term n) : Formula 1 n := (rc_value_s rw_op_s).matrix_m Fin.elim0 a p T
derive_free_closed js_wit_m
theorem js_wit_delta_l {n} (a p T : Term n) : (js_wit_m a p T).IsDelta0 := (rc_value_s rw_op_s).matrix.delta0.bind_l _
theorem js_wit_sat_l (ρ : Env M 0) {n} (η : Env M n) (a p T : Term n) :
    Formula.satisfies η (js_wit_m a p T) ↔ Formula.satisfies
      (((ρ.push (a.eval η)).push (p.eval η)).push (T.eval η)) (rc_value_s rw_op_s).matrix.body := by
  rw [js_wit_m, S1_binary.matrix_sat_l]
  exact Formula.closed_env_l _ (rc_value_s rw_op_s).matrix.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))

def Js_seen_d (ρ : Env M 0) (B a p : M.Domain) : Prop := M.IsOrdinal a ∧ M.mem a B ∧ M.mem p B ∧
  ∃ T, M.mem T B ∧ Formula.satisfies (((ρ.push a).push p).push T) (rc_value_s rw_op_s).matrix.body
def js_seen_m {n} (B a p : Term n) : Formula 1 n := .conj (KP.ord0_m a)
  (.conj (.mem a B) (.conj (.mem p B) (Formula.existsMem B (js_wit_m a.weaken p.weaken .newest))))
derive_free_closed js_seen_m
theorem js_seen_delta_l {n} (B a p : Term n) : (js_seen_m B a p).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (.mem _ _) (.conj (.mem _ _) (.existsMem _ (js_wit_delta_l ..))))
theorem js_seen_sat_l (hKP : M.Models KP) (ρ : Env M 0) {n} (η : Env M n) (B a p : Term n) :
    Formula.satisfies η (js_seen_m B a p) ↔ Js_seen_d ρ (B.eval η) (a.eval η) (p.eval η) := by
  simp only [js_seen_m, Js_seen_d, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, js_wit_sat_l ρ, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem Js_seen_d.state_l {ρ : Env M 0} {B a p : M.Domain} (h : Js_seen_d ρ B a p) : Js_state_d a p :=
  (js_state_env_l ρ a p).mp ((S1_binary.sat_l _ ρ a p).mpr (h.2.2.2.imp fun _ h => h.2))
theorem js_seen_of_in_l (hKP : M.Models KP) {ρ : Env M 0} {B a p : M.Domain}
    (hb : M.TransitiveSet B) (ha : M.IsOrdinal a) (h : Si_cert_d B (rc_value_s rw_op_s) ρ a p) : Js_seen_d ρ B a p := by
  obtain ⟨T, hTB, ht, hpT, hm⟩ := h
  obtain ⟨A, F, hf, haA, _⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ a p T).mp hm
  exact ⟨ha, hb T hTB a (ht A hf.domain a haA), hb T hTB p hpT, T, hTB, hm⟩

theorem js_seen_lt_l (hM : M.Models KPi) {ρ : Env M 0} {a B R b p : M.Domain}
    (ha : M.IsOrdinal a) (hB : Js_value_d a B R) (h : Js_seen_d ρ B b p) : M.mem b a := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨V, S, hp⟩ := js_state_pair_l hM h.state_l
  have hv : Js_value_d b V S := ⟨p, h.state_l, hp⟩
  have ht := (js_coherence_l hM ha hB).1
  have hVB := (po_pair_bound_l ht h.2.2.1 hp).1
  rcases Structure.IsOrdinal.trichotomy hKP.1 h.1 ha (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP b a) with he | hba | hab
  · have he := hKP.1.eq_of_same_members b a he; subst b
    have he := (js_value_unique_l hM hv hB).1
    exact (KP.mem_irrefl_d hKP B (he ▸ hVB)).elim
  · exact hba
  · exact (KP.mem_irrefl_d hKP B (ht V hVB B (js_value_mem_l hM h.1 hab hB hv))).elim

theorem js_seen_step_in_l (hM : M.Models KPi) {ρ : Env M 0} {B a p q : M.Domain}
    (hB : Rd_closed_d B) (hb : M.TransitiveSet B) (h : Js_seen_d ρ B a p) (hq : Rw_state_d p q) :
    Si_cert_d B rw_state_s ρ p q := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨U, R, hp⟩ := js_state_pair_l hM h.state_l
  obtain ⟨T, hTB, hm⟩ := h.2.2.2
  obtain ⟨A, F, hf, _, hap⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ a p T).mp hm
  have hRT := (po_pair_bound_l hf.trans (hf.function.bound_l hap).2 hp).2
  exact rw_state_in_l hKP hB hb (po_pair_bound_l hb h.2.2.1 hp).1
    (js_coherence_l hM h.1 ⟨p, h.state_l, hp⟩).1 hp ⟨T, hTB, hf.trans, hRT⟩ hq ρ

def js_indices_s : Delta0UnarySchema 1 where
  body := Formula.existsMem (.bound 1) (js_seen_m (.bound 2) (.bound 1) .newest)
  freeClosed := by simp -implicitDefEqProofs
  delta0 := .existsMem _ (js_seen_delta_l ..)
def js_values_s : Delta0UnarySchema 1 where
  body := Formula.existsMem (.bound 1) (js_seen_m (.bound 2) .newest (.bound 1))
  freeClosed := by simp -implicitDefEqProofs
  delta0 := .existsMem _ (js_seen_delta_l ..)
def js_rows_s : Delta0UnarySchema 1 where
  body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (js_seen_m (.bound 3) (.bound 1) .newest)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (js_seen_delta_l ..)))
theorem js_indices_sat_l (hKP : M.Models KP) (ρ : Env M 0) (B a : M.Domain) :
    js_indices_s.toUnarySchema.denote (ρ.push B) a ↔ ∃ p, M.mem p B ∧ Js_seen_d ρ B a p := by
  simp only [UnarySchema.denote, js_indices_s, Formula.satisfies_existsMem_iff, js_seen_sat_l hKP ρ]; rfl
theorem js_values_sat_l (hKP : M.Models KP) (ρ : Env M 0) (B p : M.Domain) :
    js_values_s.toUnarySchema.denote (ρ.push B) p ↔ ∃ a, M.mem a B ∧ Js_seen_d ρ B a p := by
  simp only [UnarySchema.denote, js_values_s, Formula.satisfies_existsMem_iff, js_seen_sat_l hKP ρ]; rfl
theorem js_rows_sat_l (hKP : M.Models KP) (ρ : Env M 0) (B r : M.Domain) :
    js_rows_s.toUnarySchema.denote (ρ.push B) r ↔
      ∃ a, M.mem a B ∧ ∃ p, M.mem p B ∧ KPair_d M r a p ∧ Js_seen_d ρ B a p := by
  simp only [UnarySchema.denote, js_rows_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hKP.1, js_seen_sat_l hKP ρ]; rfl

end YesMetaZFC.SetTheory.InnerModel
