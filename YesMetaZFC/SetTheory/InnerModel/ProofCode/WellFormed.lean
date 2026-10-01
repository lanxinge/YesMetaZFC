import YesMetaZFC.SetTheory.InnerModel.ProofCode.Construction

/-! # 独立于求值的内部码合法性

语法历史只保存 (高度,码)，检查序数参数及较低高度的子码；不查询 J 层值。
合法码的求值总性随后由内部高度归纳证明。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Ps_read_d (F h c : M.Domain) : Prop := ∃ n, M.mem n h ∧ Rd_entry_d n c F
def ps_read_m {n} (F h c : Term n) : Formula 1 n := Formula.existsMem h (rd_entry0_m .newest c.weaken F.weaken)
derive_free_closed ps_read_m
theorem ps_read_delta_l {n} (F h c : Term n) : (ps_read_m F h c).IsDelta0 := .existsMem _ (rd_entry0_delta_l ..)
theorem ps_read_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F h c : Term n) :
    Formula.satisfies ρ (ps_read_m F h c) ↔ Ps_read_d (F.eval ρ) (h.eval ρ) (c.eval ρ) := by
  simp only [ps_read_m, Ps_read_d, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Ps_step_d (T F h c : M.Domain) : Prop :=
  (∃ a, M.mem a T ∧ Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
    ∃ k a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ d, M.mem d T ∧
      Pc_node_d T k c a b d ∧ Ps_read_d F h a ∧ Ps_read_d F h b ∧ Ps_read_d F h d

def ps_step_m {n} (T F h c : Term n) : Formula 1 n :=
  .disj (Formula.existsMem T (.conj (pc_leaf_m T.weaken c.weaken .newest) (KP.ord0_m .newest)))
    (rd_any_m rd_menu_l (fun k => Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
      (.conj (pc_node_m T.weaken.weaken.weaken k c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.conj (ps_read_m F.weaken.weaken.weaken h.weaken.weaken.weaken (.bound 2))
          (.conj (ps_read_m F.weaken.weaken.weaken h.weaken.weaken.weaken (.bound 1))
            (ps_read_m F.weaken.weaken.weaken h.weaken.weaken.weaken .newest))))))))
derive_free_closed ps_step_m

theorem ps_step_delta_l {n} (T F h c : Term n) : (ps_step_m T F h c).IsDelta0 :=
  .disj (.existsMem _ (.conj (pc_leaf_delta_l ..) (KP.ord0_delta_l _)))
    (rd_any_delta_l _ _ (fun _ => .existsMem _ (.existsMem _ (.existsMem _ (.conj (pc_node_delta_l ..)
      (.conj (ps_read_delta_l ..) (.conj (ps_read_delta_l ..) (ps_read_delta_l ..))))))))

theorem ps_step_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T F h c : Term n) :
    Formula.satisfies ρ (ps_step_m T F h c) ↔ Ps_step_d (T.eval ρ) (F.eval ρ) (h.eval ρ) (c.eval ρ) := by
  simp only [ps_step_m, Ps_step_d, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, pc_leaf_sat_l hKP.1, KP.ord0_sat_l hKP, rd_any_sat_l,
    pc_node_sat_l hKP.1, ps_read_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact or_congr Iff.rfl ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, rd_menu_mem_l k, h⟩⟩

structure Ps_cert_d (F T : M.Domain) : Prop where
  trans : M.TransitiveSet T
  graph : M.mem F T
  row : ∀ r, M.mem r F → ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧
    KPair_d M r h c ∧ KP.N0_d h ∧ Ps_step_d T F h c

def ps_cert_m {n} (F T : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive T) (.conj (.mem F T) (Formula.forallMem F
    (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.conj (KP.n0_m (.bound 1))
        (ps_step_m T.weaken.weaken.weaken F.weaken.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed ps_cert_m

theorem ps_cert_delta_l {n} (F T : Term n) : (ps_cert_m F T).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (.mem _ _) (.forallMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (KP.n0_delta_l _) (ps_step_delta_l ..)))))))

theorem ps_cert_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (F T : Term n) :
    Formula.satisfies ρ (ps_cert_m F T) ↔ Ps_cert_d (F.eval ρ) (T.eval ρ) := by
  simp only [ps_cert_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    kpair0_sat_l hKP.1, KP.n0_sat_l hKP.1, ps_step_sat_l hKP, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.trans, h.graph, h.row⟩⟩

theorem Ps_cert_d.at_l {F T h c : M.Domain} (hf : Ps_cert_d F T) (hc : Rd_entry_d h c F) :
    M.mem h T ∧ M.mem c T ∧ KP.N0_d h ∧ Ps_step_d T F h c := by
  obtain ⟨r, hr, hrf⟩ := hc
  obtain ⟨n, hn, d, hd, hp, ho, hs⟩ := hf.row r hrf
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hr
  exact ⟨hn, hd, ho, hs⟩

def Ps_rank_d (h c : M.Domain) : Prop := ∃ T F, Ps_cert_d F T ∧ Rd_entry_d h c F
def Ps_valid_d (c : M.Domain) : Prop := ∃ h, Ps_rank_d h c

def ps_rank_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (.conj (ps_cert_m .newest (.bound 1)) (rd_entry0_m (.bound 3) (.bound 2) .newest))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.conj (ps_cert_delta_l ..) (rd_entry0_delta_l ..)) }

theorem ps_rank_sat_l (hKP : M.Models KP) (ρ : Env M 0) (h c : M.Domain) :
    ps_rank_s.schema.denote ρ h c ↔ Ps_rank_d h c := by
  rw [S1_binary.sat_l]
  simp only [ps_rank_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, ps_cert_sat_l hKP, rd_entry0_sat_l hKP.1]
  change (∃ T F, M.mem F T ∧ Ps_cert_d F T ∧ Rd_entry_d h c F) ↔ _
  exact ⟨fun ⟨T, F, _, hf, hc⟩ => ⟨T, F, hf, hc⟩, fun ⟨T, F, hf, hc⟩ => ⟨T, F, hf.graph, hf, hc⟩⟩

def ps_rank_m {n} (h c : Term n) : Formula 1 n := binary_pred_m ps_rank_s.schema Fin.elim0 h c
derive_free_closed ps_rank_m
theorem ps_rank_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (h c : Term n) :
    Formula.satisfies ρ (ps_rank_m h c) ↔ Ps_rank_d (h.eval ρ) (c.eval ρ) := by
  rw [ps_rank_m, binary_pred_sat_l, ps_rank_sat_l hKP]

theorem ps_eval_total_l (hM : M.Models KPi) {c : M.Domain} (hc : Ps_valid_d c) : ∃ x, Pc_eval_d c x := by
  obtain ⟨h, hc⟩ := hc
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema 0 := { body := .forallE (.imp (ps_rank_m (.bound 1) .newest)
    (.existsE (pc_eval_m (.bound 1) .newest))) }
  have hψ n : ψ.denote (jh_env_l h) n ↔ ∀ c, Ps_rank_d n c → ∃ x, Pc_eval_d c x := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ps_rank_formula_l hKP, Formula.satisfies_exists_iff, pc_eval_formula_l hKP]
    rfl
  apply (hψ h).mp (hi ψ (jh_env_l h) ?_ h) c hc
  intro n ih
  apply (hψ n).mpr
  rintro c ⟨T, F, hf, hc⟩
  have child {d} (hd : Ps_read_d F n d) : ∃ x, Pc_eval_d d x :=
    hd.elim fun m hm => (hψ m).mp (ih m hm.1) d ⟨T, F, hf, hm.2⟩
  rcases (hf.at_l hc).2.2.2 with ⟨a, _, hc, ha⟩ | ⟨k, a, _, b, _, d, _, hc, ha, hb, hd⟩
  · obtain ⟨x, hx⟩ := jh_value_exists_l hM a
    exact ⟨x, pc_leaf_value_l hM hc ha hx⟩
  · obtain ⟨u, hu⟩ := child ha
    obtain ⟨v, hv⟩ := child hb
    obtain ⟨w, hw⟩ := child hd
    obtain ⟨x, hx⟩ := rd_fun_exists_l hKP k u v w
    exact ⟨x, pc_node_value_l hM hc hu hv hw hx⟩

end YesMetaZFC.SetTheory.InnerModel
