import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Rule

/-! # 比较的内部有限证书与 Σ₁ 定义

每行记录 (高度,左码,右码)，递归比较只读取较低高度。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure Po_cert_d (F T : M.Domain) : Prop where
  trans : M.TransitiveSet T
  graph : M.mem F T
  row : ∀ r, M.mem r F → ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧ ∃ x, M.mem x T ∧
    Rd_triple_d r h c x ∧ KP.N0_d h ∧ Po_step_d T (Pc_read_d F h) c x

def po_cert_m {n} (F T : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive T) (.conj (.mem F T) (Formula.forallMem F
    (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken
      (.conj (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest) (.conj (KP.n0_m (.bound 2))
        (po_step_m T.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))
derive_free_closed po_cert_m

theorem po_cert_delta_l {n} (F T : Term n) : (po_cert_m F T).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (.mem _ _) (.forallMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_triple0_delta_l ..) (.conj (KP.n0_delta_l _) (po_step_delta_l ..))))))))

theorem po_cert_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (F T : Term n) :
    Formula.satisfies ρ (po_cert_m F T) ↔ Po_cert_d (F.eval ρ) (T.eval ρ) := by
  simp only [po_cert_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rd_triple0_sat_l hKP.1, KP.n0_sat_l hKP.1, po_step_sat_l hKP.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.trans, h.graph, h.row⟩⟩

theorem Po_cert_d.at_l {F T h c x : M.Domain} (hf : Po_cert_d F T) (hx : Pc_at_d F h c x) :
    M.mem h T ∧ M.mem c T ∧ M.mem x T ∧ KP.N0_d h ∧ Po_step_d T (Pc_read_d F h) c x := by
  obtain ⟨r, hr, hx⟩ := hx
  obtain ⟨n, hn, d, hd, y, hy, hp, ho, hs⟩ := hf.row r hr
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hp hx
  exact ⟨hn, hd, hy, ho, hs⟩

def Po_rank_d (h c x : M.Domain) : Prop := ∃ T F, Po_cert_d F T ∧ Pc_at_d F h c x

def po_rank_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest (.conj (po_cert_m .newest (.bound 1))
      (pc_at_m .newest (.bound 4) (.bound 3) (.bound 2)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.conj (po_cert_delta_l ..) (pc_at_delta_l ..)) }

theorem po_rank_sat_l (hKP : M.Models KP) (ρ : Env M 1) (c x : M.Domain) :
    po_rank_s.schema.denote ρ c x ↔ Po_rank_d (ρ.bound 0) c x := by
  rw [S1_binary.sat_l]
  simp only [po_rank_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, po_cert_sat_l hKP, pc_at_sat_l hKP.1]
  change (∃ T F, M.mem F T ∧ Po_cert_d F T ∧ Pc_at_d F (ρ.bound 0) c x) ↔ _
  exact ⟨fun ⟨T, F, _, hf, hx⟩ => ⟨T, F, hf, hx⟩, fun ⟨T, F, hf, hx⟩ => ⟨T, F, hf.graph, hf, hx⟩⟩

def po_rank_m {n} (h c x : Term n) : Formula 1 n := binary_pred_m po_rank_s.schema (fun _ => h) c x
derive_free_closed po_rank_m

theorem po_rank_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (h c x : Term n) :
    Formula.satisfies ρ (po_rank_m h c x) ↔ Po_rank_d (h.eval ρ) (c.eval ρ) (x.eval ρ) := by
  rw [po_rank_m, binary_pred_sat_l, po_rank_sat_l hKP]

def Po_lt_d (c x : M.Domain) : Prop := ∃ h, Po_rank_d h c x

def po_lt_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (po_cert_m .newest (.bound 2)) (pc_at_m .newest (.bound 1) (.bound 4) (.bound 3))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (po_cert_delta_l ..) (pc_at_delta_l ..))) }

theorem po_lt_sat_l (hKP : M.Models KP) (ρ : Env M 0) (c x : M.Domain) :
    po_lt_s.schema.denote ρ c x ↔ Po_lt_d c x := by
  rw [S1_binary.sat_l]
  simp only [po_lt_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, po_cert_sat_l hKP, pc_at_sat_l hKP.1]
  change (∃ T h, M.mem h T ∧ ∃ F, M.mem F T ∧ Po_cert_d F T ∧ Pc_at_d F h c x) ↔ _
  exact ⟨fun ⟨T, h, _, F, _, hf, hx⟩ => ⟨h, T, F, hf, hx⟩,
    fun ⟨h, T, F, hf, hx⟩ => ⟨T, h, (hf.at_l hx).1, F, hf.graph, hf, hx⟩⟩

def po_lt_m {n} (c x : Term n) : Formula 1 n := binary_pred_m po_lt_s.schema Fin.elim0 c x
derive_free_closed po_lt_m

theorem po_lt_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (c x : Term n) :
    Formula.satisfies ρ (po_lt_m c x) ↔ Po_lt_d (c.eval ρ) (x.eval ρ) := by
  rw [po_lt_m, binary_pred_sat_l, po_lt_sat_l hKP]

end YesMetaZFC.SetTheory.InnerModel
