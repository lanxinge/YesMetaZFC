import YesMetaZFC.SetTheory.InnerModel.ProofCode.Rules

/-! # 内部构造推导的 Σ₁ 求值关系

历史中的每一行是 (内部自然数高度,码,值)。证书逐行检查，不假定历史先已
是函数；同一码的函数性将在内部高度归纳中证明。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure Pc_cert_d (F T : M.Domain) : Prop where
  trans : M.TransitiveSet T
  graph : M.mem F T
  row : ∀ r, M.mem r F → ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧ ∃ x, M.mem x T ∧
    Rd_triple_d r h c x ∧ KP.N0_d h ∧ Pc_step_d T F h c x

def pc_cert_m {n} (F T : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive T) (.conj (.mem F T) (Formula.forallMem F
    (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken
      (.conj (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest) (.conj (KP.n0_m (.bound 2))
        (pc_step_m T.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))
derive_free_closed pc_cert_m

theorem pc_cert_delta_l {n} (F T : Term n) : (pc_cert_m F T).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (.mem _ _) (.forallMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_triple0_delta_l ..) (.conj (KP.n0_delta_l _) (pc_step_delta_l ..))))))))

theorem pc_cert_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (F T : Term n) :
    Formula.satisfies ρ (pc_cert_m F T) ↔ Pc_cert_d (F.eval ρ) (T.eval ρ) := by
  simp only [pc_cert_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rd_triple0_sat_l hKP.1, KP.n0_sat_l hKP.1, pc_step_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.trans, h.graph, h.row⟩⟩

theorem Pc_cert_d.at_l {F T h c x : M.Domain} (hf : Pc_cert_d F T) (hx : Pc_at_d F h c x) :
    M.mem h T ∧ M.mem c T ∧ M.mem x T ∧ KP.N0_d h ∧ Pc_step_d T F h c x := by
  obtain ⟨r, hr, hx⟩ := hx
  obtain ⟨n, hn, d, hd, y, hy, hp, ho, hs⟩ := hf.row r hr
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hp hx
  exact ⟨hn, hd, hy, ho, hs⟩

def Pc_rank_d (h c x : M.Domain) : Prop := ∃ T F, Pc_cert_d F T ∧ Pc_at_d F h c x

def pc_rank_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest (.conj (pc_cert_m .newest (.bound 1))
      (pc_at_m .newest (.bound 4) (.bound 3) (.bound 2)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.conj (pc_cert_delta_l ..) (pc_at_delta_l ..)) }

theorem pc_rank_sat_l (hKP : M.Models KP) (ρ : Env M 1) (c x : M.Domain) :
    pc_rank_s.schema.denote ρ c x ↔ Pc_rank_d (ρ.bound 0) c x := by
  rw [S1_binary.sat_l]
  simp only [pc_rank_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pc_cert_sat_l hKP, pc_at_sat_l hKP.1]
  change (∃ T F, M.mem F T ∧ Pc_cert_d F T ∧ Pc_at_d F (ρ.bound 0) c x) ↔ _
  exact ⟨fun ⟨T, F, _, hf, hx⟩ => ⟨T, F, hf, hx⟩, fun ⟨T, F, hf, hx⟩ => ⟨T, F, hf.graph, hf, hx⟩⟩

def pc_rank_m {n} (h c x : Term n) : Formula 1 n := binary_pred_m pc_rank_s.schema (fun _ => h) c x
derive_free_closed pc_rank_m

theorem pc_rank_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (h c x : Term n) :
    Formula.satisfies ρ (pc_rank_m h c x) ↔ Pc_rank_d (h.eval ρ) (c.eval ρ) (x.eval ρ) := by
  rw [pc_rank_m, binary_pred_sat_l, pc_rank_sat_l hKP]

def Pc_eval_d (c x : M.Domain) : Prop := ∃ h, Pc_rank_d h c x

def pc_eval_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (pc_cert_m .newest (.bound 2)) (pc_at_m .newest (.bound 1) (.bound 4) (.bound 3))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (pc_cert_delta_l ..) (pc_at_delta_l ..))) }

theorem pc_eval_sat_l (hKP : M.Models KP) (ρ : Env M 0) (c x : M.Domain) :
    pc_eval_s.schema.denote ρ c x ↔ Pc_eval_d c x := by
  rw [S1_binary.sat_l]
  simp only [pc_eval_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pc_cert_sat_l hKP, pc_at_sat_l hKP.1]
  change (∃ T h, M.mem h T ∧ ∃ F, M.mem F T ∧ Pc_cert_d F T ∧ Pc_at_d F h c x) ↔ _
  exact ⟨fun ⟨T, h, _, F, _, hf, hx⟩ => ⟨h, T, F, hf, hx⟩,
    fun ⟨h, T, F, hf, hx⟩ => ⟨T, h, (hf.at_l hx).1, F, hf.graph, hf, hx⟩⟩

def pc_eval_m {n} (c x : Term n) : Formula 1 n := binary_pred_m pc_eval_s.schema Fin.elim0 c x
derive_free_closed pc_eval_m

theorem pc_eval_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (c x : Term n) :
    Formula.satisfies ρ (pc_eval_m c x) ↔ Pc_eval_d (c.eval ρ) (x.eval ρ) := by
  rw [pc_eval_m, binary_pred_sat_l, pc_eval_sat_l hKP]

end YesMetaZFC.SetTheory.InnerModel
