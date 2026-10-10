import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Global

/-! # 规范码序的 Σ₁ 正规形及合法码名上的 Δ₁ 判定

正向证书检查字典比较；反向证书检查相等或反向严格比较。完备性来自已证明
的三歧性，互斥性来自序律，没有把不可证的反射或判定性加入模型假设。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem po_matrix_env_l (φ : S1_binary 0) (ρ : Env M 0) {n} (η : Env M n) (x y w : Term n) :
    Formula.satisfies η (φ.matrix_m Fin.elim0 x y w) ↔
      φ.matrix_binary.toBinarySchema.denote (ρ.push (x.eval η)) (y.eval η) (w.eval η) := by
  rw [S1_binary.matrix_sat_l]
  exact Formula.closed_env_l _ φ.matrix.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))

def pn_lt_s : S1_binary 0 where
  -- 存在量词之后的槽位为 W,d,m,b,c,h,a,T,w,v；W 只验证最后的树比较。
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <|
        .conj (rd_triple0_m (.bound 9) (.bound 6) (.bound 5) (.bound 4)) <|
          .conj (rd_triple0_m (.bound 8) (.bound 3) (.bound 2) (.bound 1)) <|
            .disj (.mem (.bound 6) (.bound 3)) <| .conj (Formula.extensionalEq (.bound 6) (.bound 3)) <|
              .disj (.mem (.bound 5) (.bound 2)) <| .conj (Formula.extensionalEq (.bound 5) (.bound 2))
                (po_lt_s.matrix_m Fin.elim0 (.bound 4) (.bound 1) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (rd_triple0_delta_l ..) (.conj (rd_triple0_delta_l ..) (.disj (.mem _ _)
        (.conj (.atom _ _ _) (.disj (.mem _ _) (.conj (.atom _ _ _) (po_lt_s.matrix.delta0.bind_l _))))))))))))) }

theorem pn_lt_sat_l (hKP : M.Models KP) (ρ : Env M 0) (v w : M.Domain) :
    pn_lt_s.schema.denote ρ v w ↔ Pn_lt_d v w := by
  rw [S1_binary.sat_l]
  simp only [pn_lt_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_triple0_sat_l hKP.1,
    Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1, po_matrix_env_l po_lt_s ρ]
  change (∃ T a, M.mem a T ∧ ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧ ∃ b, M.mem b T ∧ ∃ m, M.mem m T ∧
    ∃ d, M.mem d T ∧ ∃ W, M.mem W T ∧ Rd_triple_d v a h c ∧ Rd_triple_d w b m d ∧
      (M.mem a b ∨ a = b ∧ (M.mem h m ∨ h = m ∧ po_lt_s.matrix_binary.toBinarySchema.denote (ρ.push c) d W))) ↔ _
  constructor
  · rintro ⟨T, a, _, h, _, c, _, b, _, m, _, d, _, W, _, hv, hw, he⟩
    refine ⟨a, h, c, b, m, d, hv, hw, ?_⟩
    rcases he with he | ⟨he, hf | ⟨hf, hg⟩⟩
    · exact Or.inl he
    · exact Or.inr ⟨he, Or.inl hf⟩
    · exact Or.inr ⟨he, Or.inr ⟨hf, (po_lt_sat_l hKP ρ c d).mp ((po_lt_s.sat_l ρ c d).mpr ⟨W, hg⟩)⟩⟩
  · rintro ⟨a, h, c, b, m, d, hv, hw, he⟩
    have witness : ∃ W, M.mem a b ∨ a = b ∧ (M.mem h m ∨ h = m ∧
        po_lt_s.matrix_binary.toBinarySchema.denote (ρ.push c) d W) := by
      rcases he with he | ⟨he, hf | ⟨hf, hg⟩⟩
      · exact ⟨a, Or.inl he⟩
      · exact ⟨a, Or.inr ⟨he, Or.inl hf⟩⟩
      · obtain ⟨W, hg⟩ := (po_lt_s.sat_l ρ c d).mp ((po_lt_sat_l hKP ρ c d).mpr hg)
        exact ⟨W, Or.inr ⟨he, Or.inr ⟨hf, hg⟩⟩⟩
    obtain ⟨W, he⟩ := witness
    obtain ⟨T, hT⟩ := kp_finite_cover_l hKP [a, h, c, b, m, d, W]
    exact ⟨T, a, (hT a (by simp)).2, h, (hT h (by simp)).2, c, (hT c (by simp)).2,
      b, (hT b (by simp)).2, m, (hT m (by simp)).2, d, (hT d (by simp)).2, W, (hT W (by simp)).2, hv, hw, he⟩

def pn_lt_m {n} (v w : Term n) : Formula 1 n := binary_pred_m pn_lt_s.schema Fin.elim0 v w
derive_free_closed pn_lt_m
theorem pn_lt_formula_l (hKP : M.Models KP) {n} (ρ : Env M n) (v w : Term n) :
    Formula.satisfies ρ (pn_lt_m v w) ↔ Pn_lt_d (v.eval ρ) (w.eval ρ) := by
  rw [pn_lt_m, binary_pred_sat_l, pn_lt_sat_l hKP]

def pn_not_lt_s : S1_binary 0 where
  matrix := {
    body := .disj (Formula.extensionalEq (.bound 2) (.bound 1)) (pn_lt_s.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .disj (.atom _ _ _) (pn_lt_s.matrix.delta0.bind_l _) }

theorem pn_not_lt_sat_l (hKP : M.Models KP) (ρ : Env M 0) (v w : M.Domain) :
    pn_not_lt_s.schema.denote ρ v w ↔ v = w ∨ Pn_lt_d w v := by
  rw [S1_binary.sat_l]
  simp only [pn_not_lt_s, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1, po_matrix_env_l pn_lt_s ρ]
  change (∃ T, v = w ∨ pn_lt_s.matrix_binary.toBinarySchema.denote (ρ.push w) v T) ↔ _
  exact ⟨fun ⟨T, h⟩ => h.elim Or.inl (fun h => Or.inr ((pn_lt_sat_l hKP ρ w v).mp ((pn_lt_s.sat_l ρ w v).mpr ⟨T, h⟩))),
    fun h => h.elim (fun he => ⟨v, Or.inl he⟩) (fun h =>
      ((pn_lt_s.sat_l ρ w v).mp ((pn_lt_sat_l hKP ρ w v).mpr h)).imp (fun _ h => Or.inr h))⟩

theorem pn_delta1_l (hM : M.Models KPi) {v w : M.Domain} (hv : Pn_valid_d v) (hw : Pn_valid_d w) (ρ : Env M 0) :
    pn_lt_s.schema.denote ρ v w ↔ ¬ pn_not_lt_s.schema.denote ρ v w := by
  rw [pn_lt_sat_l (KPi.models_iff_l.mp hM).1, pn_not_lt_sat_l (KPi.models_iff_l.mp hM).1]
  constructor
  · intro h g
    rcases g with rfl | g
    · exact pn_irrefl_l hM hv h
    · exact pn_irrefl_l hM hv (pn_trans_l hM hv hw hv h g)
  · intro hn
    exact (pn_compare_l hM hv hw).elim (fun h => (hn (Or.inl h)).elim) (fun h => h.elim id (fun h => (hn (Or.inr h)).elim))

end YesMetaZFC.SetTheory.InnerModel
