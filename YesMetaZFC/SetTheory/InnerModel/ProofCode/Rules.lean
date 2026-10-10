import YesMetaZFC.SetTheory.InnerModel.ProofCode.Syntax

/-! # 构造推导的有界局部规则 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pc_jh_d (W a x : M.Domain) : Prop :=
  (rc_value_s jh_op_s).matrix_binary.toBinarySchema.denote ((jh_env_l a).push a) x W

def pc_jh_m {n} (W a x : Term n) : Formula 1 n := (rc_value_s jh_op_s).matrix_m Fin.elim0 a x W
derive_free_closed pc_jh_m

theorem pc_jh_delta_l {n} (W a x : Term n) : (pc_jh_m W a x).IsDelta0 :=
  (rc_value_s jh_op_s).matrix.delta0.bind_l _

theorem pc_jh_sat_l {n} (ρ : Env M n) (W a x : Term n) :
    Formula.satisfies ρ (pc_jh_m W a x) ↔ Pc_jh_d (W.eval ρ) (a.eval ρ) (x.eval ρ) := by
  rw [pc_jh_m, S1_binary.matrix_sat_l]
  exact Formula.closed_env_l _ (rc_value_s jh_op_s).matrix.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))

theorem pc_jh_value_l (a x : M.Domain) : (∃ W, Pc_jh_d W a x) ↔ Jh_value_d a x :=
  ((rc_value_s jh_op_s).sat_l (jh_env_l a) a x).symm

def Pc_base_d (T c x : M.Domain) : Prop :=
  ∃ a, M.mem a T ∧ Pc_leaf_d T c a ∧ M.IsOrdinal a ∧ ∃ W, M.mem W T ∧ Pc_jh_d W a x

def pc_base_m {n} (T c x : Term n) : Formula 1 n := Formula.existsMem T
  (.conj (pc_leaf_m T.weaken c.weaken .newest) (.conj (KP.ord0_m .newest)
    (Formula.existsMem T.weaken (pc_jh_m .newest (.bound 1) x.weaken.weaken))))
derive_free_closed pc_base_m

theorem pc_base_delta_l {n} (T c x : Term n) : (pc_base_m T c x).IsDelta0 :=
  .existsMem _ (.conj (pc_leaf_delta_l ..) (.conj (KP.ord0_delta_l _) (.existsMem _ (pc_jh_delta_l ..))))

theorem pc_base_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T c x : Term n) :
    Formula.satisfies ρ (pc_base_m T c x) ↔ Pc_base_d (T.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pc_base_m, Pc_base_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_leaf_sat_l hKP.1, KP.ord0_sat_l hKP, pc_jh_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Pc_apply_d (T F h c x : M.Domain) (k : Rd_sym) : Prop :=
  ∃ a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ d, M.mem d T ∧
  ∃ u, M.mem u T ∧ ∃ v, M.mem v T ∧ ∃ w, M.mem w T ∧
    Pc_node_d T k c a b d ∧ Pc_read_d F h a u ∧ Pc_read_d F h b v ∧ Pc_read_d F h d w ∧ Rd_fun_d k u v w x

/-- 六个局部槽依次装入三个子码和三个子值，外层参数为码、高度、历史、集合界。 -/
def pc_apply_s (k : Rd_sym) : Delta0UnarySchema 4 where
  body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5) (Formula.existsMem (.bound 6)
    (Formula.existsMem (.bound 7) (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 9)
      (.conj (pc_node_m (.bound 10) k (.bound 7) (.bound 5) (.bound 4) (.bound 3))
        (.conj (pc_read_m (.bound 9) (.bound 8) (.bound 5) (.bound 2))
          (.conj (pc_read_m (.bound 9) (.bound 8) (.bound 4) (.bound 1))
            (.conj (pc_read_m (.bound 9) (.bound 8) (.bound 3) .newest)
              (rd_graph_m k (.bound 2) (.bound 1) .newest (.bound 6)))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (pc_node_delta_l ..) (.conj (pc_read_delta_l ..) (.conj (pc_read_delta_l ..)
      (.conj (pc_read_delta_l ..) (rd_graph_delta_l ..))))))))))

def pc_apply_m {n} (T F h c x : Term n) (k : Rd_sym) : Formula 1 n :=
  pred_m (pc_apply_s k).toUnarySchema (Fin.cases c (Fin.cases h (Fin.cases F (fun _ => T)))) x

@[simp] theorem pc_apply_closed_l {n} (T F h c x : Term n) (k : Rd_sym)
    (hT : T.freeSupport = []) (hF : F.freeSupport = []) (hh : h.freeSupport = [])
    (hc : c.freeSupport = []) (hx : x.freeSupport = []) : (pc_apply_m T F h c x k).FreeClosed :=
  pred_m_freeClosed _ _ _ (Fin.cases hc (Fin.cases hh (Fin.cases hF (fun _ => hT)))) hx

theorem pc_apply_delta_l {n} (T F h c x : Term n) (k : Rd_sym) : (pc_apply_m T F h c x k).IsDelta0 :=
  (pc_apply_s k).delta0.bind_l _

theorem pc_apply_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T F h c x : Term n) (k : Rd_sym) :
    Formula.satisfies ρ (pc_apply_m T F h c x k) ↔
      Pc_apply_d (T.eval ρ) (F.eval ρ) (h.eval ρ) (c.eval ρ) (x.eval ρ) k := by
  rw [pc_apply_m, pred_sat_l]
  simp only [pc_apply_s, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_node_sat_l hKP.1, pc_read_sat_l hKP.1, rd_graph_sat_l hKP]
  rfl

def Pc_step_d (T F h c x : M.Domain) : Prop := Pc_base_d T c x ∨ ∃ k, Pc_apply_d T F h c x k

def pc_step_m {n} (T F h c x : Term n) : Formula 1 n :=
  .disj (pc_base_m T c x) (rd_any_m rd_menu_l (pc_apply_m T F h c x))
derive_free_closed pc_step_m

theorem pc_step_delta_l {n} (T F h c x : Term n) : (pc_step_m T F h c x).IsDelta0 :=
  .disj (pc_base_delta_l ..) (rd_any_delta_l _ _ (fun k => pc_apply_delta_l T F h c x k))

theorem pc_step_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T F h c x : Term n) :
    Formula.satisfies ρ (pc_step_m T F h c x) ↔ Pc_step_d (T.eval ρ) (F.eval ρ) (h.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pc_step_m, Pc_step_d, Formula.satisfies_disj_iff, pc_base_sat_l hKP, rd_any_sat_l, pc_apply_sat_l hKP]
  exact or_congr Iff.rfl ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, rd_menu_mem_l k, h⟩⟩

end YesMetaZFC.SetTheory.InnerModel
