import YesMetaZFC.SetTheory.InnerModel.Computation.Program
import YesMetaZFC.SetTheory.KP.Sigma1

/-! # 程序到 Σ₁ 公式的可执行编译

矩阵只检查有界的计算证书。中间寄存器和循环结果族都显式受同一集合界约束。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_cert_m : {n d : Nat} → Cp_code n → (Fin n → Term d) → Term d → Term d → Formula 1 d
  | _, _, .var i, e, y, _ => Formula.extensionalEq y (e i)
  | _, _, .zero, _, y, _ => Formula.forallMem y .falsum
  | _, _, .op k p q r, e, y, T =>
      Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
        (.conj (cp_cert_m p (fun i => (e i).weaken.weaken.weaken) (.bound 2) T.weaken.weaken.weaken)
          (.conj (cp_cert_m q (fun i => (e i).weaken.weaken.weaken) (.bound 1) T.weaken.weaken.weaken)
            (.conj (cp_cert_m r (fun i => (e i).weaken.weaken.weaken) .newest T.weaken.weaken.weaken)
              (rd_graph_m k (.bound 2) (.bound 1) .newest y.weaken.weaken.weaken))))))
  | _, _, .let1 p q, e, y, T => Formula.existsMem T
      (.conj (cp_cert_m p (fun i => (e i).weaken) .newest T.weaken)
        (cp_cert_m q (Fin.cases .newest (fun i => (e i).weaken)) y.weaken T.weaken))
  | _, _, .bunion p q, e, y, T => Formula.existsMem T (Formula.existsMem T.weaken
      (.conj (cp_cert_m p (fun i => (e i).weaken.weaken) (.bound 1) T.weaken.weaken)
        (.conj (Formula.forallMem (.bound 1) (Formula.existsMem (.bound 1)
          (cp_cert_m q (Fin.cases (.bound 1) (fun i => (e i).weaken.weaken.weaken.weaken)) .newest T.weaken.weaken.weaken.weaken)))
          (.conj (Formula.forallMem .newest (Formula.existsMem (.bound 2)
            (cp_cert_m q (Fin.cases .newest (fun i => (e i).weaken.weaken.weaken.weaken)) (.bound 1) T.weaken.weaken.weaken.weaken)))
            (rd_graph_m .union .newest .newest .newest y.weaken.weaken)))))

@[simp] theorem cp_cons_closed_l {n d} (t : Term d) (e : Fin n → Term d) :
    (∀ i : Fin (n + 1), (Fin.cases t e i : Term d).freeSupport = []) ↔ t.freeSupport = [] ∧ ∀ i, (e i).freeSupport = [] :=
  ⟨fun h => ⟨h 0, fun i => h i.succ⟩, fun h => Fin.cases h.1 h.2⟩

@[simp] theorem cp_cert_closed_l {n d} (p : Cp_code n) (e : Fin n → Term d) (y T : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hy : y.freeSupport = []) (hT : T.freeSupport = []) :
    (cp_cert_m p e y T).FreeClosed := by
  induction p generalizing d with
  | var i => simp -implicitDefEqProofs [cp_cert_m, he, hy]
  | zero => simp -implicitDefEqProofs [cp_cert_m, Definitional.Formula.FreeClosed, hy]
  | op k p q r ih jh kh =>
    simp -implicitDefEqProofs [cp_cert_m, Definitional.Formula.FreeClosed, ih, jh, kh, he, hy, hT]
  | let1 p q ih jh | bunion p q ih jh =>
    simp -implicitDefEqProofs [cp_cert_m, Definitional.Formula.FreeClosed, ih, jh, he, hy, hT]

theorem cp_cert_delta_l {n d} (p : Cp_code n) (e : Fin n → Term d) (y T : Term d) :
    (cp_cert_m p e y T).IsDelta0 := by
  induction p generalizing d with
  | var i => exact .atom _ _ _
  | zero => exact .forallMem _ .falsum
  | op k p q r ih jh kh => exact .existsMem _ (.existsMem _ (.existsMem _
      (.conj (ih ..) (.conj (jh ..) (.conj (kh ..) (rd_graph_delta_l ..))))))
  | let1 p q ih jh => exact .existsMem _ (.conj (ih ..) (jh ..))
  | bunion p q ih jh => exact .existsMem _ (.existsMem _ (.conj (ih ..)
      (.conj (.forallMem _ (.existsMem _ (jh ..)))
        (.conj (.forallMem _ (.existsMem _ (jh ..))) (rd_graph_delta_l ..)))))

theorem cp_env_cons_l {n d} (ρ : Env M d) (t : Term d) (e : Fin n → Term d) :
    (⟨fun i => (Fin.cases t e i : Term d).eval ρ, ρ.free⟩ : Env M (n + 1)) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (t.eval ρ) := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩

theorem cp_cert_sat_l (hKP : M.Models KP) {n d} (p : Cp_code n) (ρ : Env M d)
    (e : Fin n → Term d) (y T : Term d) :
    Formula.satisfies ρ (cp_cert_m p e y T) ↔
      Cp_cert_d p ⟨fun i => (e i).eval ρ, ρ.free⟩ (y.eval ρ) (T.eval ρ) := by
  induction p generalizing d with
  | var i => exact Formula.satisfies_extensionalEq_iff_eq hKP.1 _ _ _
  | zero => simp only [cp_cert_m, Cp_cert_d, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
  | op k p q r ih jh kh =>
    simp only [cp_cert_m, Cp_cert_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      ih, jh, kh, rd_graph_sat_l hKP, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    rfl
  | let1 p q ih jh | bunion p q ih jh =>
    simp only [cp_cert_m, Cp_cert_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_conj_iff, ih, jh, cp_env_cons_l, rd_graph_sat_l hKP,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    rfl

def cp_graph_s {n} (p : Cp_code (n + 1)) : S1_binary n where
  matrix := {
    body := cp_cert_m p (fun i => .bound ⟨i.val + 2, by omega⟩) (.bound 1) .newest
    freeClosed := cp_cert_closed_l _ _ _ _ (fun _ => rfl) rfl rfl
    delta0 := cp_cert_delta_l .. }

theorem cp_matrix_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (x y T : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push T) (cp_graph_s p).matrix.body ↔ Cp_cert_d p (ρ.push x) y T :=
  cp_cert_sat_l hKP _ _ _ _ _

theorem cp_graph_sound_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) {x y : M.Domain}
    (h : (cp_graph_s p).schema.denote ρ x y) : Cp_eval_d p (ρ.push x) y := by
  obtain ⟨T, ht⟩ := ((cp_graph_s p).sat_l ρ x y).mp h
  exact cp_cert_sound_l hKP.1 p _ ((cp_matrix_sat_l hKP p ρ x y T).mp ht)

end YesMetaZFC.SetTheory.InnerModel
