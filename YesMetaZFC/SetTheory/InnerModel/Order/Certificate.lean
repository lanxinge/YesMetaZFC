import YesMetaZFC.SetTheory.InnerModel.Order.Formula

/-! # 固定运算菜单的 Δ₀ 构造证书

同一见证集合界住所有中间载体、像集及序关系；菜单仍是固定的十三项原运算。
证书与既有规范追加逐项等价，不把良序性或极小代表的存在放入验证条件。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_add_cert_d (k : Rd_sym) (B U R P V S W T : M.Domain) : Prop :=
  ∃ Y, M.mem Y B ∧ ∃ Q, M.mem Q B ∧ Rw_image_d k U P Y ∧ Rw_rel_d (Rw_cmp_d k U R P) Y Q ∧
    M.IsUnionOfTwo W V Y ∧ Rw_rel_d (Rw_append_d V S Q) W T
def rw_add_cert_m {n} (k : Rd_sym) (B U R P V S W T : Term n) : Formula 1 n :=
  Formula.existsMem B (Formula.existsMem B.weaken
    (.conj (rw_image_m k U.weaken.weaken P.weaken.weaken (.bound 1))
      (.conj (rw_table_m (rw_cmp_s k) U.weaken.weaken R.weaken.weaken P.weaken.weaken (.bound 1) .newest)
        (.conj (rw_union_m W.weaken.weaken V.weaken.weaken (.bound 1))
          (rw_table_m rw_append_s V.weaken.weaken S.weaken.weaken .newest W.weaken.weaken T.weaken.weaken)))))
derive_free_closed rw_add_cert_m
theorem rw_add_cert_delta_l {n} (k : Rd_sym) (B U R P V S W T : Term n) :
    (rw_add_cert_m k B U R P V S W T).IsDelta0 := .existsMem _ (.existsMem _
      (.conj (rw_image_delta_l ..) (.conj (rw_table_delta_l ..) (.conj (rw_union_delta_l ..) (rw_table_delta_l ..)))))
theorem rw_add_cert_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (B U R P V S W T : Term n)
    (hp : Rw_domain_d (U.eval ρ) (P.eval ρ)) : Formula.satisfies ρ (rw_add_cert_m k B U R P V S W T) ↔
      Rw_add_cert_d k (B.eval ρ) (U.eval ρ) (R.eval ρ) (P.eval ρ) (V.eval ρ) (S.eval ρ) (W.eval ρ) (T.eval ρ) := by
  simp only [rw_add_cert_m, Rw_add_cert_d, Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]
  apply exists_congr; intro Y; apply and_congr_right; intro _
  apply exists_congr; intro Q; apply and_congr_right; intro _
  have hp' : Rw_domain_d (U.weaken.weaken.eval ((ρ.push Y).push Q))
      (P.weaken.weaken.eval ((ρ.push Y).push Q)) := by simpa only [Definitional.Term.eval_weaken] using hp
  simp only [Formula.satisfies_conj_iff, rw_image_sat_l hKP _ k _ _ _ hp', rw_table_formula_l hKP, rw_union_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  simp only [Rw_rel_d, rw_cmp_sat_l hKP, rw_append_sat_l hKP.1]
  simp -implicitDefEqProofs [Definitional.Term.eval_weaken]; rfl

def Rw_fold_cert_d : List Rd_sym → M.Domain → M.Domain → M.Domain → M.Domain → M.Domain → M.Domain → M.Domain → M.Domain → Prop
  | [], _, _, _, _, V, S, W, T => W = V ∧ T = S
  | k :: L, B, U, R, P, V, S, W, T => ∃ A, M.mem A B ∧ ∃ Q, M.mem Q B ∧
      Rw_add_cert_d k B U R P V S A Q ∧ Rw_fold_cert_d L B U R P A Q W T
def rw_fold_cert_m {n} (L : List Rd_sym) (B U R P V S W T : Term n) : Formula 1 n :=
  match L with
  | [] => .conj (Formula.extensionalEq W V) (Formula.extensionalEq T S)
  | k :: L => Formula.existsMem B (Formula.existsMem B.weaken
      (.conj (rw_add_cert_m k B.weaken.weaken U.weaken.weaken R.weaken.weaken P.weaken.weaken
        V.weaken.weaken S.weaken.weaken (.bound 1) .newest)
        (rw_fold_cert_m L B.weaken.weaken U.weaken.weaken R.weaken.weaken P.weaken.weaken
          (.bound 1) .newest W.weaken.weaken T.weaken.weaken)))
@[simp] theorem rw_fold_cert_closed_l {n} (L : List Rd_sym) (B U R P V S W T : Term n)
    (hB : B.freeSupport = []) (hU : U.freeSupport = []) (hR : R.freeSupport = []) (hP : P.freeSupport = [])
    (hV : V.freeSupport = []) (hS : S.freeSupport = []) (hW : W.freeSupport = []) (hT : T.freeSupport = []) :
    (rw_fold_cert_m L B U R P V S W T).FreeClosed := by
  induction L generalizing n with
  | nil => simp -implicitDefEqProofs [rw_fold_cert_m, Definitional.Formula.FreeClosed, *]
  | cons k L ih => simp -implicitDefEqProofs [rw_fold_cert_m, Definitional.Formula.FreeClosed, *]
theorem rw_fold_cert_delta_l {n} (L : List Rd_sym) (B U R P V S W T : Term n) :
    (rw_fold_cert_m L B U R P V S W T).IsDelta0 := by
  induction L generalizing n with
  | nil => exact .conj (.atom _ _ _) (.atom _ _ _)
  | cons k L ih => exact .existsMem _ (.existsMem _ (.conj (rw_add_cert_delta_l ..) (ih ..)))
theorem rw_fold_cert_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (L : List Rd_sym) (B U R P V S W T : Term n)
    (hp : Rw_domain_d (U.eval ρ) (P.eval ρ)) : Formula.satisfies ρ (rw_fold_cert_m L B U R P V S W T) ↔
      Rw_fold_cert_d L (B.eval ρ) (U.eval ρ) (R.eval ρ) (P.eval ρ) (V.eval ρ) (S.eval ρ) (W.eval ρ) (T.eval ρ) := by
  induction L generalizing n with
  | nil => simp only [rw_fold_cert_m, Rw_fold_cert_d, Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1]
  | cons k L ih =>
    simp only [rw_fold_cert_m, Rw_fold_cert_d, Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]
    apply exists_congr; intro A; apply and_congr_right; intro _
    apply exists_congr; intro Q; apply and_congr_right; intro _
    have hp' : Rw_domain_d (U.weaken.weaken.eval ((ρ.push A).push Q))
        (P.weaken.weaken.eval ((ρ.push A).push Q)) := by simpa only [Definitional.Term.eval_weaken] using hp
    rw [Formula.satisfies_conj_iff, rw_add_cert_sat_l hKP _ _ _ _ _ _ _ _ _ _ hp', ih _ _ _ _ _ _ _ _ _ hp']
    simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

theorem rw_fold_cert_mono_l {L B B' U R P V S W T} (h : Rw_fold_cert_d (M := M) L B U R P V S W T)
    (hb : M.MemberSubset B B') : Rw_fold_cert_d L B' U R P V S W T := by
  induction L generalizing V S with
  | nil => exact h
  | cons k L ih =>
    obtain ⟨A, ha, Q, hq, ⟨Y, hy, Z, hz, h⟩, hf⟩ := h
    exact ⟨A, hb A ha, Q, hb Q hq, ⟨Y, hb Y hy, Z, hb Z hz, h⟩, ih hf⟩
theorem rw_fold_cert_sound_l {L B U R P V S W T} (h : Rw_fold_cert_d (M := M) L B U R P V S W T) :
    Rw_fold_d L U R P V S W T := by
  induction L generalizing V S with
  | nil => exact h
  | cons k L ih =>
    obtain ⟨A, _, Q, _, ⟨Y, _, Z, _, h⟩, hf⟩ := h
    exact ⟨A, Q, ⟨Y, Z, h⟩, ih hf⟩
theorem rw_fold_cert_exists_l (hKP : M.Models KP) {L U R P V S W T} (h : Rw_fold_d (M := M) L U R P V S W T) :
    ∃ B, Rw_fold_cert_d L B U R P V S W T := by
  induction L generalizing V S with
  | nil => exact ⟨U, h⟩
  | cons k L ih =>
    obtain ⟨A, Q, ⟨Y, Z, hy⟩, hf⟩ := h
    obtain ⟨D, hd⟩ := ih hf
    obtain ⟨B, hb⟩ := kp_finite_cover_l hKP [A, Q, Y, Z, D]
    exact ⟨B, A, (hb A (by simp)).2, Q, (hb Q (by simp)).2,
      ⟨Y, (hb Y (by simp)).2, Z, (hb Z (by simp)).2, hy⟩, rw_fold_cert_mono_l hd (hb D (by simp)).1⟩

end YesMetaZFC.SetTheory.InnerModel
