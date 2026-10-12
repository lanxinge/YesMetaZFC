import YesMetaZFC.Model.SetTheory.Internal.TypeExceeds
import YesMetaZFC.Model.SetTheory.Internal.TypeTruthSyntax

/-! # 超过关系的背景原公式

保留真实低层实现、全部原坐标和任意内部有限排列；高度间隙仍为 ν+1<η。
仅重写语法，既不缩减排列，也不预设新类型的最后坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def tp_perm_raw_m {d} (m A π g h : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜m⌝ₛ, ∀ x ∈ ⌜A⌝ₛ,
  ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(i, x, ⌜h⌝ₛ) ↔
    (∃ j ∈ ⌜m⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, j, ⌜π⌝ₛ) ∧ ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(j, x, ⌜g⌝ₛ))⟫
derive_free_closed tp_perm_raw_m

theorem tp_perm_raw_sat_l {d} (ρ : Env M d) (m A π g h : Term d) :
    Formula.satisfies ρ (tp_perm_raw_m m A π g h) ↔ Tp_perm_d K
      (m.eval ρ) (A.eval ρ) (π.eval ρ) (g.eval ρ) (h.eval ρ) := by
  simp only [tp_perm_raw_m, Tp_perm_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff K,
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def ts_at0_m : Formula 1 9 :=
  let p : Fin 9 → Term 9 := Term.bound
  set[9] ⟪∃ A c R r g h π,
    ⌜v_m kpair_convention_l⌝ₚ(⌜p 8⌝ₛ, A) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, A, R) ∧
    ⌜tt_realized_m⌝ₚ(⌜p 0⌝ₛ, c, A, R, ⌜p 4⌝ₛ, r, ⌜p 1⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ) ∧
    ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜p 0⌝ₛ, A) ∧
    ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(h, ⌜p 4⌝ₛ, A) ∧
    ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(r, h) ∧
    (∀ i x, i ∈ ⌜p 2⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, x, ⌜p 3⌝ₛ) ↔ ⌜Formula.orderedPairMem FlatPairing.convention⌝ₚ(i, x, g))) ∧
    ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(π, ⌜p 4⌝ₛ, ⌜p 4⌝ₛ) ∧ ⌜tp_perm_raw_m⌝ₚ(⌜p 4⌝ₛ, A, π, g, h)⟫

theorem ts_at0_closed_l : ts_at0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_at0_m, Definitional.Formula.FreeClosed]

def ts_at_m {d} (ω δ n s m U D w ν : Term d) : Formula 1 d :=
  ts_at0_m.bind (fun i => [ω, δ, n, s, m, U, D, w, ν].get i)

@[simp] theorem ts_at_closed_l {d} (ω δ n s m U D w ν : Term d)
    (hw : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hn : n.freeSupport = []) (hs : s.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hu : w.freeSupport = [])
    (hν : ν.freeSupport = []) : (ts_at_m ω δ n s m U D w ν).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_at0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hδ, hn, hs, hm, hU, hD, hu, hν, fun i => Fin.elim0 i⟩

theorem ts_at_sat_l {d} (ρ : Env M d) (ω δ n s m U D w ν : Term d) :
    Formula.satisfies ρ (ts_at_m ω δ n s m U D w ν) ↔ Ts_at_d hZF
      (ω.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (m.eval ρ) (U.eval ρ) (D.eval ρ) (w.eval ρ) (ν.eval ρ) := by
  simp only [ts_at_m, Formula.satisfies_bind, ts_at0_m, Ts_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_isFunctionFromTo_iff K hZF.1, sx_graph_sat_l I K,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hZF.1, Formula.satisfies_orderedPairMem_iff K,
    Formula.satisfies_isBijectionFromTo_iff I hZF.1, tp_perm_raw_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

def tx_exceeds0_m : Formula 1 12 :=
  let ω := Term.bound 0; let δ := Term.bound 1; let κ := Term.bound 2; let n := Term.bound 3
  let U := Term.bound 4; let D := Term.bound 5; let u := Term.bound 6; let τ := Term.bound 7
  let m := Term.bound 8; let V := Term.bound 9; let W := Term.bound 10; let w := Term.bound 11
  set[12] ⟪
  ⌜κ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜n⌝ₛ ⊆ ⌜m⌝ₛ ∧ (∃ η Y c R s,
    ⌜v_m kpair_convention_l⌝ₚ(η, Y) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) ∧
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
    (∃ ν μ, ⌜Formula.isSuccessor⌝ₚ(μ, ν) ∧ μ ∈ η ∧
      ⌜ts_at_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, s, ⌜m⌝ₛ, ⌜V⌝ₛ, ⌜W⌝ₛ, ⌜w⌝ₛ, ν)))⟫
theorem tx_exceeds0_closed_l : tx_exceeds0_m.FreeClosed := by
  simp -implicitDefEqProofs [tx_exceeds0_m, Definitional.Formula.FreeClosed]

def tx_exceeds_m {d} (ω δ κ n U D u τ m V W w : Term d) : Formula 1 d :=
  tx_exceeds0_m.bind (fun i => [ω, δ, κ, n, U, D, u, τ, m, V, W, w].get i)

@[simp] theorem tx_exceeds_closed_l {d} (ω δ κ n U D u τ m V W w : Term d)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hκ : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hu : u.freeSupport = []) (hτ : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hV : V.freeSupport = []) (hW : W.freeSupport = []) (hw : w.freeSupport = []) :
    (tx_exceeds_m ω δ κ n U D u τ m V W w).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tx_exceeds0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, hδ, hκ, hn, hU, hD, hu, hτ, hm, hV, hW, hw, fun i => Fin.elim0 i⟩

theorem tx_exceeds_sat_l {d} (ρ : Env M d) (ω δ κ n U D u τ m V W w : Term d) :
    Formula.satisfies ρ (tx_exceeds_m ω δ κ n U D u τ m V W w) ↔ Tx_exceeds_d hZF
      (ω.eval ρ) (δ.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ)
      (τ.eval ρ) (m.eval ρ) (V.eval ρ) (W.eval ρ) (w.eval ρ) := by
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m, Tx_exceeds_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_isSuccessor_iff, ts_at_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
