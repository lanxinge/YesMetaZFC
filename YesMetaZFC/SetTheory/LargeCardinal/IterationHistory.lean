import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationTree

/-! # 内部有限下降历史

每一行携带原模型码、原域、目标模型、嵌入及编号。全前驱条件同时保留
共同秩段、缺失子集和模型隶属下降；新行通过一次拼接更新整段历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Pn_cell_d (r a X P π ι : M.Domain) : Prop := ∃ q, Rd_triple_d r X P q ∧ Rd_triple_d q a π ι

def pn_cell_m {d} (r a X P π ι : Term d) : Formula 1 d := set[d] ⟪
  ∃ q, ⌜rd_triple0_m⌝ₚ(⌜r⌝ₛ, ⌜X⌝ₛ, ⌜P⌝ₛ, q) ∧ ⌜rd_triple0_m⌝ₚ(q, ⌜a⌝ₛ, ⌜π⌝ₛ, ⌜ι⌝ₛ)⟫
derive_free_closed pn_cell_m

theorem pn_cell_sat_l (hE : Extensional M) {d} (ρ : Env M d) (r a X P π ι : Term d) :
    Formula.satisfies ρ (pn_cell_m r a X P π ι) ↔
      Pn_cell_d (r.eval ρ) (a.eval ρ) (X.eval ρ) (P.eval ρ) (π.eval ρ) (ι.eval ρ) := by
  simp only [pn_cell_m, Pn_cell_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Pn_cell_d.unique_l {r a X P π ι b Y N σ η : M.Domain}
    (h : Pn_cell_d r a X P π ι) (g : Pn_cell_d r b Y N σ η) : a = b ∧ X = Y ∧ P = N ∧ π = σ ∧ ι = η := by
  obtain ⟨q, hq, hr⟩ := h
  obtain ⟨q', hq', hr'⟩ := g
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hq hq'
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hr hr'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- 行的定义域由源内图实际回收；故固定传递包络能容纳每次新行。 -/
theorem Pn_row_d.cell_l {ω a X P π ι C : M.Domain} (h : Pn_row_d hZF ω a X P π ι)
    (ct : M.TransitiveSet C) (algebra : Sc_algebra_d C) (ha : M.mem a C) (hP : M.mem P C) :
    ∃ r, M.mem r C ∧ Pn_cell_d r a X P π ι := by
  obtain ⟨_, R, S, c, μ, K, _, hn, model, hp, hi, emb, _⟩ := h
  have hX := sc_function_domain_mem_l hZF model.source.omega model.source.transitive hn model.source.theory hp
    (fn0_of_function_l (ZF.modelsKP hZF) emb.1.1)
  obtain ⟨t, ht, pair⟩ := algebra.kpair_l (ct P hP π hp) (ct P hP ι hi)
  obtain ⟨q, hq, triple⟩ := algebra.kpair_l ha ht
  obtain ⟨v, hv, pair'⟩ := algebra.kpair_l hP hq
  obtain ⟨r, hr, triple'⟩ := algebra.kpair_l (ct P hP X hX) hv
  exact ⟨r, hr, q, ⟨v, pair', triple'⟩, t, pair, triple⟩

def Pn_past_d (L i X P π Y N σ : M.Domain) : Prop := ∃ ρ φ, Rd_entry_d i ρ L ∧ M.mem N P ∧
  Pn_agree_d X P π Y N σ ρ φ ∧ Es_strength_d X ρ Y

def pn_past_m {d} (L i X P π Y N σ : Term d) : Formula 1 d := set[d] ⟪
  ∃ ρ φ, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ) ∧ ⌜N⌝ₛ ∈ ⌜P⌝ₛ ∧
    ⌜pn_agree_m⌝ₚ(⌜X⌝ₛ, ⌜P⌝ₛ, ⌜π⌝ₛ, ⌜Y⌝ₛ, ⌜N⌝ₛ, ⌜σ⌝ₛ, ρ, φ) ∧ ⌜pn_strength_m⌝ₚ(⌜X⌝ₛ, ρ, ⌜Y⌝ₛ)⟫
derive_free_closed pn_past_m

theorem pn_past_sat_l (hKP : M.Models KP) {d} (η : Env M d) (L i X P π Y N σ : Term d) :
    Formula.satisfies η (pn_past_m L i X P π Y N σ) ↔
      Pn_past_d (L.eval η) (i.eval η) (X.eval η) (P.eval η) (π.eval η) (Y.eval η) (N.eval η) (σ.eval η) := by
  simp only [pn_past_m, Pn_past_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hKP.1, pn_agree_sat_l hKP,
    pn_strength_sat_l, Definitional.Term.eval_weaken]; rfl

structure Pn_history_d (ω Q L C n H : M.Domain) : Prop where
  function : Fn0_d n C H
  rows : ∀ i r, Rd_entry_d i r H → ∃ a X P π ι,
    Pn_cell_d r a X P π ι ∧ Rd_entry_d i a Q ∧ Pn_row_d hZF ω a X P π ι
  past : ∀ i j r s a X P π ι b Y N σ η, Rd_entry_d i r H → Rd_entry_d j s H → M.mem i j →
    Pn_cell_d r a X P π ι → Pn_cell_d s b Y N σ η → Pn_past_d L i X P π Y N σ

def pn_history_m {d} (ω Q L C n H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜n⌝ₛ, ⌜C⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i r, ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ∃ a X P π ι,
    ⌜pn_cell_m⌝ₚ(r, a, X, P, π, ι) ∧ ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) ∧ ⌜pn_row_m⌝ₚ(⌜ω⌝ₛ, a, X, P, π, ι)) ∧
  (∀ i j r s a X P π ι b Y N σ η,
    ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, s, ⌜H⌝ₛ) → i ∈ j →
    ⌜pn_cell_m⌝ₚ(r, a, X, P, π, ι) → ⌜pn_cell_m⌝ₚ(s, b, Y, N, σ, η) →
      ⌜pn_past_m⌝ₚ(⌜L⌝ₛ, i, X, P, π, Y, N, σ))⟫
derive_free_closed pn_history_m

theorem pn_history_sat_l {d} (ρ : Env M d) (ω Q L C n H : Term d) : Formula.satisfies ρ (pn_history_m ω Q L C n H) ↔
    Pn_history_d hZF (ω.eval ρ) (Q.eval ρ) (L.eval ρ) (C.eval ρ) (n.eval ρ) (H.eval ρ) := by
  simp only [pn_history_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    pn_cell_sat_l hZF.1, pn_row_sat_l hZF, pn_past_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, r, p⟩ => ⟨f, r, p⟩, fun h => ⟨h.function, h.rows, h.past⟩⟩

theorem pn_history_start_l {ω Q L C z o a X P π ι r : M.Domain}
    (hz : ∀ x, ¬ M.mem x z) (ho : M.SuccessorOf o z) (hq : Rd_entry_d z a Q)
    (cell : Pn_cell_d r a X P π ι) (row : Pn_row_d hZF ω a X P π ι) (hr : M.mem r C) :
    ∃ H, Pn_history_d hZF ω Q L C o H ∧ Rd_entry_d z r H := by
  have only i (hi : M.mem i o) : i = z := ((ho i).mp hi).elim (fun hi => (hz i hi).elim) (hZF.1.eq_of_same_members i z)
  obtain ⟨H, fn, spec⟩ := ZF.exists_constantFunction hZF I (source := o) hr
  refine ⟨H, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, ?_, ?_⟩, (spec z r).mpr ⟨ho.predecessor_mem, rfl⟩⟩
  · intro i s hs
    obtain ⟨hi, rfl⟩ := (spec i s).mp hs
    exact ⟨a, X, P, π, ι, cell, (only i hi).symm ▸ hq, row⟩
  · intro i j u v a₀ X₀ P₀ π₀ ι₀ a₁ X₁ P₁ π₁ ι₁ _ hj hij _ _
    exact (hz i (only j (fn.input_mem_of_pairMember hj) ▸ hij)).elim

/-- 全前驱更新只使用实际相邻共同秩段及支撑的严格递增。 -/
theorem Pn_history_d.push_l {ω Q L C n m H r b Y N σ η ρ φ a X P π ι s : M.Domain}
    (h : Pn_history_d hZF ω Q L C m H) (hm : M.SuccessorOf m n) (hn : M.IsOrdinal n)
    (hr : Rd_entry_d n r H) (cell : Pn_cell_d r b Y N σ η) (row : Pn_row_d hZF ω b Y N σ η)
    (hl : Rd_entry_d n ρ L) (increasing : ∀ i α, M.mem i n → Rd_entry_d i α L → M.mem α ρ)
    (next : Pn_row_d hZF ω a X P π ι) (hq : Rd_entry_d m a Q) (hs : Pn_cell_d s a X P π ι) (hC : M.mem s C)
    (inside : M.mem P N) (adjacent : Pn_agree_d Y N σ X P π ρ φ) (strength : Es_strength_d Y ρ X) :
    ∃ k G, M.SuccessorOf k m ∧ Pn_history_d hZF ω Q L C k G ∧
      ∀ i t, Rd_entry_d i t G ↔ Rd_entry_d i t H ∨ i = m ∧ t = s := by
  have mo := KP.successor_isOrdinal (ZF.modelsKP hZF) hn hm
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨G, gf, spec⟩ := it_move_push_l (ZF.modelsKP hZF) (fn0_function_l (ZF.modelsKP hZF) h.function).1
    (fun t ht => ir m (h.function.bound_l ht).1)
  obtain ⟨k, hk⟩ := KP.exists_successor (ZF.modelsKP hZF) m
  have km i : M.mem i k ↔ M.mem i m ∨ i = m := (hk i).trans
    (or_congr Iff.rfl ⟨hZF.1.eq_of_same_members i m, fun e => e ▸ fun _ => Iff.rfl⟩)
  have fn : M.IsSetFunctionFromTo I G k C := ⟨gf, fun i => ⟨fun hi =>
    ((km i).mp hi).elim (fun hi => (h.function.2.1 i hi).elim fun t ht => ⟨t, (spec i t).mpr (Or.inl ht.2)⟩)
      (fun eq => ⟨s, (spec i s).mpr (Or.inr ⟨eq, rfl⟩)⟩), fun ⟨t, ht⟩ =>
    (km i).mpr (((spec i t).mp ht).elim (fun h' => Or.inl (h.function.bound_l h').1) (fun e => Or.inr e.1))⟩, fun i hi => by
    rcases (km i).mp hi with hi | rfl
    · obtain ⟨t, ht, hit⟩ := h.function.2.1 i hi
      exact ⟨t, ht, (spec i t).mpr (Or.inl hit)⟩
    · exact ⟨s, hC, (spec _ s).mpr (Or.inr ⟨rfl, rfl⟩)⟩⟩
  refine ⟨k, G, hk, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, ?_, ?_⟩, spec⟩
  · intro i t ht
    rcases (spec i t).mp ht with ht | ⟨rfl, rfl⟩
    · exact h.rows i t ht
    · exact ⟨a, X, P, π, ι, hs, hq, next⟩
  · intro i j u v a₀ X₀ P₀ π₀ ι₀ a₁ X₁ P₁ π₁ ι₁ hi hj hij cu cv
    rcases (spec j v).mp hj with hj | ⟨rfl, rfl⟩
    · have hi : Rd_entry_d i u H := ((spec i u).mp hi).elim id
        (fun eq => (ir m (mo.transitive j (h.function.bound_l hj).1 m (eq.1 ▸ hij))).elim)
      exact h.past i j u v a₀ X₀ P₀ π₀ ι₀ a₁ X₁ P₁ π₁ ι₁ hi hj hij cu cv
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hs.unique_l cv
      have hi : Rd_entry_d i u H := ((spec i u).mp hi).elim id (fun eq => (ir j (eq.1 ▸ hij)).elim)
      rcases (hm i).mp hij with hin | eq
      · obtain ⟨α, β, hl', hnP, previous, exactness⟩ := h.past i n u r a₀ X₀ P₀ π₀ ι₀ b Y N σ η hi hr hin cu cell
        have hαρ := increasing i α hin hl'
        obtain ⟨_, R, S, c, μ, K, mx, my, ready, _, _, emb, _⟩ := row
        have hβφ := ((my.2 β φ).mp ((emb.relation_l I hZF ready.source.omega mx.1 my.1
          previous.right_end adjacent.left_end).mp ((mx.2 α ρ).mpr
            ⟨emb.1.1.input_mem_of_pairMember previous.right_end, emb.1.1.input_mem_of_pairMember adjacent.left_end, hαρ⟩))).2.2
        exact ⟨α, β, hl', previous.target_left N hnP P inside,
          previous.trans_l hZF adjacent hαρ hβφ, adjacent.strength_l hZF hαρ exactness⟩
      · have eq := hZF.1.eq_of_same_members i n eq
        subst i
        have e := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 n u r hi hr
        subst u
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := cell.unique_l cu
        exact ⟨ρ, φ, hl, inside, adjacent, strength⟩

end YesMetaZFC.SetTheory.LargeCardinal
