import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyPast
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

def Pn_past_d (L i j X P π Y N σ : M.Domain) : Prop :=
  Ic_past_d L i j X P π Y N σ ∧ (P = N ∨ M.mem N P) ∧ ((∃ ρ, Rd_entry_d i ρ L) → M.mem N P)

def pn_past_m {d} (L i j X P π Y N σ : Term d) : Formula 1 d := set[d] ⟪
  ⌜ic_past_m⌝ₚ(⌜L⌝ₛ, ⌜i⌝ₛ, ⌜j⌝ₛ, ⌜X⌝ₛ, ⌜P⌝ₛ, ⌜π⌝ₛ, ⌜Y⌝ₛ, ⌜N⌝ₛ, ⌜σ⌝ₛ) ∧
  (⌜P⌝ₛ = ⌜N⌝ₛ ∨ ⌜N⌝ₛ ∈ ⌜P⌝ₛ) ∧ ((∃ ρ, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ)) → ⌜N⌝ₛ ∈ ⌜P⌝ₛ)⟫
derive_free_closed pn_past_m

theorem pn_past_sat_l (hKP : M.Models KP) {d} (η : Env M d) (L i j X P π Y N σ : Term d) :
    Formula.satisfies η (pn_past_m L i j X P π Y N σ) ↔
      Pn_past_d (L.eval η) (i.eval η) (j.eval η) (X.eval η) (P.eval η) (π.eval η) (Y.eval η) (N.eval η) (σ.eval η) := by
  simp only [pn_past_m, Pn_past_d, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1, ic_past_sat_l hKP, Definitional.Term.eval_weaken]; rfl

structure Pn_history_d (ω Q L C n H : M.Domain) : Prop where
  function : Fn0_d n C H
  rows : ∀ i r, Rd_entry_d i r H → ∃ a X P π ι,
    Pn_cell_d r a X P π ι ∧ Rd_entry_d i a Q ∧ Pn_row_d hZF ω a X P π ι
  past : ∀ i j r s a X P π ι b Y N σ η, Rd_entry_d i r H → Rd_entry_d j s H → M.mem i j →
    Pn_cell_d r a X P π ι → Pn_cell_d s b Y N σ η → Pn_past_d L i j X P π Y N σ

def pn_history_m {d} (ω Q L C n H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜n⌝ₛ, ⌜C⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i r, ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ∃ a X P π ι,
    ⌜pn_cell_m⌝ₚ(r, a, X, P, π, ι) ∧ ⌜rd_entry0_m⌝ₚ(i, a, ⌜Q⌝ₛ) ∧ ⌜pn_row_m⌝ₚ(⌜ω⌝ₛ, a, X, P, π, ι)) ∧
  (∀ i j r s a X P π ι b Y N σ η,
    ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, s, ⌜H⌝ₛ) → i ∈ j →
    ⌜pn_cell_m⌝ₚ(r, a, X, P, π, ι) → ⌜pn_cell_m⌝ₚ(s, b, Y, N, σ, η) →
      ⌜pn_past_m⌝ₚ(⌜L⌝ₛ, i, j, X, P, π, Y, N, σ))⟫
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

/-- 将实际新行及已证明的全前驱关系装入同一有限图。 -/
theorem Pn_history_d.push_l {ω Q L C m H a X P π ι s : M.Domain}
    (h : Pn_history_d hZF ω Q L C m H) (mo : M.IsOrdinal m)
    (next : Pn_row_d hZF ω a X P π ι) (hq : Rd_entry_d m a Q) (hs : Pn_cell_d s a X P π ι) (hC : M.mem s C)
    (past : ∀ i r b Y N σ η, Rd_entry_d i r H → Pn_cell_d r b Y N σ η → Pn_past_d L i m Y N σ X P π) :
    ∃ k G, M.SuccessorOf k m ∧ Pn_history_d hZF ω Q L C k G ∧
      ∀ i t, Rd_entry_d i t G ↔ Rd_entry_d i t H ∨ i = m ∧ t = s := by
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
      exact past i u a₀ X₀ P₀ π₀ ι₀ hi cu

/-- 活动步以真实最大强度更新全部旧行；此前的恒等段沿同一支撑一并接入。 -/
theorem Pn_history_d.active_push_l {ω Q L C n m H r b Y N σ η ρ φ a X P π ι s : M.Domain}
    (h : Pn_history_d hZF ω Q L C m H) (hm : M.SuccessorOf m n) (hn : M.IsOrdinal n)
    (hr : Rd_entry_d n r H) (cell : Pn_cell_d r b Y N σ η) (row : Pn_row_d hZF ω b Y N σ η)
    (hl : Rd_entry_d n ρ L) (increasing : ∀ i α, M.mem i n → Rd_entry_d i α L → M.mem α ρ)
    (next : Pn_row_d hZF ω a X P π ι) (hq : Rd_entry_d m a Q) (hs : Pn_cell_d s a X P π ι) (hC : M.mem s C)
    (inside : M.mem P N) (adjacent : Pn_agree_d Y N σ X P π ρ φ) (strength : Es_strength_d Y ρ X) :
    ∃ k G, M.SuccessorOf k m ∧ Pn_history_d hZF ω Q L C k G ∧
      ∀ i t, Rd_entry_d i t G ↔ Rd_entry_d i t H ∨ i = m ∧ t = s := by
  apply h.push_l hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) hn hm) next hq hs hC
  intro i u a₀ X₀ P₀ π₀ ι₀ hi cu
  rcases (hm i).mp (h.function.bound_l hi).1 with hin | eq
  · obtain ⟨prior, below, _⟩ := h.past i n u r a₀ X₀ P₀ π₀ ι₀ b Y N σ η hi hr hin cu cell
    rcases prior with ⟨e₁, e₂, e₃, no⟩ | ⟨k, α, β, hik, hk, hl', first, previous, exactness⟩
    · subst X₀ P₀ π₀
      exact ⟨Or.inr ⟨n, ρ, φ, Or.inr hin, hm.predecessor_mem, hl, fun ν hv => (no ν hv).elim, adjacent, strength⟩,
        Or.inr inside, fun _ => inside⟩
    · have hαρ := increasing k α hk hl'
      obtain ⟨_, R, S, c, μ, K, mx, my, ready, _, _, emb, _⟩ := row
      have hβφ := ((my.2 β φ).mp ((emb.relation_l I hZF ready.source.omega mx.1 my.1
        previous.right_end adjacent.left_end).mp ((mx.2 α ρ).mpr
          ⟨emb.1.1.input_mem_of_pairMember previous.right_end, emb.1.1.input_mem_of_pairMember adjacent.left_end, hαρ⟩))).2.2
      have member := below.elim (fun eq => eq.symm ▸ inside) (fun mem => previous.target_left N mem P inside)
      exact ⟨Or.inr ⟨k, α, β, hik, (hm k).mpr (Or.inl hk), hl', first,
        previous.trans_l hZF adjacent hαρ hβφ, adjacent.strength_l hZF hαρ exactness⟩, Or.inr member, fun _ => member⟩
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 n u r hi hr
    subst u
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := cu.unique_l cell
    subst a₀ X₀ P₀ π₀ ι₀
    exact ⟨Or.inr ⟨n, ρ, φ, Or.inl rfl, hm.predecessor_mem, hl, fun _ _ => rfl, adjacent, strength⟩,
      Or.inr inside, fun _ => inside⟩

/-- 恒等步沿用同一模型行，故只有尚无支撑的末行允许相等。 -/
theorem Pn_history_d.pad_push_l {ω Q L C n m H r b Y N σ η : M.Domain}
    (h : Pn_history_d hZF ω Q L C m H) (hm : M.SuccessorOf m n) (hn : M.IsOrdinal n)
    (hr : Rd_entry_d n r H) (cell : Pn_cell_d r b Y N σ η) (row : Pn_row_d hZF ω b Y N σ η)
    (hq : Rd_entry_d m b Q) (inactive : ∀ ρ, ¬ Rd_entry_d n ρ L) :
    ∃ k G, M.SuccessorOf k m ∧ Pn_history_d hZF ω Q L C k G ∧
      ∀ i t, Rd_entry_d i t G ↔ Rd_entry_d i t H ∨ i = m ∧ t = r := by
  apply h.push_l hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) hn hm) row hq cell (h.function.bound_l hr).2
  intro i u a X P π ι hi cu
  rcases (hm i).mp (h.function.bound_l hi).1 with hin | eq
  · obtain ⟨prior, below, strict⟩ := h.past i n u r a X P π ι b Y N σ η hi hr hin cu cell
    refine ⟨?_, below, strict⟩
    rcases prior with same | ⟨k, ρ, φ, hik, hk, rest⟩
    · exact Or.inl same
    · exact Or.inr ⟨k, ρ, φ, hik, (hm k).mpr (Or.inl hk), rest⟩
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 n u r hi hr
    subst u
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := cu.unique_l cell
    subst a X P π ι
    exact ⟨Or.inl ⟨rfl, rfl, rfl, inactive⟩, Or.inl rfl, fun ⟨ρ, hρ⟩ => (inactive ρ hρ).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal
