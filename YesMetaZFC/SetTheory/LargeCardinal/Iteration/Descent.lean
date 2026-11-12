import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySuccessor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemStep
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Coherence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.SetTheory.HereditaryCover

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

/-- 严格秩段下降史保存实际隶属秩段；一般原关系复制史另由 Ic_past_d 表达。 -/
def Pn_past_d (L i j X P π Y N σ : M.Domain) : Prop :=
  ((X = Y ∧ P = N ∧ π = σ ∧ ∀ ρ, ¬ Rd_entry_d i ρ L) ∨
    ∃ k ρ φ, (i = k ∨ M.mem i k) ∧ M.mem k j ∧ Rd_entry_d k ρ L ∧
      (∀ ν, Rd_entry_d i ν L → i = k) ∧ Pn_agree_d X P π Y N σ ρ φ ∧ Es_strength_d X ρ Y) ∧
    (P = N ∨ M.mem N P) ∧ ((∃ ρ, Rd_entry_d i ρ L) → M.mem N P)

def pn_past_m {d} (L i j X P π Y N σ : Term d) : Formula 1 d := set[d] ⟪
  ((⌜X⌝ₛ = ⌜Y⌝ₛ ∧ ⌜P⌝ₛ = ⌜N⌝ₛ ∧ ⌜π⌝ₛ = ⌜σ⌝ₛ ∧
      (∀ ρ, ¬ ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ))) ∨
    (∃ k ρ φ, (⌜i⌝ₛ = k ∨ ⌜i⌝ₛ ∈ k) ∧ k ∈ ⌜j⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(k, ρ, ⌜L⌝ₛ) ∧
      (∀ ν, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ν, ⌜L⌝ₛ) → ⌜i⌝ₛ = k) ∧
      ⌜pn_agree_m⌝ₚ(⌜X⌝ₛ, ⌜P⌝ₛ, ⌜π⌝ₛ, ⌜Y⌝ₛ, ⌜N⌝ₛ, ⌜σ⌝ₛ, ρ, φ) ∧
      ⌜es_strength0_m⌝ₚ(⌜X⌝ₛ, ρ, ⌜Y⌝ₛ))) ∧
  (⌜P⌝ₛ = ⌜N⌝ₛ ∨ ⌜N⌝ₛ ∈ ⌜P⌝ₛ) ∧ ((∃ ρ, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ)) → ⌜N⌝ₛ ∈ ⌜P⌝ₛ)⟫
derive_free_closed pn_past_m

theorem pn_past_sat_l (hKP : M.Models KP) {d} (η : Env M d) (L i j X P π Y N σ : Term d) :
    Formula.satisfies η (pn_past_m L i j X P π Y N σ) ↔
      Pn_past_d (L.eval η) (i.eval η) (j.eval η) (X.eval η) (P.eval η)
        (π.eval η) (Y.eval η) (N.eval η) (σ.eval η) := by
  simp only [pn_past_m, Pn_past_d, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, pn_agree_sat_l hKP, es_strength0_sat_l, Definitional.Term.eval_weaken]; rfl

theorem Pn_past_d.prior_l {L i j X P π Y N σ : M.Domain} (h : Pn_past_d L i j X P π Y N σ) :
    (X = Y ∧ P = N ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X P π Y N σ ρ φ ∧ Es_strength_d X ρ Y := by
  rcases h.1 with ⟨hx,hp,hπ,_⟩ | ⟨_,ρ,φ,_,_,_,_,agree,strong⟩
  · exact Or.inl ⟨hx,hp,hπ⟩
  · exact Or.inr ⟨ρ,φ,agree,strong⟩

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
    (h : Pn_history_d hZF ω Q L C m H)
    (hm : M.SuccessorOf m n) (hn : M.IsOrdinal n)
    (hr : Rd_entry_d n r H) (cell : Pn_cell_d r b Y N σ η) (row : Pn_row_d hZF ω b Y N σ η)
    (hq : Rd_entry_d m b Q) (inactive : ∀ ρ, ¬ Rd_entry_d n ρ L) :
    ∃ k G, M.SuccessorOf k m ∧ Pn_history_d hZF ω Q L C k G ∧
      ∀ i t, Rd_entry_d i t G ↔ Rd_entry_d i t H ∨ i = m ∧ t = r := by
  obtain ⟨b₀, Y₀, N₀, σ₀, η₀, cell₀, hb, _⟩ := h.rows n r hr
  obtain ⟨eb, eY, eN, eσ, eη⟩ := cell₀.unique_l cell
  subst b₀ Y₀ N₀ σ₀ η₀
  apply h.push_l hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) hn hm) row hq cell (h.function.bound_l hr).2
  intro i u a X P π ι hi cu
  rcases (hm i).mp (h.function.bound_l hi).1 with hin | eq
  · obtain ⟨prior, below, strict⟩ := h.past i n u r a X P π ι b Y N σ η hi hr hin cu cell
    refine ⟨?_, below, strict⟩
    rcases prior with same | ⟨k,ρ,φ,hik,hk,hl,first,same⟩
    · exact Or.inl same
    · exact Or.inr ⟨k,ρ,φ,hik,(hm k).mpr (Or.inl hk),hl,first,same⟩
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 n u r hi hr
    subst u
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := cu.unique_l cell
    subst a X P π ι
    exact ⟨Or.inl ⟨rfl,rfl,rfl,inactive⟩, Or.inl rfl, fun ⟨ρ,hρ⟩ => (inactive ρ hρ).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## nice 复制的实际下降一步

固定原树已有的超幂和其中严格较小的正则秩段。最大强度给出两侧共同秩层，
旧图的内部可数性回收整个 Vρ∪{ρ} 上的限制；尝试树及指定种子的小壳调整
实际产生属于旧所属模型的新模型，并逐点保留旧图在该整个集合上的值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_copy_step_l
    {ω κ κ' K K' K₀ K₁ L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' P Rₚ o j₀ ι η D a Q α : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Pn_model_d hZF ω κ' K' Y S)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀) (owner' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₁ N' R₁)
    (agree : Ea_agree_d ω κ X N) (inside : M.MemberSubset N' Y)
    (ob : Sc_branch_d ω N') (op : Sc_power_d N') (oc : Sc_cover_d N')
    (ocl : Sc_inaccessible_closure_d I ω N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (prior : (X = N ∧ Y = N' ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X Y π N N' σ ρ φ ∧ Es_strength_d X ρ N)
    (loc : It_local_d I ω N R₀ κ L F)
    (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L N F) (inaccessible : Sc_inaccessible_d ω N L)
    (hπY : M.mem π Y) (hιY : M.mem ι Y) (ip : M.IsSetInjectionFromTo I ι π ω)
    (hσN : M.mem σ N') (hηN : M.mem η N') (is : M.IsSetInjectionFromTo I η σ ω)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c o j₀)
    (hD : M.mem D P) (rank : Vr_d P α D) (regular : Sc_regular_d P α)
    (hd : Smem_d I a D Q) (hLD : M.mem L D) :
    ∃ B k ξ, M.mem B N' ∧ Pn_row_d hZF ω a D B k ξ ∧
      Es_strength_d N L D ∧ Pn_agree_d N N' σ D B k L L' := by
  obtain ⟨target, branches, hierarchy, power, cover, small, closure⟩ := target
  have image_lt {x y u v} (hx : Rd_entry_d x y σ) (hu : Rd_entry_d u v σ) (hxu : M.mem x u) : M.mem y v :=
    ((h₁.2 y v).mp ((hσ.relation_l I hZF owner.omega h₀.1 h₁.1 hx hu).mp
      ((h₀.2 x u).mpr ⟨hσ.1.1.input_mem_of_pairMember hx, hσ.1.1.input_mem_of_pairMember hu, hxu⟩))).2.2
  have inaccessible' := inaccessible.map_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hσ hLσ
  obtain ⟨reg', sizes'⟩ := ocl L' inaccessible'
  have sizes := (hσ.rank_size_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ).mpr sizes'
  have limit := inaccessible.limit_l (ZF.modelsKP hZF) owner.transitive (owner.algebra_l (ZF.modelsKP hZF)).pair
  have limit' := inaccessible'.limit_l (ZF.modelsKP hZF) owner'.transitive (owner'.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨V, f, hV, hv, hf, bij⟩ := sizes.level
  have input : ∃ ρ φ, Pn_agree_d X Y π N N' σ ρ φ ∧ M.mem κ ρ := by
    rcases prior with ⟨rfl, rfl, rfl⟩ | h
    · obtain ⟨V', hV', hVV⟩ := hσ.1.1.2.2 V hV
      have hv' := (hσ.hierarchy_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ hVV).mp hv
      have copy := loc
      obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp copy
      simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
      exact ⟨L, L', ⟨owner.transitive, owner'.transitive, owner.transitive, owner'.transitive, limit, limit',
        ⟨V, hV, hV, hv, hv, fun _ _ _ => Iff.rfl⟩, ⟨V', hV', hV', hv', hv'⟩, hLσ, hLσ⟩, pre.1.2.2.2.2.1⟩
    · obtain ⟨ρ, φ, coincide, exactness⟩ := h
      exact ⟨ρ, φ, coincide, ea_critical_bound_l hZF source owner agree
        (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).1 coincide.source_limit.1 exactness.2⟩
  obtain ⟨ρ, φ, coincide, hκρ⟩ := input
  obtain ⟨_, agree', maps⟩ := coincide.copy_l hZF source owner target owner' hκρ
    (image_lt hκσ coincide.right_end hκρ)
  obtain ⟨W₀, hW₀, _, w₀, _, points⟩ := coincide.source_rank
  have hκπ := (points κ κ' (w₀.ordinal_subset_l hZF source.transitive hW₀ κ hκρ)).mpr hκσ
  obtain ⟨C, hC, _, iso⟩ := ep_transitive_code_l hZF owner (hv.transitive_l owner.transitive hV) hf bij
  have level : Er_level_d N L V := ⟨hV, hv, C, f, hC, hf, iso⟩
  obtain ⟨P', R', o', j', k, next', mdl', ultra', hk, hLP, hLP', fixed, endpoint, _, _, _,
    pb, ph, pp, pc, ps, pcl, back, countable, models, ⟨KP, ready⟩, KP', ready'⟩ :=
    ep_copy_successor_l hZFC source target owner owner' agree agree' inside branches hierarchy power cover small
      ob op oc hm hn hπ hκπ h₀ h₁ hσ hκσ hLσ hFσ maps loc limit level mdl ultra
  have hP := ready.transitive
  have hP' := ready'.transitive
  have hj := ultra.elementary_l hZF hm.1 mdl.1
  have old_power := (sc_power_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr op
  have old_cover := (sc_cover_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr oc
  have old_branches := ob.pull_l hZF owner.omega owner.transitive owner'.transitive owner.omega_mem h₀ h₁ hσ
  have old_hierarchy := (sc_hierarchy_iff_l hZF source.omega source.transitive target.transitive hm hn hπ).mpr hierarchy
  have old_powers := (sc_power_iff_l hZF source.omega source.transitive target.transitive hm hn hπ).mpr power
  have next : Ep_successor_d hZF ω κ L X R F P Rₚ := by
    obtain ⟨X₀, R₂, P₀, S₀, J, O, Z, A, p, U, V, q, u, C, W, i, e,
      mx, nx, system, lim, model, wc, bij, he, _⟩ := ultra
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx.1 hm.1
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I nx.1 mdl.1
    exact ⟨J, O, Z, A, p, U, V, q, u, C, W, o, e, system, lim, model, mdl, hP, wc, bij, he⟩
  obtain ⟨W, hWN, wN, wP, _, es, _⟩ := loc.rank_agree_l hZFC source owner ready agree old_branches old_power old_cover
    ((sc_hierarchy_iff_l hZF source.omega source.transitive hP hm mdl hj).mp old_hierarchy)
    ((sc_power_iff_l hZF source.omega source.transitive hP hm mdl hj).mp old_powers) sizes limit next strength
  have loc' := loc.map_l hZF owner.omega h₀.1 h₁.1 hσ
    (hσ.omega_l I hZF owner.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hκσ hLσ hFσ
  have strength' := strength.map_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hσ owner'.theory hκσ hLσ hFσ
  obtain ⟨W', hWN', wN', wP', _, _, same⟩ := loc'.rank_agree_l hZFC target owner' ready' agree' ob op oc ph pp sizes' limit' next' strength'
  have copy := inaccessible'
  obtain ⟨_, _, above⟩ := copy
  have hωL' : M.mem ω L' := (Formula.satisfies_mem_iff _ _ _).mp ((Formula.satisfies_conj_iff _ _ _).mp above).1
  obtain ⟨KN, ow⟩ := owner'.rebase_l (hσ.1.1.output_mem_of_pairMember hLσ) (limit'.1.transitive ω hωL')
    (sc_ordinal_small_l hZF owner'.omega owner'.transitive h₁ owner'.theory (hσ.1.1.output_mem_of_pairMember hLσ) limit'.1)
  -- 给共同秩层加入支撑端点，整张限制一次回收，随后小壳保持同一端点。
  obtain ⟨C₀, f₀, _, hf₀, iso₀⟩ := wP.code
  obtain ⟨U, f, hU, hf, us, uf⟩ := sc_insert_enumeration_l hZF ready.omega hP mdl ready.theory
    ready.omega_mem ready.cardinal_mem ready.below wP.member hf₀ ready.cardinal_mem (iso₀.bijection_l (ZF.modelsKP hZF))
  have wt := wP.hierarchy.transitive_l hP wP.member
  have ut : M.TransitiveSet U := fun x hx y hy => (us y).mpr (Or.inl
    (((us x).mp hx).elim (fun hx => wt x hx y hy) (fun eq => wP.hierarchy.ordinal_subset_l hZF hP wP.member y (eq ▸ hy))))
  obtain ⟨_, _, sameU, _⟩ := models U f ut hf uf
  obtain ⟨_, τ, hτ, τs⟩ := ep_copy_countable_restriction_l hZF ready ow ready'
    (fun μ hμ => (same μ hμ).subset_l) mdl mdl' hk owner.transitive h₀ h₁ hσ hσN hηN is limit.1 hLσ
    (reg' ω hωL') fixed ut hf uf
  obtain ⟨W₀, hW₀, hWW⟩ := hσ.1.1.2.2 W hWN
  have eq := ((hσ.hierarchy_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ hWW).mp wN).unique_l
    hZF owner'.transitive hW₀ hWN' wN'
  subst W₀
  have low x y (hx : M.mem x U) (hxy : Rd_entry_d x y k) : M.mem y W' ∨ y = L' := by
    have hs := (sameU x y hx).mp hxy
    rcases (us x).mp hx with hx | rfl
    · exact Or.inl (((h₁.2 y W').mp ((hσ.relation_l I hZF owner.omega h₀.1 h₁.1 hs hWW).mp
        ((h₀.2 x W).mpr ⟨owner.transitive W hWN x hx, hWN, hx⟩))).2.2)
    · exact Or.inr (hσ.1.1.1.2 x y L' hs hLσ)
  -- 原树的严格秩段先取复制像；内部正则性和旧域可数编号均由实际图传输。
  obtain ⟨B₀, G, hB₀, hG, cert⟩ := rank
  have hα := sc_function_domain_mem_l hZF ready.omega hP mdl ready.theory hG (cert D hD).2.1
  have rank : Vr_d P α D := ⟨B₀, G, hB₀, hG, cert⟩
  have dt := rank.transitive_l hP hD
  have hωD := rank.subset_mem_l hP hD hLD ready.omega_mem ready.below
  have hωα := rank.ordinal_height_l hZF hP hD (ready.omega.isOrdinal (ZF.modelsKP hZF)) hωD
  have hαl := sc_omega_bound_limit_l hZF ready.omega hP mdl ready.theory ready.omega_mem hα
    (cert D hD).1 ⟨ω, hωα⟩ (regular ω hωα)
  obtain ⟨hWD, wD⟩ := rank.rank_l hZF hP hD hαl hLD wP.member wP.hierarchy
  have hLα := rank.ordinal_height_l hZF hP hD limit.1 hLD
  have wd := (rank.compare_l hZF hP hD wP.member wP.hierarchy ((cert D hD).1.transitive L hLα)).1
  have ud : M.MemberSubset U D := fun x hx => ((us x).mp hx).elim (wd x) (fun eq => eq ▸ hLD)
  obtain ⟨β, _, hαβ⟩ := hk.1.1.2.2 α hα
  obtain ⟨A, a', Q', r, hA, ra, regularA, hDA, modelA, rs, er⟩ :=
    ep_rank_restriction_l hZF ready ready' mdl mdl' hk hD rank regular hd hαβ
  have hLA := ((mdl'.2 L' A).mp ((hk.relation_l I hZF ready.omega mdl.1 mdl'.1 endpoint hDA).mp
    ((mdl.2 L D).mpr ⟨ready.cardinal_mem, hD, hLD⟩))).2.2
  have hLβ := ra.ordinal_height_l hZF hP' hA limit'.1 hLA
  have bo : M.IsOrdinal β := by obtain ⟨_, _, _, _, cert⟩ := ra; exact (cert A hA).1
  have wa := (ra.compare_l hZF hP' hA wP'.member wP'.hierarchy (bo.transitive L' hLβ)).1
  obtain ⟨hPP, ξ, hξ, pξ⟩ := countable ι η hπY hιY ip hσN hηN is
  have hDP := hP' P hPP D hD
  obtain ⟨ζ, hζ, dζ⟩ := ((Sc_index_d.of_injection_l (ZF.modelsKP hZF) (ready.omega.isOrdinal (ZF.modelsKP hZF)) pξ).mono_l
    (hP D hD)).restrict_l hZF ready'.omega hP' mdl' ready'.theory hDP ready'.omega_mem hξ
  have prescribed x y (hxy : Rd_entry_d x y τ) : Rd_entry_d x y r :=
    (rs.2 x y).mpr ⟨ud x ((τs.2 x y).mp hxy).1, ((τs.2 x y).mp hxy).2⟩
  obtain ⟨B, e, T, j, s, ζ, J, hBN, hBP, bt, mb, _, _, sb, bb, bh, bp, bc, bs, bcl,
    wb, _, db, hs, hζ, elem, ct, keep⟩ := ep_skolem_rank_step_l hZF ready' ow ps back pb ph pp wP'
      hA ra regularA wa hLA hDP dt hd modelA hτ hζ dζ er prescribed
  obtain ⟨Z, hZ, zB⟩ := bh L' sb.cardinal_mem limit'.1
  have eq := vr_cross_l hZF hP' bt wP'.member hZ wP'.hierarchy zB wb
    (fun A _ t ht _ => hP' B hBP t ht)
  subst Z
  have exactness : Es_strength_d N L D := by
    refine ⟨fun β hβ x hx sub => rank.subset_mem_l hP hD (dt L hLD β hβ) (es.1 β hβ x hx sub) sub, ?_⟩
    obtain ⟨x, hx, sub, missing⟩ := es.2
    exact ⟨x, hx, sub, fun hxD => missing (hP D hD x hxD)⟩
  have kept x y (hx : M.mem x W ∨ x = L) (hxy : Rd_entry_d x y σ) : Rd_entry_d x y s := by
    have hxU := (us x).mpr hx
    have hxyk := (sameU x y hxU).mpr hxy
    exact keep x y ((τs.2 x y).mpr ⟨hxU, hxyk⟩) (low x y hxU hxyk)
  have adjacent : Pn_agree_d N N' σ D B s L L' := by
    refine ⟨owner.transitive, owner'.transitive, dt, bt, limit, limit',
      ⟨W, hWN, hWD, wN, wD, fun x y hx => ⟨kept x y (Or.inl hx), ?_⟩⟩,
      ⟨W', hWN', hZ, wN', zB⟩, hLσ, kept L L' (Or.inr rfl) hLσ⟩
    intro hxy
    obtain ⟨v, _, hxv⟩ := hσ.1.1.2.2 x (owner.transitive W hWN x hx)
    exact elem.1.1.1.2 x v y (kept x v (Or.inl hx) hxv) hxy ▸ hxv
  have row : Pn_row_d hZF ω a D B s ζ := ⟨dt, Q, T, e, L', J, hd, mb,
    ⟨sb, bb, bh, bp, bc, bs, bcl (pcl closure)⟩, hs, hζ, elem, ct⟩
  exact ⟨B, s, ζ, hBN, row, exactness, adjacent⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树的严格秩段自动接入下降复制

前驱临界点的位置由旧缺失子集推出。原边的秩限制提供指定的实际超幂，
原强度与不可达性随截断保留；递归行自身提供复制所需的全部目标性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_cut_step_l
    {ω κ K K₀ K₁ L F X R N S P T c o j α A β B δ D γ a b d Q Q₀ Q₁ Y Z π σ ι η : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N S)
    (next : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K₁ P T) (mx : Smem_d I c X R)
    (mp : Smem_d I o P T) (agree : Ea_agree_d ω κ X N) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c o j)
    (hA : M.mem A X) (ra : Vr_d X α A) (ga : Sc_regular_d X α) (hωA : M.mem ω A)
    (hB : M.mem B N) (rb : Vr_d N β B) (gb : Sc_regular_d N β) (hLB : M.mem L B) (hFB : M.mem F B)
    (hD : M.mem D P) (rd : Vr_d P δ D) (gd : Sc_regular_d P δ) (hLD : M.mem L D)
    (ma : Smem_d I a A Q) (mb : Smem_d I b B Q₀) (md : Smem_d I d D Q₁)
    (image : Rd_entry_d α γ j) (decrease : M.mem δ γ)
    (loc : It_local_d I ω N S κ L F) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L N F)
    (inaccessible : Sc_inaccessible_d ω N L)
    (left : Pn_row_d hZF ω a A Y π ι) (right : Pn_row_d hZF ω b B Z σ η)
    (inside : M.MemberSubset Z Y)
    (prior : (A = B ∧ Y = Z ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d A Y π B Z σ ρ φ ∧ Es_strength_d A ρ B) :
    ∃ C τ ξ L', M.mem C Z ∧ Pn_row_d hZF ω d D C τ ξ ∧ Es_strength_d B L D ∧
      Pn_agree_d B Z σ D C τ L L' := by
  obtain ⟨ta, R₂, S₂, e, μ, J, ma₀, my, sy, hp, hi, ep, ip⟩ := left
  obtain ⟨bt, R₃, S₃, f, ν, J', mb₀, mz, sz, hs, he, es, is⟩ := right
  obtain ⟨_, rfl⟩ := smdl_unique_l I ma₀.1 ma.1
  obtain ⟨_, rfl⟩ := smdl_unique_l I mb₀.1 mb.1
  have copy := loc
  obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hκL : M.mem κ L := pre.1.2.2.2.2.1
  have hκB := bt L hLB κ hκL
  have hωB := rb.subset_mem_l owner.transitive hB hκB owner.omega_mem owner.below
  have limit := (owner.rank_height_l hZF hB rb gb hωB).2
  have ko := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).1
  have hκA : M.mem κ A := by
    rcases prior with ⟨eq, _, _⟩ | ⟨ρ, φ, common, exactness⟩
    · exact eq.symm ▸ hκB
    · obtain ⟨x, hx, sub, missing⟩ := exactness.2
      have bound := ea_critical_bound_l hZF source owner agree ko common.source_limit.1
        ⟨x, source.transitive A hA x hx, sub, fun hxN => missing
          (rb.subset_mem_l owner.transitive hB (es.1.1.input_mem_of_pairMember common.right_end) hxN sub)⟩
      obtain ⟨W, hw, _, rank, _⟩ := common.source_rank
      exact ta W hw κ (rank.ordinal_subset_l hZF ta hw κ bound)
  obtain ⟨KB, sb⟩ := owner.rank_l hZF hB rb limit gb hωB mb hκB ko owner.below
  have localB := loc.rank_l hZF owner hB rb limit hκB hLB hFB ⟨_, mb⟩
  have inaccessibleB := inaccessible.rank_l hZF owner.transitive (owner.algebra_l (ZF.modelsKP hZF)).pair hB rb limit hLB
  obtain ⟨κ', hκZ, ek⟩ := es.1.1.2.2 κ hκB
  obtain ⟨L', _, el⟩ := es.1.1.2.2 L hLB
  obtain ⟨F', _, ef⟩ := es.1.1.2.2 F hFB
  have sizes := (es.rank_size_l hZF owner.omega bt sz.source.transitive mb mz el).mpr
    (sz.inaccessible L' (inaccessibleB.map_l hZF owner.omega bt sz.source.transitive mb mz es el)).2
  obtain ⟨W, q, hw, wr, hq, bij⟩ := sizes.level
  obtain ⟨U, hu, _, iso⟩ := ep_transitive_code_l hZF sb (wr.transitive_l bt hw) hq bij
  have level : Er_level_d B L W := ⟨hw, wr, U, q, hu, hq, iso⟩
  have ll := inaccessibleB.limit_l (ZF.modelsKP hZF) bt (sb.algebra_l (ZF.modelsKP hZF)).pair
  have exactB := strength.rank_l hZF sb owner.transitive hB rb limit hLB hFB ll hκL level
  have powerB := (sc_power_iff_l hZF owner.omega bt sz.source.transitive mb mz es).mpr sz.power
  obtain ⟨V, hv, powers⟩ := powerB KB sb.finite.mem_l
  have ab := owner.rank_agree_l hZF hB rb limit hκB
  have full : Ea_agree_d ω κ B X := fun n D A hn hd sub =>
    (ab n D A hn hd sub).trans (agree n D A hn hd sub).symm
  have family := (localB.measures_l hZF sb.omega (sb.read_source_l hZF) sb.code sb.theory
    (sf_finite_power_l hZF sb.omega sb.transitive sb.code sb.theory (sb.finite_l (ZF.modelsKP hZF)) hv powers)).transfer_l full
  have coherent := (localB.coherent_l hZF (sb.read_source_l hZF) sb.code).transfer_l hZF full
  have lo := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).2
  obtain ⟨la, KA, a', R', γ', V', v, S', j', sa, code, _, eαγ, hV, rv, gv, mv, edge, _, _⟩ :=
    it_ultra_rank_l hZFC source family coherent
      mx mp ultra hA ra ga hκA ko
  have eq := (ultra.elementary_l hZF mx.1 mp.1).1.1.1.2 α γ' γ eαγ image
  subst γ'
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 code ma
  have aa := source.rank_agree_l hZF hA ra la hκA
  have cut_agree : Ea_agree_d ω κ A B := fun n D A hn hd sub =>
    (aa n D A hn hd sub).trans ((agree n D A hn hd sub).trans (ab n D A hn hd sub).symm)
  have ek' : Rd_entry_d κ κ' π := by
    rcases prior with ⟨_, _, eq⟩ | ⟨ρ, φ, common, exactness⟩
    · exact eq.symm ▸ ek
    · have bound := ea_critical_bound_l hZF sa sb cut_agree ko common.source_limit.1 exactness.2
      obtain ⟨W, hw, _, rank, _, points⟩ := common.source_rank
      exact (points κ κ' (rank.ordinal_subset_l hZF ta hw κ bound)).mpr ek
  have above := fun x hx => (es.ordinal_le_l hZF owner.omega bt sz.source.transitive mb mz ek ko) x (owner.below x hx)
  have ko' := es.ordinal_l hZF owner.omega bt sz.source.transitive mb mz ek ko
  obtain ⟨KZ, sz'⟩ := sz.source.rebase_l hκZ above
    (sc_ordinal_small_l hZF owner.omega sz.source.transitive mz sz.source.theory hκZ ko')
  have hκY := ep.1.1.output_mem_of_pairMember ek'
  obtain ⟨KY, sy'⟩ := sy.rebase_l hZF hκY above
    (sc_ordinal_small_l hZF owner.omega sy.source.transitive my sy.source.theory hκY ko')
  have hωV : M.mem ω V' := by
    have emb := edge.elementary_l hZF ma.1 mv.1
    exact emb.1.1.output_mem_of_pairMember
      (emb.omega_l I hZF owner.omega ta (edge.transitive_l hZF mv.1) ma mv hωA)
  have lv := (next.rank_height_l hZF hV rv gv hωV).2
  obtain ⟨hdV, rankD⟩ := rv.rank_l hZF next.transitive hV lv
    (rv.ordinal_subset_l hZF next.transitive hV δ decrease) hD rd
  have regularD : Sc_regular_d V' δ := fun μ hm q hq => gd μ hm q (next.transitive V' hV q hq)
  obtain ⟨C, τ, ξ, hc, row, exactness, common⟩ := pn_copy_step_l hZFC sa sy' sb sz' cut_agree inside
    sz.branches sz.power sz.cover sz.inaccessible ma my ep mb mz es ek el ef prior localB exactB inaccessibleB
    hp hi ip hs he is mv edge hdV rankD regularD md hLD
  exact ⟨C, τ, ξ, L', hc, row, exactness, common⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际秩段列上的有限下降历史延伸

每一步使用同一工作树已有的前驱、超幂及严格高度下降，自动读取历史中的两个旧行并生成下一行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)

/-- 每一段合法历史的下一步由原树数据构造，没有额外的可延伸性前提。 -/
theorem pn_history_active_l
    {ω c T Q G E L A D C n m H : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (drop : ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A → Rd_entry_d j β A →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ)
    (history : Pn_history_d (ZFC.models_zf_l hZFC) ω D L C m H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (ct : M.TransitiveSet C) (algebra : Sc_algebra_d C)
    (codes : ∀ i a, Rd_entry_d i a D → M.mem a C) (active : ∃ ρ, Rd_entry_d n ρ L) :
    ∃ l J, M.SuccessorOf l m ∧ Pn_history_d (ZFC.models_zf_l hZFC) ω D L C l J ∧
      ∀ i r, Rd_entry_d i r H → Rd_entry_d i r J := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hω := nice.tree.omega
  obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
  have eq := hZF.1.eq_of_same_members m₀ m fun x => (hm₀ x).trans (hm x).symm
  subst m₀
  obtain ⟨k, b, a, d, j, p, κ, ρ, F, N, S, X, R, pred, hb, ha, hd, hj, hp, payload, mn, _, rawModel,
    raw, strength, inaccessible, hl⟩ := nice.step_l hZF hmω hm active
  obtain ⟨N₁,S₁,mn₁,nt⟩ := cuts.models n b hb
  obtain ⟨en,es⟩ := smdl_unique_l I mn₁.1 mn.1
  subst N₁ S₁
  obtain ⟨N₀, S₀, K₀, mn₀, owner₀⟩ := (nice.tree.sources n b hb).mem_l hZF
    ⟨N,S,mn,nt⟩
  obtain ⟨en, es⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ S₀
  obtain ⟨X₁,R₁,mx,xt⟩ := cuts.models k a ha
  obtain ⟨ex,er⟩ := smdl_unique_l I mx.1 rawModel
  subst X₁ R₁
  obtain ⟨X₀, R₀, K₁, mx₀, parent₀⟩ := (nice.tree.sources k a ha).mem_l hZF
    ⟨X,R,mx,xt⟩
  obtain ⟨ex, er⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  obtain ⟨P,U,mp,pt⟩ := cuts.models m d hd
  obtain ⟨P₀,U₀,K₂,mp₀,next⟩ := (nice.tree.sources m d hd).mem_l hZF ⟨P,U,mp,pt⟩
  obtain ⟨ep,eu⟩ := smdl_unique_l I mp₀.1 mp.1
  subst P₀ U₀
  obtain ⟨loc,agree,ultra⟩ := It_active_d.read_l hZF owner₀ parent₀ mn mx mp pt payload raw
  have ko := (loc.ordinals_l (ZF.modelsKP hZF) owner₀.transitive owner₀.code).1
  have locality := loc
  obtain ⟨_,hκ,_,_,_⟩ := locality
  obtain ⟨K₃, owner⟩ := owner₀.rebase_l hκ
    (by obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner₀.code).mp loc
        simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
        exact ko.transitive ω pre.1.2.2.1)
    (sc_ordinal_small_l hZF hω owner₀.transitive mn owner₀.theory hκ ko)
  obtain ⟨K₄, parent⟩ := agree.subset_l.alphabet_l hZF owner parent₀ ko
  obtain ⟨r, hrC, hr⟩ := history.function.2.1 n hm.predecessor_mem
  obtain ⟨b', V, Z, σ, η, cell, hb', row⟩ := history.rows n r hr
  obtain ⟨s, hsC, hs⟩ := history.function.2.1 k pred.1
  obtain ⟨a', W, Y, π, ι, cell', ha', row'⟩ := history.rows k s hs
  obtain ⟨β, hβ⟩ := (cuts.height_domain n).mp hn
  obtain ⟨α, hα⟩ := (cuts.height_domain k).mp (hω.transitive (ZF.modelsKP hZF) m hmω k pred.1)
  obtain ⟨δ, hδ⟩ := (cuts.height_domain m).mp hmω
  obtain ⟨d', hd'⟩ := (cuts.code_domain m).mp hmω
  obtain ⟨V₀, V₁, mv₀, hV, rv, gv, hωV⟩ := cuts.ranks n b b' β N S hb hb' hβ mn
  obtain ⟨W₀, W₁, mw₀, hW, rw, gw, hωW⟩ := cuts.ranks k a a' α X R ha ha' hα mx
  obtain ⟨B, B₁, mb, hB, rb, gb, _⟩ := cuts.ranks m d d' δ P U hd hd' hδ mp
  have row₀ := row
  have row₁ := row'
  obtain ⟨_, V₂, V₃, c₁, μ, J₀, mv, mz, sz, _⟩ := row₀
  obtain ⟨_, W₂, W₃, c₂, ν, J₁, mw, my, sy, _⟩ := row₁
  obtain ⟨ev, es⟩ := smdl_unique_l I mv₀.1 mv.1
  subst V₀ V₁
  obtain ⟨ew, er⟩ := smdl_unique_l I mw₀.1 mw.1
  subst W₀ W₁
  obtain ⟨hρ, hF⟩ := cuts.contains n p κ ρ F b' V V₂ hp payload hb' mv
  obtain ⟨l, sl, hlω⟩ := hω.1.2 m hmω
  have hρB := cuts.next n m p κ ρ F d' B B₁ hm hp payload hd' mb
  obtain ⟨γ, image, decrease⟩ := drop n m k j p κ ρ F α δ hm pred hj hp payload hα hδ
  have previous : M.MemberSubset Z Y ∧
      ((W = V ∧ Y = Z ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d W Y π V Z σ ρ φ ∧ Es_strength_d W ρ V) := by
    rcases (hm k).mp pred.1 with hk | eq
    · have prior := history.past k n s r a' W Y π ι b' V Z σ η hs hr hk cell' cell
      exact ⟨prior.2.1.elim (fun eq => fun x hx => eq.symm ▸ hx) (fun hz => sy.source.transitive Z hz), prior.prior_l⟩
    · have eq := hZF.1.eq_of_same_members k n eq
      subst k
      have eq := (fn0_function_l (ZF.modelsKP hZF) history.function).1.2 n s r hs hr
      subst s
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := cell'.unique_l cell
      exact ⟨fun _ h => h, Or.inl ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨B', τ, ξ, φ, hBZ, new, exactness, adjacent⟩ := pn_cut_step_l hZFC parent owner next mx mp
    (fun n D A hn hd sub => (agree n D A hn hd sub).symm) ultra hW rw gw hωW hV rv gv hρ hF hB rb gb hρB
    mw mv mb image decrease loc strength inaccessible row' row previous.1 previous.2
  have cell₀ := cell
  obtain ⟨u, path, _⟩ := cell₀
  obtain ⟨v, pv, pr⟩ := path
  have hZC := (pv.mem_l M ct (pr.mem_l M ct hrC).2).1
  obtain ⟨s', hs', cell''⟩ := new.cell_l hZF ct algebra (codes m d' hd') (ct Z hZC B' hBZ)
  obtain ⟨l, J, succ, result, entries⟩ := history.active_push_l hZF hm (hω.members_areOrdinals (ZF.modelsKP hZF) n hn)
    hr cell row hl (fun i ρ hi hρ => nice.increasing i n ρ _ hρ hl hi) new hd' cell'' hs' hBZ adjacent exactness
  exact ⟨l, J, succ, result, fun i r hr => (entries i r).mpr (Or.inl hr)⟩
/-- 统一下一步：真实扩展器严格缩小模型，空操作保存已保持的同一秩段。 -/
theorem pn_history_extend_l {ω c T Q G E L A D C n m H : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (pads : ∀ i j p, M.SuccessorOf j i → Rd_entry_d i p E → (∀ x, ¬ M.mem x p) →
      ∀ a, Rd_entry_d i a D ↔ Rd_entry_d j a D)
    (drop : ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A → Rd_entry_d j β A →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ)
    (history : Pn_history_d (ZFC.models_zf_l hZFC) ω D L C m H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (ct : M.TransitiveSet C) (algebra : Sc_algebra_d C)
    (codes : ∀ i a, Rd_entry_d i a D → M.mem a C) :
    ∃ l J, M.SuccessorOf l m ∧ Pn_history_d (ZFC.models_zf_l hZFC) ω D L C l J ∧
      ∀ i r, Rd_entry_d i r H → Rd_entry_d i r J := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  by_cases active : ∃ ρ, Rd_entry_d n ρ L
  · exact pn_history_active_l hZFC nice cuts drop history hn hm ct algebra codes active
  · obtain ⟨m₀, sm, hmω⟩ := nice.tree.omega.1.2 n hn
    have eq := sm.eq hZF.1 hm
    subst m₀
    obtain ⟨p, hp⟩ := (nice.tree.move_domain n).mpr ⟨m, hmω, hm⟩
    have empty : ∀ x, ¬ M.mem x p := (nice.tree.move_cases_l hZF hp).elim id (fun ⟨κ, ρ, F, pay⟩ =>
      (active ⟨ρ, (nice.levels n ρ).mpr ⟨p, κ, F, hp, pay⟩⟩).elim)
    obtain ⟨r, _, hr⟩ := history.function.2.1 n hm.predecessor_mem
    obtain ⟨a, X, P, π, ι, cell, ha, row⟩ := history.rows n r hr
    obtain ⟨l, J, sl, hist, kept⟩ := history.pad_push_l hZF hm
      (nice.tree.omega.members_areOrdinals (ZF.modelsKP hZF) n hn)
      hr cell row ((pads n m p hm hp empty a).mp ha) (fun ρ hρ => active ⟨ρ, hρ⟩)
    exact ⟨l, J, sl, hist, fun i r hr => (kept i r).mpr (Or.inl hr)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 恒等段上的秩段保持

原下降高度在恒等段仍严格下降。下降模型递归则在恒等段保留上一个秩段；
遇到真实扩展器才使用新的原秩段。保留的高度始终不小于原高度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def It_hold_d (Q A i r : M.Domain) : Prop := ∃ c α β,
  Rd_entry_d i c Q ∧ Rd_entry_d r c Q ∧ Rd_entry_d i α A ∧ Rd_entry_d r β A ∧ (α = β ∨ M.mem α β)
private def it_hold_m {d} (Q A i r : Term d) : Formula 1 d := set[d] ⟪∃ c α β,
  ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜r⌝ₛ, c, ⌜Q⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, α, ⌜A⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜r⌝ₛ, β, ⌜A⌝ₛ) ∧ (α = β ∨ α ∈ β)⟫
derive_free_closed it_hold_m
private theorem it_hold_sat_l (hE : Extensional M) {d} (η : Env M d) (Q A i r : Term d) :
    Formula.satisfies η (it_hold_m Q A i r) ↔ It_hold_d (Q.eval η) (A.eval η) (i.eval η) (r.eval η) := by
  simp only [it_hold_m, It_hold_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_cut_normalize_l {ω c T Q G E L A D o : M.Domain}
    (nice : It_pnice_d hZF ω c ω T Q G E L) (cuts : It_cut_d hZF ω ω Q E A D)
    (ho : ∀ x, ¬ M.mem x o)
    (drop : ∀ i j k f α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d k α A → Rd_entry_d j β A → ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ) :
    ∃ A' D', It_cut_d hZF ω ω Q E A' D' ∧
      (∀ α, Rd_entry_d o α A' ↔ Rd_entry_d o α A) ∧
      (∀ a, Rd_entry_d o a D' ↔ Rd_entry_d o a D) ∧
      (∀ i j p, M.SuccessorOf j i → Rd_entry_d i p E → (∀ x, ¬ M.mem x p) →
        ∀ a, Rd_entry_d i a D' ↔ Rd_entry_d j a D') ∧
      ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
        Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A' → Rd_entry_d j β A' →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ := by
  have actual i b (hb : Rd_entry_d i b Q) := (nice.tree.sources i b hb).mem_l hZF
    (cuts.models i b hb)
  have hw := nice.tree.omega
  have self i (hi : M.mem i ω) : It_hold_d Q A i i := by
    obtain ⟨c, hc⟩ := (nice.tree.diagram.model_domain i).mp hi
    obtain ⟨α, hα⟩ := (cuts.height_domain i).mp hi
    exact ⟨c, α, α, hc, hc, hα, hα, Or.inl rfl⟩
  let η : Env M 4 := ⟨Fin.cases ω (Fin.cases E (Fin.cases A (fun _ => Q))), fun _ => ω⟩
  let B : BinarySchema 4 := { body := it_hold_m (.bound 5) (.bound 4) (.bound 1) .newest }
  let φ : UnarySchema 6 := { body := set[7] ⟪
    (⌜(Term.newest : Term 7)⌝ₛ = ⌜(Term.bound 1 : Term 7)⌝ₛ ∧ (∃ p, ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 2 : Term 7)⌝ₛ, p, ⌜(Term.bound 4 : Term 7)⌝ₛ) ∧ (∀ x, ¬ x ∈ p))) ∨
    (⌜KP.succ0_m⌝ₚ(⌜(Term.newest : Term 7)⌝ₛ, ⌜(Term.bound 2 : Term 7)⌝ₛ) ∧
      (∃ p κ ρ F, ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 2 : Term 7)⌝ₛ, p, ⌜(Term.bound 4 : Term 7)⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p, κ, ρ, F)))⟫ }
  have valid i r : B.denote η i r ↔ It_hold_d Q A i r := it_hold_sat_l hZF.1 ..
  have step i r s : φ.denote ((η.push i).push r) s ↔
      (s = r ∧ ∃ p, Rd_entry_d i p E ∧ ∀ x, ¬ M.mem x p) ∨
      (M.SuccessorOf s i ∧ ∃ p κ ρ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1,
      rd_entry0_sat_l hZF.1, it_payload_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  have hoω := (nice.tree.diagram.model_domain o).mpr ⟨c, nice.tree.root o ho⟩
  obtain ⟨C, r, rf, r₀, rv, rs⟩ := ZFC.class_indexed_choice_l I hZFC B φ η hw ho ((valid o o).mpr (self o hoω)) (by
    intro i j a hi succ ha
    have hj := (hw.1.2 i hi).elim fun j' h => (h.1.eq hZF.1 succ) ▸ h.2
    obtain ⟨k, b, d, e, f, p, pred, hb, hd, he, hf, hp, data⟩ := nice.tree.steps i j hj succ
    rcases data with ⟨empty, eq, ec, ident⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · subst k e
      obtain ⟨b₀, α, β, hb₀, hab, hα, hβ, le⟩ := (valid i a).mp ha
      have eq := nice.tree.diagram.model_function.2 i b₀ b hb₀ hb
      subst b₀
      obtain ⟨δ, hδ⟩ := (cuts.height_domain j).mp hj
      obtain ⟨γ, image, lt⟩ := drop i j i f α δ succ pred hf hα hδ
      have eq := ident α γ image
      subst γ
      obtain ⟨X, R, _, mx, source⟩ := actual a b hab
      obtain ⟨q, hq⟩ := (cuts.code_domain a).mp ((nice.tree.diagram.model_domain a).mpr ⟨b, hab⟩)
      obtain ⟨V, _, _, hV, rank, reg, hω⟩ := cuts.ranks a b q β X R hab hq hβ mx
      have less := le.elim (fun eq => eq ▸ lt) (fun l => (source.rank_height_l hZF hV rank reg hω).2.1.transitive α l δ lt)
      exact ⟨a, (valid j a).mpr ⟨b, δ, β, he, hab, hδ, hβ, Or.inr less⟩,
        (step i a a).mpr (Or.inl ⟨rfl, p, hp, empty⟩)⟩
    · exact ⟨j, (valid j j).mpr (self j hj), (step i a j).mpr (Or.inr ⟨succ, p, κ, ρ, F, hp, pay⟩)⟩)
  have hold i a (ha : Rd_entry_d i a r) := (valid i a).mp (rv i a ha)
  have rr : M.IsSetFunctionFromTo I r ω ω := ⟨rf.1, rf.2.1, by
    intro i hi
    obtain ⟨a, _, ha⟩ := rf.2.2 i hi
    obtain ⟨b, _, _, _, hab, _⟩ := hold i a ha
    exact ⟨a, (nice.tree.diagram.model_domain a).mpr ⟨b, hab⟩, ha⟩⟩
  obtain ⟨V, vs⟩ := ZF.exists_range_of_setFunction hZF I cuts.heights cuts.height_domain
  obtain ⟨W, ws⟩ := ZF.exists_range_of_setFunction hZF I cuts.codes cuts.code_domain
  have af : M.IsSetFunctionFromTo I A ω V := ⟨cuts.heights, cuts.height_domain, fun i hi => by
    obtain ⟨a, ha⟩ := (cuts.height_domain i).mp hi
    exact ⟨a, (vs a).mpr ⟨i, ha⟩, ha⟩⟩
  have df : M.IsSetFunctionFromTo I D ω W := ⟨cuts.codes, cuts.code_domain, fun i hi => by
    obtain ⟨a, ha⟩ := (cuts.code_domain i).mp hi
    exact ⟨a, (ws a).mpr ⟨i, ha⟩, ha⟩⟩
  obtain ⟨A', af', as⟩ := ZF.exists_compositionFunction hZF I rr af
  obtain ⟨D', df', ds⟩ := ZF.exists_compositionFunction hZF I rr df
  have eq_at i a (ha : Rd_entry_d i a r) :
      (∀ β, Rd_entry_d i β A' ↔ Rd_entry_d a β A) ∧ (∀ d, Rd_entry_d i d D' ↔ Rd_entry_d a d D) := by
    have unique b (hb : Rd_entry_d i b r) := rr.1.2 i b a hb ha
    exact ⟨fun β => (as i β).trans ⟨fun ⟨_, b, hb, hβ⟩ => unique b hb ▸ hβ,
      fun hβ => ⟨rr.input_mem_of_pairMember ha, a, ha, hβ⟩⟩,
      fun d => (ds i d).trans ⟨fun ⟨_, b, hb, hd⟩ => unique b hb ▸ hd,
      fun hd => ⟨rr.input_mem_of_pairMember ha, a, ha, hd⟩⟩⟩
  have lower i a α β (ha : Rd_entry_d i a r) (hα : Rd_entry_d i α A) (hβ : Rd_entry_d a β A) : α = β ∨ M.mem α β := by
    obtain ⟨_, α₀, β₀, _, _, hα₀, hβ₀, le⟩ := hold i a ha
    exact cuts.heights.2 i α₀ α hα₀ hα ▸ cuts.heights.2 a β₀ β hβ₀ hβ ▸ le
  have cut i b d β X R (hb : Rd_entry_d i b Q) (hd : Rd_entry_d i d D') (hβ : Rd_entry_d i β A') (mx : Smem_d I b X R) :
      ∃ V S, Smem_d I d V S ∧ M.mem V X ∧ Vr_d X β V ∧ Sc_regular_d X β ∧ M.mem ω V := by
    obtain ⟨a, _, ha⟩ := rr.2.2 i (df'.input_mem_of_pairMember hd)
    obtain ⟨b₀, _, _, hb₀, hab, _⟩ := hold i a ha
    have eq := nice.tree.diagram.model_function.2 i b₀ b hb₀ hb
    exact cuts.ranks a b d β X R (eq ▸ hab) ((eq_at i a ha).2 d |>.mp hd) ((eq_at i a ha).1 β |>.mp hβ) mx
  have enlarge i d X R (hd : Rd_entry_d i d D') (mx : Smem_d I d X R) :
      ∃ e Y S, Rd_entry_d i e D ∧ Smem_d I e Y S ∧ M.MemberSubset Y X := by
    have hi := df'.input_mem_of_pairMember hd
    obtain ⟨b, hb⟩ := (nice.tree.diagram.model_domain i).mp hi
    obtain ⟨Z, T, _, mz, sz⟩ := actual i b hb
    obtain ⟨α, hα⟩ := (cuts.height_domain i).mp hi
    obtain ⟨e, he⟩ := (cuts.code_domain i).mp hi
    obtain ⟨Y, S, my, hY, ry, gy, hyω⟩ := cuts.ranks i b e α Z T hb he hα mz
    obtain ⟨β, _, hβ⟩ := af'.2.2 i hi
    obtain ⟨X₀, R₀, mx₀, hX, rx, gx, hxω⟩ := cut i b d β Z T hb hd hβ mz
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx₀.1 mx.1
    obtain ⟨a, _, ha⟩ := rr.2.2 i hi
    rcases lower i a α β ha hα (((eq_at i a ha).1 β).mp hβ) with eq | lt
    · exact ⟨e, Y, S, he, my, (ry.unique_l hZF sz.transitive hY hX (eq.symm ▸ rx)) ▸ fun _ h => h⟩
    · exact ⟨e, Y, S, he, my, (rx.compare_l hZF sz.transitive hX hY ry ((sz.rank_height_l hZF hX rx gx hxω).2.1.transitive α lt)).1⟩
  refine ⟨A', D', ⟨af'.1, af'.2.1, df'.1, df'.2.1, cuts.models, cut, ?_, ?_⟩,
    (eq_at o o r₀).1, (eq_at o o r₀).2, ?_, ?_⟩
  · intro i p κ ρ F d X R hp pay hd mx
    obtain ⟨e, Y, S, he, my, sub⟩ := enlarge i d X R hd mx
    obtain ⟨hρ, hF⟩ := cuts.contains i p κ ρ F e Y S hp pay he my
    exact ⟨sub ρ hρ, sub F hF⟩
  · intro i j p κ ρ F d X R succ hp pay hd mx
    obtain ⟨e, Y, S, he, my, sub⟩ := enlarge j d X R hd mx
    exact sub ρ (cuts.next i j p κ ρ F e Y S succ hp pay he my)
  · intro i j p succ hp empty d
    have hj := (nice.tree.move_domain i).mp ⟨p, hp⟩ |>.elim fun j' h => (h.2.eq hZF.1 succ) ▸ h.1
    obtain ⟨a, _, ha⟩ := rr.2.2 i (hw.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem)
    obtain ⟨b, _, hb⟩ := rr.2.2 j hj
    rcases (step i a b).mp (rs i j a b succ ha hb) with ⟨eq, _⟩ | ⟨_, q, κ, ρ, F, hq, pay⟩
    · exact ((eq_at i a ha).2 d).trans (eq ▸ (eq_at j b hb).2 d).symm
    · have eq := nice.tree.move_function.2 i q p hq hp
      obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
      exact (empty u ((pair u).mpr (Or.inl rfl))).elim
  · intro i j k f p κ ρ F α β succ pred hf hp pay hα hβ
    have hk := af'.input_mem_of_pairMember hα
    have hj := af'.input_mem_of_pairMember hβ
    obtain ⟨a, _, ha⟩ := rr.2.2 i (hw.transitive (ZF.modelsKP hZF) j hj i succ.predecessor_mem)
    obtain ⟨b, _, hb⟩ := rr.2.2 j hj
    have eq : b = j := by
      rcases (step i a b).mp (rs i j a b succ ha hb) with ⟨_, q, hq, empty⟩ | ⟨sb, _⟩
      · have eq := nice.tree.move_function.2 i p q hp hq
        obtain ⟨t, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
        exact (empty u ((pair u).mpr (Or.inl rfl))).elim
      · exact sb.eq hZF.1 succ
    subst b
    obtain ⟨α₀, hα₀⟩ := (cuts.height_domain k).mp hk
    obtain ⟨γ₀, image₀, lt⟩ := drop i j k f α₀ β succ pred hf hα₀ (((eq_at j j hb).1 β).mp hβ)
    obtain ⟨b, hbQ⟩ := (nice.tree.diagram.model_domain k).mp hk
    obtain ⟨d, hdQ⟩ := (nice.tree.diagram.model_domain j).mp hj
    obtain ⟨X, R, _, mx, sx⟩ := actual k b hbQ
    obtain ⟨Y, S, _, my, sy⟩ := actual j d hdQ
    obtain ⟨a, _, hka⟩ := rr.2.2 k hk
    obtain ⟨q, _, hq⟩ := df'.2.2 k hk
    obtain ⟨V, _, _, hV, rank, reg, hvω⟩ := cut k b q α X R hbQ hq hα mx
    have ord := sx.rank_height_l hZF hV rank reg hvω
    have em := nice.tree.diagram.elementary k j f b X R d Y S hf hbQ hdQ mx.1 my.1
    obtain ⟨γ, _, image⟩ := em.1.1.2.2 α ord.1
    refine ⟨γ, image, ?_⟩
    rcases lower k a α₀ α hka hα₀ (((eq_at k a hka).1 α).mp hα) with eq | less
    · exact em.1.1.1.2 α γ₀ γ (eq ▸ image₀) image ▸ lt
    · exact (em.ordinal_l hZF hw sx.transitive sy.transitive mx my image ord.2.1).transitive γ₀
        ((em.member_l I hZF hw mx my image₀ image).mp less) β lt

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 含恒等步的双重基础反证

分离全部合法有限历史，先取末模型的隶属极小值，再在同一模型的历史中
取原高度极小值。活动步使模型下降，恒等步使原高度下降，两者均矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

private def Pn_state_d (ω D L C s : M.Domain) : Prop := ∃ n H m,
  KPair_d M s n H ∧ M.mem n ω ∧ M.SuccessorOf m n ∧ Pn_history_d hZF ω D L C m H

private def pn_state_m {d} (ω D L C s : Term d) : Formula 1 d := set[d] ⟪
  ∃ n H m, ⌜kpair_m⌝ₚ(⌜s⌝ₛ, n, H) ∧ n ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(m, n) ∧ ⌜pn_history_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, ⌜L⌝ₛ, ⌜C⌝ₛ, m, H)⟫
derive_free_closed pn_state_m

private theorem pn_state_sat_l {d} (η : Env M d) (ω D L C s : Term d) :
    Formula.satisfies η (pn_state_m ω D L C s) ↔ Pn_state_d hZF (ω.eval η) (D.eval η) (L.eval η) (C.eval η) (s.eval η) := by
  simp only [pn_state_m, Pn_state_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, pn_history_sat_l hZF,
    Definitional.Term.eval_weaken]; rfl

private def Pn_last_d (s P : M.Domain) : Prop := ∃ n H r a X π ι,
  KPair_d M s n H ∧ Rd_entry_d n r H ∧ Pn_cell_d r a X P π ι

private def pn_last_m {d} (s P : Term d) : Formula 1 d := set[d] ⟪
  ∃ n H r a X π ι, ⌜kpair_m⌝ₚ(⌜s⌝ₛ, n, H) ∧ ⌜rd_entry0_m⌝ₚ(n, r, H) ∧ ⌜pn_cell_m⌝ₚ(r, a, X, ⌜P⌝ₛ, π, ι)⟫
derive_free_closed pn_last_m

private theorem pn_last_sat_l (hE : Extensional M) {d} (η : Env M d) (s P : Term d) :
    Formula.satisfies η (pn_last_m s P) ↔ Pn_last_d (s.eval η) (P.eval η) := by
  simp only [pn_last_m, Pn_last_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry0_sat_l hE, pn_cell_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)

/-- 含恒等步的 nice 树，其实际正则秩段列不能沿每条后继边严格下降。 -/
theorem it_pnice_no_drop_l {ω c T Q G E L A D z a X P π ι : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (hz : ∀ x, ¬ M.mem x z) (hq : Rd_entry_d z a D) (initial : Pn_row_d (ZFC.models_zf_l hZFC) ω a X P π ι) :
    ¬ (∀ i j k f α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d k α A → Rd_entry_d j β A → ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ) := by
  intro drop
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hω := nice.tree.omega
  have succ_mem {n m} (hn : M.mem n ω) (hm : M.SuccessorOf m n) : M.mem m ω := by
    obtain ⟨m', hm', h'⟩ := hω.1.2 n hn
    exact (hZF.1.eq_of_same_members m' m (fun x => (hm' x).trans (hm x).symm)) ▸ h'
  obtain ⟨A', D', cuts', _, roots, pads, strict⟩ := it_cut_normalize_l hZFC nice cuts hz drop
  have hq' := (roots a).mpr hq
  -- 固定包络容纳原码列和初始模型；后续模型沿隶属下降，始终留在此包络。
  obtain ⟨B, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) D' P
  obtain ⟨χ, C, reg, above, hc, hBC⟩ := ZFC.h_cover_l I hZFC hω B
  have ct := ZF.h_transitive_l I hZF hc
  have algebra := sc_h_algebra_l hZFC hω reg above hc
  have hDC := ct B hBC D' ((pair D').mpr (Or.inl rfl))
  have hPC := ct B hBC P ((pair P).mpr (Or.inr rfl))
  have codes i b (hb : Rd_entry_d i b D') := (rd_entry_transitive_l ct hDC hb).2
  obtain ⟨r, hrC, cell⟩ := initial.cell_l hZF ct algebra (codes z a hq') hPC
  have hzω := (cuts'.code_domain z).mpr ⟨a, hq'⟩
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  obtain ⟨H₀, history₀, _⟩ := pn_history_start_l hZF hz ho hq' cell initial hrC
  obtain ⟨s₀, pair₀⟩ := I.total z H₀
  have first : Pn_state_d hZF ω D' L C s₀ := ⟨z, H₀, o, pair₀, hzω, ho, history₀⟩
  obtain ⟨S, seq⟩ := ZF.fseq_space_exists_l I hZF hω C
  obtain ⟨U, product⟩ := ZF.exists_cartesianProduct hZF I ω S
  let η : Env M 4 := ⟨Fin.cases C (Fin.cases L (Fin.cases D' (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := { body := pn_state_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read s : φ.denote η s ↔ Pn_state_d hZF ω D' L C s := pn_state_sat_l hZF ..
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF φ η U
  have state s : M.mem s B ↔ Pn_state_d hZF ω D' L C s := by
    rw [bs s]
    change (M.mem s U ∧ φ.denote η s) ↔ _
    rw [read s]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨n, H, m, pair, hn, hm, hist⟩ := h
    exact (product s).mpr ⟨n, hn, H, (seq H).mpr ⟨m, succ_mem hn hm, fn0_function_l (ZF.modelsKP hZF) hist.function⟩, pair⟩
  have last_exists s (hs : M.mem s B) : ∃ P, Pn_last_d s P := by
    obtain ⟨n, H, m, pair, _, hm, hist⟩ := (state s).mp hs
    obtain ⟨r, _, hr⟩ := hist.function.2.1 n hm.predecessor_mem
    obtain ⟨a, X, P, π, ι, cell, _⟩ := hist.rows n r hr
    exact ⟨P, n, H, r, a, X, π, ι, pair, hr, cell⟩
  have last_mem s P (hs : M.mem s B) (hp : Pn_last_d s P) : M.mem P C := by
    obtain ⟨n, H, m, pair, _, _, hist⟩ := (state s).mp hs
    obtain ⟨n', H', r, a, X, π, ι, pair', hr, q, path, _⟩ := hp
    obtain ⟨e, e'⟩ := kpair_injective_l M pair' pair
    subst n' H'
    obtain ⟨v, pv, pr⟩ := path
    exact (pv.mem_l M ct (pr.mem_l M ct (hist.function.bound_l hr).2).2).1
  -- 第一层基础：所有合法历史的末模型组成一个真实集合。
  let ψ : UnarySchema 1 := { body := .existsMem (.bound 1) (pn_last_m .newest (.bound 1)) }
  let θ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  have readP P : ψ.denote θ P ↔ ∃ s, M.mem s B ∧ Pn_last_d s P := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, pn_last_sat_l hZF.1]; rfl
  obtain ⟨V, vs⟩ := ZF.separation_exists_d hZF ψ θ C
  have ps P : M.mem P V ↔ ∃ s, M.mem s B ∧ Pn_last_d s P := by
    refine (vs P).trans ?_
    change (M.mem P C ∧ ψ.denote θ P) ↔ _
    rw [readP]
    exact ⟨And.right, fun h => ⟨by obtain ⟨s, hs, last⟩ := h; exact last_mem s P hs last, h⟩⟩
  obtain ⟨P₀, last₀⟩ := last_exists s₀ ((state s₀).mpr first)
  obtain ⟨P, hP, minP⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨P₀, (ps P₀).mpr ⟨s₀, (state s₀).mpr first, last₀⟩⟩
  -- 第二层基础：固定末模型后，原高度仍是已有高度列的一个子集。
  let χ : UnarySchema 3 := { body := set[4] ⟪∃ s ∈ ⌜(Term.bound 2 : Term 4)⌝ₛ,
    ⌜pn_last_m⌝ₚ(s, ⌜(Term.bound 1 : Term 4)⌝ₛ) ∧
    (∃ n H, ⌜kpair_m⌝ₚ(s, n, H) ∧ ⌜rd_entry0_m⌝ₚ(n, ⌜(Term.newest : Term 4)⌝ₛ, ⌜(Term.bound 3 : Term 4)⌝ₛ))⟫ }
  let ξ : Env M 3 := ⟨Fin.cases P (Fin.cases B (fun _ => A)), fun _ => A⟩
  have readA α : χ.denote ξ α ↔ ∃ s, M.mem s B ∧ Pn_last_d s P ∧
      ∃ n H, KPair_d M s n H ∧ Rd_entry_d n α A := by
    simp only [χ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_exists_iff, pn_last_sat_l hZF.1, kpair_sat_l M hZF.1, rd_entry0_sat_l hZF.1,
      Definitional.Term.eval_weaken]; rfl
  obtain ⟨W, ws⟩ := ZF.exists_range_of_setFunction hZF I cuts.heights cuts.height_domain
  obtain ⟨U, us⟩ := ZF.separation_exists_d hZF χ ξ W
  have values α : M.mem α U ↔ ∃ s, M.mem s B ∧ Pn_last_d s P ∧
      ∃ n H, KPair_d M s n H ∧ Rd_entry_d n α A := by
    refine (us α).trans ?_
    change (M.mem α W ∧ χ.denote ξ α) ↔ _
    rw [readA]
    exact ⟨And.right, fun h => ⟨by obtain ⟨_, _, _, n, _, _, hα⟩ := h; exact (ws α).mpr ⟨n, hα⟩, h⟩⟩
  have nonempty : ∃ α, M.mem α U := by
    obtain ⟨s, hs, last⟩ := (ps P).mp hP
    obtain ⟨n, H, _, pair, hn, _⟩ := (state s).mp hs
    obtain ⟨α, hα⟩ := (cuts.height_domain n).mp hn
    exact ⟨α, (values α).mpr ⟨s, hs, last, n, H, pair, hα⟩⟩
  obtain ⟨α, hα, minα⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) nonempty
  obtain ⟨s, hs, last, n, H, pair, height⟩ := (values α).mp hα
  obtain ⟨n₀, H₁, m, pair', hn, hm, hist⟩ := (state s).mp hs
  obtain ⟨eqn, eqH⟩ := kpair_injective_l M pair' pair
  subst n₀ H₁
  obtain ⟨n₀, H₁, r, a, X, π, ι, pair', hr, cell⟩ := last
  obtain ⟨eqn, eqH⟩ := kpair_injective_l M pair' pair
  subst n₀ H₁
  obtain ⟨l, J, hl, hist', keep⟩ := pn_history_extend_l hZFC nice cuts' pads strict hist hn hm ct algebra codes
  obtain ⟨t, pairt⟩ := I.total m J
  have ht := (state t).mpr ⟨m, J, l, pairt, succ_mem hn hm, hl, hist'⟩
  obtain ⟨q, _, hq⟩ := hist'.function.2.1 m hl.predecessor_mem
  obtain ⟨b, Y, N, σ, η, cq, _, _⟩ := hist'.rows m q hq
  have lastt : Pn_last_d t N := ⟨m, J, q, b, Y, σ, η, pairt, hq, cq⟩
  obtain ⟨_, below, active⟩ := hist'.past n m r q a X P π ι b Y N σ η (keep n r hr) hq hm.predecessor_mem cell cq
  have eq := below.resolve_right (minP N ((ps N).mpr ⟨t, ht, lastt⟩))
  subst N
  have inactive ρ (hρ : Rd_entry_d n ρ L) : False := KP.mem_irrefl_d (ZF.modelsKP hZF) P (active ⟨ρ, hρ⟩)
  obtain ⟨k, b, d, e, f, p, pred, _, _, _, hf, hp, data⟩ := nice.tree.steps n m (succ_mem hn hm) hm
  have pad : k = n ∧ ∀ x y, Rd_entry_d x y f → x = y := by
    rcases data with ⟨_, eq, _, ident⟩ | ⟨κ, ρ, F, _, _, _, _, pay, _⟩
    · exact ⟨eq, ident⟩
    · exact (inactive ρ ((nice.levels n ρ).mpr ⟨p, κ, F, hp, pay⟩)).elim
  obtain ⟨eq, ident⟩ := pad
  subst k
  obtain ⟨β, hβ⟩ := (cuts.height_domain m).mp (succ_mem hn hm)
  obtain ⟨γ, image, less⟩ := drop n m n f α β hm pred hf height hβ
  have eq := ident α γ image
  subst γ
  exact minα β ((values β).mpr ⟨t, ht, lastt, m, J, pairt, hβ⟩) less

end YesMetaZFC.SetTheory.LargeCardinal
