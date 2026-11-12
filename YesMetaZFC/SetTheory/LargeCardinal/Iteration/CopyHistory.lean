import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRow
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax

/-! # 保留全部前驱和实际超幂的有限复制历史

历史中的图列以原树序的初段为指标。模型行、全前驱秩段一致性、恒等段的相同历史行、每个交换
方块及每条原扩展器的实际复制边均有原公式。每条已实施的边还保存同一
工作扩展器的质量；工作支撑的严格次序只量化后继已进入历史的操作。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_cell_d (r X A π z Z α : M.Domain) : Prop :=
  ∃ s t, Rd_triple_d r X A s ∧ Rd_triple_d s π z t ∧ KPair_d M t Z α
def ic_cell_m {d} (r X A π z Z α : Term d) : Formula 1 d := set[d] ⟪
  ∃ s t, ⌜rd_triple0_m⌝ₚ(⌜r⌝ₛ, ⌜X⌝ₛ, ⌜A⌝ₛ, s) ∧ ⌜rd_triple0_m⌝ₚ(s, ⌜π⌝ₛ, ⌜z⌝ₛ, t) ∧ ⌜kpair0_m⌝ₚ(t, ⌜Z⌝ₛ, ⌜α⌝ₛ)⟫
derive_free_closed ic_cell_m
theorem ic_cell_sat_l (hE : Extensional M) {d} (η : Env M d) (r X A π z Z α : Term d) :
    Formula.satisfies η (ic_cell_m r X A π z Z α) ↔
      Ic_cell_d (r.eval η) (X.eval η) (A.eval η) (π.eval η) (z.eval η) (Z.eval η) (α.eval η) := by
  simp only [ic_cell_m, Ic_cell_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl
theorem Ic_cell_d.unique_l {r X A π z Z α Y B σ u U β : M.Domain}
    (h : Ic_cell_d r X A π z Z α) (g : Ic_cell_d r Y B σ u U β) :
    X = Y ∧ A = B ∧ π = σ ∧ z = u ∧ Z = U ∧ α = β := by
  obtain ⟨s, t, h₀, h₁, h₂⟩ := h
  obtain ⟨s', t', g₀, g₁, g₂⟩ := g
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l h₀ g₀
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l h₁ g₁
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M h₂ g₂
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ic_cell_exists_l (hKP : M.Models KP) (X A π z Z α : M.Domain) : ∃ r, Ic_cell_d r X A π z Z α := by
  let I := kp_pair_l hKP
  obtain ⟨t, ht⟩ := I.total Z α
  obtain ⟨p, hp⟩ := I.total z t
  obtain ⟨s, hs⟩ := I.total π p
  obtain ⟨q, hq⟩ := I.total A s
  obtain ⟨r, hr⟩ := I.total X q
  exact ⟨r, s, t, ⟨q, hq, hr⟩, ⟨p, hp, hs⟩, ht⟩

def Ic_at_d (H i X A π z Z α : M.Domain) : Prop := ∃ r, Rd_entry_d i r H ∧ Ic_cell_d r X A π z Z α
def ic_at_m {d} (H i X A π z Z α : Term d) : Formula 1 d := set[d] ⟪
  ∃ r, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, r, ⌜H⌝ₛ) ∧ ⌜ic_cell_m⌝ₚ(r, ⌜X⌝ₛ, ⌜A⌝ₛ, ⌜π⌝ₛ, ⌜z⌝ₛ, ⌜Z⌝ₛ, ⌜α⌝ₛ)⟫
derive_free_closed ic_at_m
theorem ic_at_sat_l (hE : Extensional M) {d} (η : Env M d) (H i X A π z Z α : Term d) :
    Formula.satisfies η (ic_at_m H i X A π z Z α) ↔
      Ic_at_d (H.eval η) (i.eval η) (X.eval η) (A.eval η) (π.eval η) (z.eval η) (Z.eval η) (α.eval η) := by
  simp only [ic_at_m, Ic_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, ic_cell_sat_l hE, Definitional.Term.eval_weaken]; rfl
theorem Ic_at_d.unique_l (hKP : M.Models KP) {H i X A π z Z α Y B σ u U β : M.Domain}
    (hf : M.IsSetFunction (kp_pair_l hKP) H) (h : Ic_at_d H i X A π z Z α) (g : Ic_at_d H i Y B σ u U β) :
    X = Y ∧ A = B ∧ π = σ ∧ z = u ∧ Z = U ∧ α = β := by
  obtain ⟨r, hr, hc⟩ := h
  obtain ⟨s, hs, sc⟩ := g
  exact hc.unique_l (hf.2 i s r hs hr ▸ sc)

/-- 只比较已经实施的支撑：较后操作的后继必须在当前历史内。 -/
def Ic_ordered_d (H L n : M.Domain) : Prop :=
  ∀ i j r X A π z Z α Y B σ u U β ρ ψ a b,
    Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β → M.SuccessorOf r j → M.mem r n →
    Rd_entry_d i ρ L → Rd_entry_d j ψ L → Rd_entry_d ρ a π → Rd_entry_d ψ b σ → M.mem i j → M.mem a b
def ic_ordered_m {d} (H L n : Term d) : Formula 1 d := set[d] ⟪
  ∀ i j r X A π z Z α Y B σ u U β ρ ψ a b,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, X, A, π, z, Z, α) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, Y, B, σ, u, U, β) →
    ⌜KP.succ0_m⌝ₚ(r, j) → r ∈ ⌜n⌝ₛ → ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, ψ, ⌜L⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(ρ, a, π) → ⌜rd_entry0_m⌝ₚ(ψ, b, σ) → i ∈ j → a ∈ b⟫
derive_free_closed ic_ordered_m
theorem ic_ordered_sat_l (hE : Extensional M) {d} (η : Env M d) (H L n : Term d) :
    Formula.satisfies η (ic_ordered_m H L n) ↔ Ic_ordered_d (H.eval η) (L.eval η) (n.eval η) := by
  simp only [ic_ordered_m, Ic_ordered_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    ic_at_sat_l hE, KP.succ0_sat_l hE, Formula.satisfies_mem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_edge_d (ω κ L F σ u U Z z v f : M.Domain) : Prop := ∃ κ' L' F',
  Rd_entry_d κ κ' σ ∧ Rd_entry_d L L' σ ∧ Rd_entry_d F F' σ ∧
    It_ultra_d I ω κ' L' F' z v f ∧ Ea_agree_d ω κ' Z U ∧ Ic_quality_d hZF ω κ' L' F' u U
def ic_edge_m {d} (ω κ L F σ u U Z z v f : Term d) : Formula 1 d := set[d] ⟪
  ∃ κ' L' F', ⌜rd_entry0_m⌝ₚ(⌜κ⌝ₛ, κ', ⌜σ⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜L⌝ₛ, L', ⌜σ⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜F⌝ₛ, F', ⌜σ⌝ₛ) ∧ ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, κ', L', F', ⌜z⌝ₛ, ⌜v⌝ₛ, ⌜f⌝ₛ) ∧
    ⌜ea_agree_m⌝ₚ(⌜ω⌝ₛ, κ', ⌜Z⌝ₛ, ⌜U⌝ₛ) ∧ ⌜ic_quality_m⌝ₚ(⌜ω⌝ₛ, κ', L', F', ⌜u⌝ₛ, ⌜U⌝ₛ)⟫
derive_free_closed ic_edge_m
theorem ic_edge_sat_l {d} (η : Env M d) (ω κ L F σ u U Z z v f : Term d) :
    Formula.satisfies η (ic_edge_m ω κ L F σ u U Z z v f) ↔ Ic_edge_d hZF
      (ω.eval η) (κ.eval η) (L.eval η) (F.eval η) (σ.eval η) (u.eval η) (U.eval η) (Z.eval η) (z.eval η) (v.eval η) (f.eval η) := by
  simp only [ic_edge_m, Ic_edge_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1, it_ultra_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, ea_agree_sat_l hZF.1, ic_quality_sat_l hZF, Definitional.Term.eval_weaken]; rfl

structure Ic_history_d (ω T Q G E L n H S Q' G' : M.Domain) : Prop where
  diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω n S Q' G'
  order : ∀ i j, Rd_entry_d i j S ↔ Rd_entry_d i j T ∧ M.mem j n
  function : M.IsSetFunction I H
  domain : M.IsDomainOf I n H
  rows : ∀ i r, Rd_entry_d i r H → ∃ c X A π z Z α, Ic_cell_d r X A π z Z α ∧
    Rd_entry_d i c Q ∧ Rd_entry_d i z Q' ∧ Ic_row_d hZF ω c X A π z Z α
  past : ∀ i j X A π z Z α Y B σ u U β, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    M.mem i j → Ic_past_d I Q L i j X A π Y B σ
  cuts : ∀ i j X A π z Z α Y B σ u U β g, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    It_map_d G' i j g → Rd_entry_d A B g
  squares : ∀ i j X A π z Z α Y B σ u U β f g, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    It_map_d G i j f → It_map_d G' i j g → ∀ x x' y y',
      Rd_entry_d x x' π → Rd_entry_d x y f → Rd_entry_d x' y' g → Rd_entry_d y y' σ
  steps : ∀ i j k H₀ B σ u U β X A π z Z α P C τ v V γ p κ ρ F f,
    M.SuccessorOf j i → It_pred_d T k j → Ic_at_d H i H₀ B σ u U β → Ic_at_d H k X A π z Z α →
    Ic_at_d H j P C τ v V γ → Rd_entry_d i p E → It_payload_d p κ ρ F → It_map_d G' k j f →
      Ic_edge_d hZF ω κ ρ F σ u U Z z v f
  pads : ∀ i j p, M.SuccessorOf j i → M.mem j n → Rd_entry_d i p E → (∀ x, ¬ M.mem x p) →
    (∀ r, Rd_entry_d i r H ↔ Rd_entry_d j r H) ∧
      ∀ f x y, It_map_d G' i j f → Rd_entry_d x y f → x = y
  increasing : Ic_ordered_d H L n

def ic_history_m {d} (ω T Q G E L n H S Q' G' : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜S⌝ₛ, ⌜Q'⌝ₛ, ⌜G'⌝ₛ) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜S⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) ∧ j ∈ ⌜n⌝ₛ) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜H⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜n⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i r, ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ∃ c X A π z Z α, ⌜ic_cell_m⌝ₚ(r, X, A, π, z, Z, α) ∧
    ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i, z, ⌜Q'⌝ₛ) ∧ ⌜ic_row_m⌝ₚ(⌜ω⌝ₛ, c, X, A, π, z, Z, α)) ∧
  (∀ i j X A π z Z α Y B σ u U β,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, X, A, π, z, Z, α) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, Y, B, σ, u, U, β) → i ∈ j →
    ⌜ic_past_m⌝ₚ(⌜Q⌝ₛ, ⌜L⌝ₛ, i, j, X, A, π, Y, B, σ)) ∧
  (∀ i j X A π z Z α Y B σ u U β g,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, X, A, π, z, Z, α) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, Y, B, σ, u, U, β) →
    ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, j, g) → ⌜rd_entry0_m⌝ₚ(A, B, g)) ∧
  (∀ i j X A π z Z α Y B σ u U β f g,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, X, A, π, z, Z, α) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, Y, B, σ, u, U, β) →
    ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, j, g) → ∀ x x' y y',
    ⌜rd_entry0_m⌝ₚ(x, x', π) → ⌜rd_entry0_m⌝ₚ(x, y, f) → ⌜rd_entry0_m⌝ₚ(x', y', g) → ⌜rd_entry0_m⌝ₚ(y, y', σ)) ∧
  (∀ i j k H₀ B σ u U β X A π z Z α P C τ v V γ p κ ρ F f,
    ⌜KP.succ0_m⌝ₚ(j, i) → ⌜it_pred_m⌝ₚ(⌜T⌝ₛ, k, j) →
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, H₀, B, σ, u, U, β) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, k, X, A, π, z, Z, α) →
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, P, C, τ, v, V, γ) → ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → ⌜it_payload_m⌝ₚ(p, κ, ρ, F) →
    ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, k, j, f) → ⌜ic_edge_m⌝ₚ(⌜ω⌝ₛ, κ, ρ, F, σ, u, U, Z, z, v, f)) ∧
  (∀ i j p, ⌜KP.succ0_m⌝ₚ(j, i) → j ∈ ⌜n⌝ₛ → ⌜rd_entry0_m⌝ₚ(i, p, ⌜E⌝ₛ) → (∀ x, ¬ x ∈ p) →
    (∀ r, ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(j, r, ⌜H⌝ₛ)) ∧
      (∀ f x y, ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, j, f) → ⌜rd_entry0_m⌝ₚ(x, y, f) → x = y)) ∧ ⌜ic_ordered_m⌝ₚ(⌜H⌝ₛ, ⌜L⌝ₛ, ⌜n⌝ₛ)⟫
derive_free_closed ic_history_m

theorem ic_history_sat_l {d} (η : Env M d) (ω T Q G E L n H S Q' G' : Term d) :
    Formula.satisfies η (ic_history_m ω T Q G E L n H S Q' G') ↔ Ic_history_d hZF
      (ω.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) (n.eval η)
      (H.eval η) (S.eval η) (Q'.eval η) (G'.eval η) := by
  simp only [ic_history_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I, KP.succ0_sat_l hZF.1,
    rd_entry0_sat_l hZF.1, it_diagram_sat_l hZF, ic_cell_sat_l hZF.1, ic_row_sat_l hZF, ic_at_sat_l hZF.1,
    it_map_sat_l hZF.1, it_pred_sat_l hZF.1,
    it_payload_sat_l hZF.1, ic_edge_sat_l hZF, ic_past_sat_l (ZF.modelsKP hZF), ic_ordered_sat_l hZF.1,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun h => ⟨h.diagram, h.order, h.function, h.domain, h.rows, h.past, h.cuts, h.squares, h.steps, h.pads, h.increasing⟩⟩

theorem Ic_history_d.row_l {ω T Q G E L n H S Q' G' i X A π z Z α : M.Domain}
    (h : Ic_history_d hZF ω T Q G E L n H S Q' G') (hi : Ic_at_d H i X A π z Z α) :
    ∃ c, Rd_entry_d i c Q ∧ Rd_entry_d i z Q' ∧ Ic_row_d hZF ω c X A π z Z α := by
  obtain ⟨r, hr, cell⟩ := hi
  obtain ⟨c, Y, B, σ, u, U, β, cell', hc, hz, row⟩ := h.rows i r hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := cell'.unique_l cell
  exact ⟨c, hc, hz, row⟩

theorem Ic_history_d.at_l {ω T Q G E L n H S Q' G' i : M.Domain}
    (h : Ic_history_d hZF ω T Q G E L n H S Q' G') (hi : M.mem i n) :
    ∃ c X A π z Z α, Ic_at_d H i X A π z Z α ∧ Rd_entry_d i c Q ∧ Rd_entry_d i z Q' ∧ Ic_row_d hZF ω c X A π z Z α := by
  obtain ⟨r, hr⟩ := (h.domain i).mp hi
  obtain ⟨c, X, A, π, z, Z, α, cell, hc, hz, row⟩ := h.rows i r hr
  exact ⟨c, X, A, π, z, Z, α, ⟨r, hr, cell⟩, hc, hz, row⟩

theorem Ic_row_d.start_l {ω c X A π z Z α o θ T Q G E L : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω θ T Q G)
    (ho : ∀ x, ¬ M.mem x o) (hc : Rd_entry_d o c Q) :
    ∃ m H S Q' G', M.SuccessorOf m o ∧ Ic_history_d hZF ω T Q G E L m H S Q' G' ∧ Ic_at_d H o X A π z Z α := by
  have data := row
  obtain ⟨_, _, V, _, _, K, _, _, hz, _, full, hA, _⟩ := data
  obtain ⟨o₀, m, S, Q', G', ho₀, hm, root⟩ := it_root_l hZF (it_source_mem_l hZF hz full.source)
  have eq := hZF.1.eq_of_same_members o₀ o (fun x => iff_of_false (ho₀ x) (ho x))
  subst o₀
  have one i (hi : M.mem i m) : i = o := ((hm i).mp hi).elim (fun h => (ho i h).elim) (hZF.1.eq_of_same_members i o)
  obtain ⟨r, cell⟩ := ic_cell_exists_l (ZF.modelsKP hZF) X A π z Z α
  obtain ⟨C, cs⟩ := KP.exists_singleton (ZF.modelsKP hZF) r
  obtain ⟨H, hf, hs⟩ := ZF.exists_constantFunction hZF I (source := m) ((cs r).mpr rfl)
  have top : Ic_at_d H o X A π z Z α := ⟨r, (hs o r).mpr ⟨hm.predecessor_mem, rfl⟩, cell⟩
  have index {i Y B σ u U β} (hi : Ic_at_d H i Y B σ u U β) : i = o := by
    obtain ⟨t, ht, _⟩ := hi
    exact one i (hf.input_mem_of_pairMember ht)
  have order i j : Rd_entry_d i j S ↔ Rd_entry_d i j T ∧ M.mem j m := by
    constructor
    · intro hij
      obtain ⟨hi, hj⟩ := root.diagram.order.bound i j hij
      have ei := one i hi
      have ej := one j hj
      subst i j
      exact ⟨tree.order.refl o ((tree.model_domain o).mpr ⟨c, hc⟩), hm.predecessor_mem⟩
    · rintro ⟨hij, hj⟩
      have ej := one j hj
      subst j
      have ei := (tree.order.forward i o hij).elim id (fun hi => (ho i hi).elim)
      subst i
      exact root.diagram.order.refl o hm.predecessor_mem
  refine ⟨m, H, S, Q', G', hm, ⟨root.diagram, order, hf.1, hf.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, top⟩
  · intro i t ht
    obtain ⟨hi, et⟩ := (hs i t).mp ht
    have ei := one i hi
    subst i t
    exact ⟨c, X, A, π, z, Z, α, cell, hc, root.root o ho, row⟩
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ ai aj hij
    exact (ho i (index aj ▸ hij)).elim
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ g ai aj hg
    have ei := index ai
    have ej := index aj
    subst i j
    rw [(ai.unique_l (ZF.modelsKP hZF) hf.1 top).2.1, (aj.unique_l (ZF.modelsKP hZF) hf.1 top).2.1]
    have e := root.diagram.elementary o o g z Z V z Z V hg (root.root o ho) (root.root o ho) hz.1 hz.1
    obtain ⟨B, _, hab⟩ := e.1.1.2.2 A hA
    exact (root.diagram.identity o g hg A B hab).symm ▸ hab
  · intro i j X₁ A₁ π₁ z₁ Z₁ α₁ X₂ A₂ π₂ z₂ Z₂ α₂ f g ai aj hfi hgi x x' y y' hxx hxy hyy
    have ei := index ai
    have ej := index aj
    subst i j
    have eq := ai.unique_l (ZF.modelsKP hZF) hf.1 aj
    exact tree.identity o f hfi x y hxy ▸ root.diagram.identity o g hgi x' y' hyy ▸ eq.2.2.1 ▸ hxx
  · intro i j k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ succ _ _ _ aj
    exact (ho i (index aj ▸ succ.predecessor_mem)).elim
  · intro i j p succ hj _ _
    exact (ho i (one j hj ▸ succ.predecessor_mem)).elim

  · intro i j r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ succ hr
    exact (ho j (one r hr ▸ succ.predecessor_mem)).elim

end YesMetaZFC.SetTheory.LargeCardinal
