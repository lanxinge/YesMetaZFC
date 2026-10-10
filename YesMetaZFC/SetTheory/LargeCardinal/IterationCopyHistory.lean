import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyRow
import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax

/-! # 保留全部前驱和实际超幂的有限复制历史

历史中的图列以原树序的初段为指标。模型行、全前驱秩段一致性、每个交换
方块及每条原扩展器的实际复制边均有原公式，供内部类依赖选择直接消费。
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

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_edge_d (ω κ L F σ U Z z v f : M.Domain) : Prop := ∃ κ' L' F',
  Rd_entry_d κ κ' σ ∧ Rd_entry_d L L' σ ∧ Rd_entry_d F F' σ ∧ It_ultra_d hZF ω κ' L' F' z v f ∧ Ea_agree_d ω κ' Z U
def ic_edge_m {d} (ω κ L F σ U Z z v f : Term d) : Formula 1 d := set[d] ⟪
  ∃ κ' L' F', ⌜rd_entry0_m⌝ₚ(⌜κ⌝ₛ, κ', ⌜σ⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜L⌝ₛ, L', ⌜σ⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜F⌝ₛ, F', ⌜σ⌝ₛ) ∧ ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, κ', L', F', ⌜z⌝ₛ, ⌜v⌝ₛ, ⌜f⌝ₛ) ∧
    ⌜ea_agree_m⌝ₚ(⌜ω⌝ₛ, κ', ⌜Z⌝ₛ, ⌜U⌝ₛ)⟫
derive_free_closed ic_edge_m
theorem ic_edge_sat_l {d} (η : Env M d) (ω κ L F σ U Z z v f : Term d) :
    Formula.satisfies η (ic_edge_m ω κ L F σ U Z z v f) ↔ Ic_edge_d hZF
      (ω.eval η) (κ.eval η) (L.eval η) (F.eval η) (σ.eval η) (U.eval η) (Z.eval η) (z.eval η) (v.eval η) (f.eval η) := by
  simp only [ic_edge_m, Ic_edge_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1, it_ultra_sat_l hZF, ea_agree_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

structure Ic_history_d (ω T Q G E L n H S Q' G' : M.Domain) : Prop where
  diagram : It_diagram_d hZF ω n S Q' G'
  order : ∀ i j, Rd_entry_d i j S ↔ Rd_entry_d i j T ∧ M.mem j n
  function : M.IsSetFunction I H
  domain : M.IsDomainOf I n H
  rows : ∀ i r, Rd_entry_d i r H → ∃ c X A π z Z α, Ic_cell_d r X A π z Z α ∧
    Rd_entry_d i c Q ∧ Rd_entry_d i z Q' ∧ Ic_row_d hZF ω c X A π z Z α
  past : ∀ i j X A π z Z α Y B σ u U β, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    M.mem i j → ∃ ρ φ, Rd_entry_d i ρ L ∧ Pn_agree_d X A π Y B σ ρ φ ∧ Es_strength_d X ρ Y
  cuts : ∀ i j X A π z Z α Y B σ u U β g, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    It_map_d G' i j g → Rd_entry_d A B g
  squares : ∀ i j X A π z Z α Y B σ u U β f g, Ic_at_d H i X A π z Z α → Ic_at_d H j Y B σ u U β →
    It_map_d G i j f → It_map_d G' i j g → ∀ x x' y y',
      Rd_entry_d x x' π → Rd_entry_d x y f → Rd_entry_d x' y' g → Rd_entry_d y y' σ
  steps : ∀ i j k H₀ B σ u U β X A π z Z α P C τ v V γ p κ ρ F f,
    M.SuccessorOf j i → It_pred_d T k j → Ic_at_d H i H₀ B σ u U β → Ic_at_d H k X A π z Z α →
    Ic_at_d H j P C τ v V γ → Rd_entry_d i p E → It_payload_d p κ ρ F → It_map_d G' k j f →
      Ic_edge_d hZF ω κ ρ F σ U Z z v f

def ic_history_m {d} (ω T Q G E L n H S Q' G' : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜S⌝ₛ, ⌜Q'⌝ₛ, ⌜G'⌝ₛ) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜S⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) ∧ j ∈ ⌜n⌝ₛ) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜H⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜n⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i r, ⌜rd_entry0_m⌝ₚ(i, r, ⌜H⌝ₛ) → ∃ c X A π z Z α, ⌜ic_cell_m⌝ₚ(r, X, A, π, z, Z, α) ∧
    ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(i, z, ⌜Q'⌝ₛ) ∧ ⌜ic_row_m⌝ₚ(⌜ω⌝ₛ, c, X, A, π, z, Z, α)) ∧
  (∀ i j X A π z Z α Y B σ u U β,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, i, X, A, π, z, Z, α) → ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, j, Y, B, σ, u, U, β) → i ∈ j →
    ∃ ρ φ, ⌜rd_entry0_m⌝ₚ(i, ρ, ⌜L⌝ₛ) ∧ ⌜pn_agree_m⌝ₚ(X, A, π, Y, B, σ, ρ, φ) ∧ ⌜es_strength0_m⌝ₚ(X, ρ, Y)) ∧
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
    ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, k, j, f) → ⌜ic_edge_m⌝ₚ(⌜ω⌝ₛ, κ, ρ, F, σ, U, Z, z, v, f))⟫
derive_free_closed ic_history_m

theorem ic_history_sat_l {d} (η : Env M d) (ω T Q G E L n H S Q' G' : Term d) :
    Formula.satisfies η (ic_history_m ω T Q G E L n H S Q' G') ↔ Ic_history_d hZF
      (ω.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) (n.eval η)
      (H.eval η) (S.eval η) (Q'.eval η) (G'.eval η) := by
  simp only [ic_history_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I, KP.succ0_sat_l hZF.1,
    rd_entry0_sat_l hZF.1, it_diagram_sat_l hZF, ic_cell_sat_l hZF.1, ic_row_sat_l hZF, ic_at_sat_l hZF.1,
    pn_agree_sat_l (ZF.modelsKP hZF), es_strength0_sat_l, it_map_sat_l hZF.1, it_pred_sat_l hZF.1,
    it_payload_sat_l hZF.1, ic_edge_sat_l hZF, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.diagram, h.order, h.function, h.domain, h.rows, h.past, h.cuts, h.squares, h.steps⟩⟩

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

end YesMetaZFC.SetTheory.LargeCardinal
