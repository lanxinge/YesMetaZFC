import YesMetaZFC.SetTheory.LargeCardinal.TypeGameProgramCatalog
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryCatalog
import YesMetaZFC.Model.SetTheory.Internal.SubtypeSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeExceedsSyntax

/-! # 类型游戏的实际走法与表项读取

辅助走法为 (ℓ,t,(κ,u))，回答为 (τ,w)。固定表项只按字面配对结构解包；
合法历史中不重复选择程序，不把语义证书当作额外走法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_aux_data_d (a ℓ t κ u : M.Domain) : Prop := ∃ b, Rd_triple_d a ℓ t b ∧ KPair_d M b κ u
def tg_aux_data_m {d} (a ℓ t κ u : Term d) : Formula 1 d := set[d] ⟪∃ b,
  ⌜rd_triple0_m⌝ₚ(⌜a⌝ₛ, ⌜ℓ⌝ₛ, ⌜t⌝ₛ, b) ∧ ⌜kpair0_m⌝ₚ(b, ⌜κ⌝ₛ, ⌜u⌝ₛ)⟫
derive_free_closed tg_aux_data_m

theorem tg_aux_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (a ℓ t κ u : Term d) :
    Formula.satisfies ρ (tg_aux_data_m a ℓ t κ u) ↔
      Tg_aux_data_d (a.eval ρ) (ℓ.eval ρ) (t.eval ρ) (κ.eval ρ) (u.eval ρ) := by
  simp only [tg_aux_data_m, Tg_aux_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Tg_aux_data_d.unique_l {a ℓ t κ u ℓ' t' κ' u' : M.Domain}
    (h : Tg_aux_data_d a ℓ t κ u) (h' : Tg_aux_data_d a ℓ' t' κ' u') :
    ℓ = ℓ' ∧ t = t' ∧ κ = κ' ∧ u = u' := by
  obtain ⟨b, head, tail⟩ := h
  obtain ⟨b', head', tail'⟩ := h'
  obtain ⟨rfl, rfl, rfl⟩ := head.unique_l head'
  exact ⟨rfl, rfl, kpair_injective_l M tail tail'⟩

def Tg_ee_data_d (Γ κ n B U D : M.Domain) (q : Ee_queries_d M) : Prop :=
  ∃ x c p, KPair_d M x κ n ∧ Rd_entry_d x c Γ ∧ Rd_quad_d c B U D p ∧
    Rd_quad_d p q.largest q.domain q.inaccessible q.stretch

def tg_ee_data_m {d} (Γ κ n B U D g h i e : Term d) : Formula 1 d := set[d] ⟪∃ x c p,
  ⌜kpair0_m⌝ₚ(x, ⌜κ⌝ₛ, ⌜n⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, c, ⌜Γ⌝ₛ) ∧
  ⌜rd_quad_m⌝ₚ(c, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, p) ∧ ⌜rd_quad_m⌝ₚ(p, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ)⟫
derive_free_closed tg_ee_data_m

theorem tg_ee_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ κ n B U D g h i e : Term d) :
    Formula.satisfies ρ (tg_ee_data_m Γ κ n B U D g h i e) ↔
      Tg_ee_data_d (Γ.eval ρ) (κ.eval ρ) (n.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [tg_ee_data_m, Tg_ee_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_query_data_d (Γ κ k s t B U D r m b h q : M.Domain) : Prop :=
  ∃ x c p a, Rd_quad_d x κ k s t ∧ Rd_entry_d x c Γ ∧ Rd_quad_d c B U D p ∧
    Rd_quad_d p r m b a ∧ KPair_d M a h q

def tg_query_data_m {d} (Γ κ k s t B U D r m b h q : Term d) : Formula 1 d := set[d] ⟪∃ x c p a,
  ⌜rd_quad_m⌝ₚ(x, ⌜κ⌝ₛ, ⌜k⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, c, ⌜Γ⌝ₛ) ∧
  ⌜rd_quad_m⌝ₚ(c, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, p) ∧ ⌜rd_quad_m⌝ₚ(p, ⌜r⌝ₛ, ⌜m⌝ₛ, ⌜b⌝ₛ, a) ∧ ⌜kpair0_m⌝ₚ(a, ⌜h⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed tg_query_data_m

theorem tg_query_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ κ k s t B U D r m b h q : Term d) :
    Formula.satisfies ρ (tg_query_data_m Γ κ k s t B U D r m b h q) ↔ Tg_query_data_d
      (Γ.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
      (r.eval ρ) (m.eval ρ) (b.eval ρ) (h.eval ρ) (q.eval ρ) := by
  simp only [tg_query_data_m, Tg_query_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hE, rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_program_data_d (Γ n b z : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∃ c p q, Rd_entry_d n c Γ ∧ Rd_quad_d c b z p q ∧
    Rd_quad_d p (σ 0) (σ 1) (σ 2) (σ 3) ∧ Rd_triple_d q (σ 4) (σ 5) (σ 6)

def tg_program_data_m {d} (Γ n b z : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∃ c p q,
  ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, c, ⌜Γ⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(c, ⌜b⌝ₛ, ⌜z⌝ₛ, p, q) ∧
  ⌜rd_quad_m⌝ₚ(p, ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ) ∧ ⌜rd_triple0_m⌝ₚ(q, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

@[simp] theorem tg_program_data_closed_l {d} (Γ n b z : Term d) (σ : Fin 7 → Term d)
    (hΓ : Γ.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hσ : ∀ j, (σ j).freeSupport = []) : (tg_program_data_m Γ n b z σ).FreeClosed := by
  simp -implicitDefEqProofs [tg_program_data_m, Definitional.Formula.FreeClosed, hΓ, hn, hb, hz, hσ]

theorem tg_program_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ n b z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_program_data_m Γ n b z σ) ↔
      Tg_program_data_d (Γ.eval ρ) (n.eval ρ) (b.eval ρ) (z.eval ρ) (fun j => (σ j).eval ρ) := by
  simp only [tg_program_data_m, Tg_program_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rd_quad_sat_l hE, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
