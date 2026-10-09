import YesMetaZFC.Model.SetTheory.Internal.TypeTruth
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite

/-! # 查询域对公式码替换的封闭性

查询域只约束名字列，允许全部自然数公式码。这个有界条件可送到初等像，
因此目标查询不必属于旧查询的逐点像，限制算子仍可在同一名字列内往返。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tt_slots_d (ω D : M.Domain) : Prop := ∀ p z e w,
  M.mem p D → M.mem z ω → M.mem w ω → KPair_d M p z e → ∃ q, M.mem q D ∧ KPair_d M q w e

def tt_slots_m {d} (ω D : Term d) : Formula 1 d := set[d] ⟪
  ∀ p ∈ ⌜D⌝ₛ, ∀ z ∈ ⌜ω⌝ₛ, ∀ a ∈ p, ∀ e ∈ a, ∀ w ∈ ⌜ω⌝ₛ,
    ⌜kpair0_m⌝ₚ(p, z, e) → (∃ q ∈ ⌜D⌝ₛ, ⌜kpair0_m⌝ₚ(q, w, e))⟫
derive_free_closed tt_slots_m

theorem tt_slots_delta_l {d} (ω D : Term d) : (tt_slots_m ω D).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (kpair0_delta_l ..) (.existsMem _ (kpair0_delta_l ..)))))))

theorem tt_slots_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D : Term d) :
    Formula.satisfies ρ (tt_slots_m ω D) ↔ Tt_slots_d (ω.eval ρ) (D.eval ρ) := by
  simp only [tt_slots_m, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_imp_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  constructor
  · intro h p z e w hp hz hw code
    obtain ⟨a, ha, he⟩ := (kpair_union_l M code e).mpr (Or.inr rfl)
    exact h p hp z hz a ha e he w hw code
  · intro h p hp z hz _ _ e _ w hw code
    exact h p z e w hp hz hw code

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tt_pool_d.slots_l {ω n U D : M.Domain} (h : Tt_pool_d I ω n U D) : Tt_slots_d ω D := by
  obtain ⟨N, E, _, _, prod⟩ := h
  intro p z e w hp _ hw code
  obtain ⟨z', _, e', he, cp⟩ := (prod p).mp hp
  obtain ⟨ez, ee⟩ := kpair_injective_l M cp code
  subst z' e'
  obtain ⟨q, cq⟩ := (I).total w e
  exact ⟨q, (prod q).mpr ⟨w, hw, e, he, cq⟩, cq⟩

theorem Smap_d.type_slots_l {ω X R c Y S d j D D' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hωX : M.mem ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hD : Rd_entry_d D D' j) (h : Tt_slots_d ω D) : Tt_slots_d ω D' := by
  have hωj := hj.omega_l I hZF hω hX hY hm hn hωX
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => ω), fun _ => ω⟩
  let η : Env M 2 := ⟨Fin.cases D' (fun _ => ω), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (tt_slots_m (.bound 1) .newest)
    (tt_slots_m_freeClosed _ _ rfl rfl) (tt_slots_delta_l ..) ρ η (Fin.cases hD (fun _ => hωj))
  exact (tt_slots_sat_l hZF.1 η (.bound 1) .newest).mp
    (tr.mp ((tt_slots_sat_l hZF.1 ρ (.bound 1) .newest).mpr h))

end YesMetaZFC.SetTheory.Internal
