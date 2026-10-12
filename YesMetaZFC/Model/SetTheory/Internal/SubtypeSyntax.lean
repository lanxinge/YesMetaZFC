import YesMetaZFC.Model.SetTheory.Internal.SubtypeCode

/-! # 裸类型中固定子类型查询的原公式

量化的名字列仍保留原前缀，并在既定程序槽位填入六个对角常量及指定点。
本文件只展开实际查询的编码，不用语义等价替换类型中的字面成员条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def ts_names_m {d} (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) : Formula 1 d := set[d] ⟪
  ⌜kpair0_m⌝ₚ(⌜v₀⌝ₛ, ⌜w⌝ₛ, ⌜w⌝ₛ) ∧ ⌜v₁⌝ₛ = ⌜n⌝ₛ ∧ ⌜kpair0_m⌝ₚ(⌜v₂⌝ₛ, ⌜m⌝ₛ, ⌜m⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(⌜v₃⌝ₛ, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜v₄⌝ₛ, ⌜τ⌝ₛ, ⌜τ⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(⌜v₅⌝ₛ, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜v₆⌝ₛ, ⌜ω⌝ₛ, ⌜ω⌝ₛ)⟫
derive_free_closed ts_names_m

theorem ts_names_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) :
    Formula.satisfies ρ (ts_names_m ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆) ↔
      Ts_names_d (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (w.eval ρ)
        (Fin.cases (v₀.eval ρ) (Fin.cases (v₁.eval ρ) (Fin.cases (v₂.eval ρ) (Fin.cases (v₃.eval ρ)
          (Fin.cases (v₄.eval ρ) (Fin.cases (v₅.eval ρ) (fun _ => v₆.eval ρ))))))) := by
  simp only [ts_names_m, Ts_names_d, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, kpair0_sat_l hE]
  rfl

def ts_query_m {d} (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  (⌜w⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜m⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜n⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜τ⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜ω⌝ₛ ∈ ⌜U⌝ₛ) ∧
  (∃ N C v₀ v₁ v₂ v₃ v₄ v₅ v₆, ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fn0_m⌝ₚ(⌜b⌝ₛ, N, C) ∧
    (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧
    (⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, C) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, C) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, C)) ∧
    ⌜ts_names_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜κ⌝ₛ, ⌜τ⌝ₛ, ⌜m⌝ₛ, ⌜w⌝ₛ, v₀, v₁, v₂, v₃, v₄, v₅, v₆) ∧
    ⌜kpair0_m⌝ₚ(⌜q⌝ₛ, ⌜z⌝ₛ, C))⟫

@[simp] theorem ts_query_closed_l {d} (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hW : w.freeSupport = []) (hb : b.freeSupport = [])
    (hz : z.freeSupport = []) (hq : q.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_query_m ω n κ τ m U w b z q σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_query_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hU, hW, hb, hz, hq, hσ]

theorem ts_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_query_m ω n κ τ m U w b z q σ) ↔ Ts_query_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (U.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun j => (σ j).eval ρ) (z.eval ρ) (q.eval ρ) := by
  simp only [ts_query_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, tn_names0_sat_l hKP, fn0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    ts_names_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨constants, N, C, v₀, v₁, v₂, v₃, v₄, v₅, v₆, names, fn, old, slots, values, pair⟩
    obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := slots
    exact ⟨constants, N, C, _, names, fn, old,
      Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
        (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j))))))), values, pair⟩
  · rintro ⟨constants, N, C, v, names, fn, old, slots, values, pair⟩
    refine ⟨constants, N, C, v 0, v 1, v 2, v 3, v 4, v 5, v 6, names, fn, old,
      ⟨slots 0, slots 1, slots 2, slots 3, slots 4, slots 5, slots 6⟩, ?_, pair⟩
    exact values

def ts_subtype_m {d} (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  .conj (.mem τ κ) (.conj (Formula.subset n m) (.existsE (.conj
    (ts_query_m ω.weaken n.weaken κ.weaken τ.weaken m.weaken U.weaken w.weaken b.weaken z.weaken .newest
      (fun j => (σ j).weaken)) (.mem .newest u.weaken))))

@[simp] theorem ts_subtype_closed_l {d} (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hW : w.freeSupport = []) (hb : b.freeSupport = [])
    (hz : z.freeSupport = []) (hu : u.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_subtype_m ω n κ τ m U w b z u σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_subtype_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hU, hW, hb, hz, hu, hσ]

theorem ts_subtype_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_subtype_m ω n κ τ m U w b z u σ) ↔ Ts_subtype_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (U.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun j => (σ j).eval ρ) (z.eval ρ) (u.eval ρ) := by
  simp only [ts_subtype_m, Ts_subtype_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, ts_query_sat_l hKP, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
