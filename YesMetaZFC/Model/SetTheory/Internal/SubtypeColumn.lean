import YesMetaZFC.Model.SetTheory.Internal.SubtypeSyntax

/-! # 子类型名字列的有界原式

所有七个名字均在给定名字域中量化，原变量列与固定槽位保持不变。
这使定义域参数的统一替换能够覆盖超幂中没有原像的新名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_column_d (ω n κ τ m N w b : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  Fn0_d b N C ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧ ∃ v : Fin 7 → M.Domain,
    (∀ i, M.mem (v i) N) ∧ (∀ i, Rd_entry_d (σ i) (v i) C) ∧ Ts_names_d ω n κ τ m w v

def ts_column_m {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜b⌝ₛ, ⌜N⌝ₛ, ⌜C⌝ₛ) ∧ (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜C⌝ₛ)) ∧
  (∃ v₀ ∈ ⌜N⌝ₛ, ∃ v₁ ∈ ⌜N⌝ₛ, ∃ v₂ ∈ ⌜N⌝ₛ, ∃ v₃ ∈ ⌜N⌝ₛ, ∃ v₄ ∈ ⌜N⌝ₛ, ∃ v₅ ∈ ⌜N⌝ₛ, ∃ v₆ ∈ ⌜N⌝ₛ,
    (⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, ⌜C⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, ⌜C⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, ⌜C⌝ₛ)) ∧
    ⌜ts_names_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜κ⌝ₛ, ⌜τ⌝ₛ, ⌜m⌝ₛ, ⌜w⌝ₛ, v₀, v₁, v₂, v₃, v₄, v₅, v₆))⟫

@[simp] theorem ts_column_closed_l {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hN : N.freeSupport = []) (hu : w.freeSupport = []) (hb : b.freeSupport = [])
    (hC : C.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) : (ts_column_m ω n κ τ m N w b C σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_column_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hN, hu, hb, hC, hσ]

theorem ts_names_delta_l {d} (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) :
    (ts_names_m ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆).IsDelta0 :=
  .conj (kpair0_delta_l ..) (.conj (.atom ..) (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (kpair0_delta_l ..))))))

theorem ts_column_delta_l {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) :
    (ts_column_m ω n κ τ m N w b C σ).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))))
        (ts_names_delta_l ..))))))))))

theorem ts_column_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_column_m ω n κ τ m N w b C σ) ↔ Ts_column_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (N.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun i => (σ i).eval ρ) (C.eval ρ) := by
  simp only [ts_column_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, ts_names_sat_l hE, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fn, orig, v₀, h₀, v₁, h₁, v₂, h₂, v₃, h₃, v₄, h₄, v₅, h₅, v₆, h₆, ⟨s₀, s₁, s₂, s₃, s₄, s₅, s₆⟩, vals⟩
    exact ⟨fn, orig, _, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅
      (Fin.cases h₆ (fun j => Fin.elim0 j))))))), Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃
      (Fin.cases s₄ (Fin.cases s₅ (Fin.cases s₆ (fun j => Fin.elim0 j))))))), vals⟩
  · rintro ⟨fn, orig, v, mem, slots, vals⟩
    exact ⟨fn, orig, v 0, mem 0, v 1, mem 1, v 2, mem 2, v 3, mem 3, v 4, mem 4, v 5, mem 5, v 6, mem 6,
      ⟨slots 0, slots 1, slots 2, slots 3, slots 4, slots 5, slots 6⟩, vals⟩

theorem Ts_column_d.query_l {ω n κ τ m U N w b z q C : M.Domain} {σ : Fin 7 → M.Domain}
    (h : Ts_column_d ω n κ τ m N w b σ C) (names : Tn_names_d n U N)
    (constants : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U)
    (code : KPair_d M q z C) : Ts_query_d ω n κ τ m U w b σ z q := by
  obtain ⟨fn, orig, v, _, slots, vals⟩ := h
  exact ⟨constants, N, C, v, names, fn, orig, slots, vals, code⟩

theorem Ts_query_d.column_l (hE : Extensional M) {ω n κ τ m U N w b z q : M.Domain}
    {σ : Fin 7 → M.Domain} (h : Ts_query_d ω n κ τ m U w b σ z q) (names : Tn_names_d n U N) :
    ∃ C, Ts_column_d ω n κ τ m N w b σ C ∧ KPair_d M q z C := by
  obtain ⟨_, N', C, v, names', fn, orig, slots, vals, code⟩ := h
  have eq := hE.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  exact ⟨C, ⟨fn, orig, v, fun i => (fn.bound_l (slots i)).2, slots, vals⟩, code⟩

/-- 原查询属于新查询域时，它的六个实际常量自动属于新常量域。 -/
theorem Ts_query_d.pool_l (hKP : M.Models KP) {ω n κ τ m U V D w b z q : M.Domain} {σ : Fin 7 → M.Domain}
    (h : Ts_query_d ω n κ τ m U w b σ z q) (on : M.IsOrdinal n)
    (pool : Tt_pool_d (kp_pair_l hKP) ω n V D) (hq : M.mem q D) : Ts_query_d ω n κ τ m V w b σ z q := by
  obtain ⟨_, N₀, C, v, _, fn, orig, slots, vals, code⟩ := h
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z', _, C', hC, code'⟩ := (prod q).mp hq
  obtain ⟨hz, hc⟩ := kpair_injective_l M code' code
  subst z' C'
  obtain ⟨b', _, fn'⟩ := (seq C).mp hC
  have eq := (fn0_of_function_l hKP fn').domain_eq_l hKP.1 fn
  subst b'
  have value i x (cp : KPair_d M (v i) x x) : M.mem x V := by
    rcases (names (v i)).mp (fn'.output_mem_of_pairMember (slots i)) with hi | eq | ⟨y, hy, cy⟩
    · exact (cp.not_transitive_l M (KP.mem_irrefl_d hKP) (on.mem hi).transitive).elim
    · exact (cp.not_transitive_l M (KP.mem_irrefl_d hKP) (eq.symm ▸ on.transitive)).elim
    · exact (kpair_injective_l M cy cp).1 ▸ hy
  exact ⟨⟨value 0 w vals.1, value 2 m vals.2.2.1, value 3 n vals.2.2.2.1,
      value 4 τ vals.2.2.2.2.1, value 5 κ vals.2.2.2.2.2.1, value 6 ω vals.2.2.2.2.2.2⟩,
    N, C, v, names, fn0_of_function_l hKP fn', orig, slots, vals, code⟩

end YesMetaZFC.SetTheory.Internal
