import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound
import YesMetaZFC.Model.SetTheory.Internal.SourceFunctionSize

/-! # 相对秩层中的源内编号与可数图

在已有秩历史中逐项选择层号，再用给定编号域上的内部共尾性界统一界住它们。
成员归纳覆盖同一编号控制的传递集合；ω 情形进一步控制可数图及其可数性见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_indexed_rank_l {ω μ c Z R α V A ι : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z) (hαZ : M.mem α Z)
    (hne : ∃ β, M.mem β α) (hVZ : M.mem V Z) (hv : Vr_d Z α V)
    (bound : Sc_omega_bound_d μ Z α) (hAZ : M.mem A Z) (hιZ : M.mem ι Z)
    (idx : Sc_index_d μ A ι) (sub : M.MemberSubset A V) : M.mem A V := by
  classical
  obtain ⟨B, F, hB, hF, cert⟩ := hv
  have fn := (cert V hVZ).2.1
  let φ : BinarySchema 4 := {
    body := Formula.forallMem (.bound 2) (.imp (rd_entry0_m .newest (.bound 2) (.bound 4))
      (Formula.existsMem (.bound 5) (.conj (rd_entry0_m (.bound 2) .newest (.bound 7))
        (Formula.subset (.bound 1) .newest)))) }
  let ρ : Env M 4 := ⟨Fin.cases A (Fin.cases ι (Fin.cases B (fun _ => F))), fun _ => A⟩
  have sat i β : φ.denote ρ i β ↔ ∀ x, M.mem x A → Rd_entry_d x i ι →
      ∃ U, M.mem U B ∧ Rd_entry_d β U F ∧ M.MemberSubset x U := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_subset_iff]; rfl
  -- 编号处只要求选出一个足够的较早层；不存在该编号的元素时任选已有层号。
  obtain ⟨f, hfZ, hf, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.forallMem _ (.imp (rd_entry0_delta_l ..) (.existsMem _ (.conj (rd_entry0_delta_l ..) (.atom ..)))))
    ρ (Fin.cases hAZ (Fin.cases hιZ (Fin.cases hB (fun _ => hF)))) hμZ hαZ (fun i hi => by
      by_cases hx : ∃ x, M.mem x A ∧ Rd_entry_d x i ι
      · obtain ⟨x, hx, hxi⟩ := hx
        obtain ⟨β, hβ, U, hU, hβU, hxU⟩ := ((cert x (hZ A hAZ x hx)).2.2.2).mp (sub x hx)
        exact ⟨β, hβ, (sat i β).mpr fun y hy hyi =>
          ⟨U, hU, hβU, idx.injective y hy x hx i hi hyi hxi ▸ hxU⟩⟩
      · obtain ⟨β, hβ⟩ := hne
        exact ⟨β, hβ, (sat i β).mpr fun x hxA hxi => (hx ⟨x, hxA, hxi⟩).elim⟩)
  obtain ⟨β, hβ, hb⟩ := bound f hfZ hf
  -- 层号严格低于 β，使 A 的全部成员进入同一个 Vβ，从而 A 本身进入 Vα。
  obtain ⟨U, hU, hβU⟩ := fn.2.1 β hβ
  refine ((cert A hAZ).2.2.2).mpr ⟨β, hβ, U, hU, hβU, fun x hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ := idx.total x hx
  obtain ⟨γ, _, hiγ⟩ := hf.2.1 i hi
  obtain ⟨W, hW, hγW, hxW⟩ := (sat i γ).mp (select i γ hiγ) x hx hxi
  exact ((cert x (hZ A hAZ x hx)).2.2.1 β hβ U hU hβU).mpr
    ⟨γ, hb i γ hiγ, W, hW, hγW, hxW⟩

/-- 同一源内编号控制传递域的全部成员，因而可直接用于成员归纳。 -/
theorem sc_indexed_transitive_rank_l {ω μ c Z R α V D ι : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z) (hαZ : M.mem α Z)
    (hne : ∃ β, M.mem β α) (hVZ : M.mem V Z) (hv : Vr_d Z α V)
    (bound : Sc_omega_bound_d μ Z α) (hDZ : M.mem D Z) (hDt : M.TransitiveSet D)
    (hιZ : M.mem ι Z) (idx : Sc_index_d μ D ι) : M.mem D V := by
  let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 1)) (.mem .newest (.bound 2)) }
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => V), fun _ => V⟩
  have sat x : φ.denote ρ x ↔ M.mem x D → M.mem x V := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]; rfl
  have all x (hx : M.mem x D) : M.mem x V := by
    apply (sat x).mp (ZF.mem_ind_l M hZF I φ ρ ?_ x) hx
    intro x ih
    apply (sat x).mpr
    intro hx
    exact sc_indexed_rank_l hZF hω hZ hm theory hμZ hαZ hne hVZ hv bound
      (hZ D hDZ x hx) hιZ
      ⟨idx.ordinal, fun y hy => idx.total y (hDt x hx y hy),
        fun y hy => idx.functional y (hDt x hx y hy),
        fun y hy z hz => idx.injective y (hDt x hx y hy) z (hDt x hx z hz)⟩
      (fun y hy => (sat y).mp (ih y hy) (hDt x hx y hy))
  exact sc_indexed_rank_l hZF hω hZ hm theory hμZ hαZ hne hVZ hv bound hDZ hιZ idx all

/-- 内部不可数共尾性已蕴含极限性，只需排除空序数。 -/
theorem sc_omega_bound_limit_l {ω c Z R α : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hωZ : M.mem ω Z) (hαZ : M.mem α Z)
    (ho : M.IsOrdinal α) (hne : ∃ β, M.mem β α) (bound : Sc_omega_bound_d ω Z α) : M.IsLimitOrdinal α := by
  refine ⟨ho, hne, fun β hβ => ?_⟩
  obtain ⟨f, C, hf, _, fn, eq⟩ := sc_constant_l hZF hω hZ hm theory hωZ (hZ α hαZ β hβ)
  have fn := fn.retarget_l (fun x y h => ((eq x y).mp h).2 ▸ hβ)
  obtain ⟨γ, hγ, hg⟩ := bound f hf fn
  obtain ⟨z, _, hz⟩ := hω.1.1
  exact ⟨γ, hγ, hg z β ((eq z β).mpr ⟨hz, rfl⟩)⟩

/-- 可数传递域到严格秩层的源内函数，其图和给定的可数性见证均属于该秩层。 -/
theorem sc_countable_function_rank_l {ω c Z R α V D σ η : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hωZ : M.mem ω Z) (hαZ : M.mem α Z)
    (hne : ∃ β, M.mem β α) (hVZ : M.mem V Z) (hv : Vr_d Z α V)
    (bound : Sc_omega_bound_d ω Z α) (hωV : M.MemberSubset ω V) (hDt : M.TransitiveSet D)
    (hσZ : M.mem σ Z) (hηZ : M.mem η Z) (fn : Fn0_d D V σ)
    (countable : M.IsSetInjectionFromTo I η σ ω) : M.mem σ V ∧ M.mem η V := by
  obtain ⟨hDZ, ι, hιZ, hι⟩ := sc_domain_numbering_l hZF hω hZ hm theory hωZ hηZ hσZ countable fn
  have hDV := sc_indexed_transitive_rank_l hZF hω hZ hm theory hωZ hαZ hne hVZ hv bound hDZ hDt hιZ
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) hι)
  have ht := hv.transitive_l hZF hZ hVZ
  have ho : M.IsOrdinal α := by
    obtain ⟨_, _, _, _, cert⟩ := hv
    exact (cert V hVZ).1
  have hl := sc_omega_bound_limit_l hZF hω hZ hm theory hωZ hαZ ho hne bound
  have hσV := sc_indexed_rank_l hZF hω hZ hm theory hωZ hαZ hne hVZ hv bound hσZ hηZ
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) countable) (fun p hp => by
      obtain ⟨x, hx, y, hy, hxy⟩ := fn.1 p hp
      exact hv.kpair_mem_l hZF hZ hVZ hl (ht D hDV x hx) hy (hZ σ hσZ p hp) hxy)
  have hn := fn0_of_function_l (ZF.modelsKP hZF) countable.1
  obtain ⟨ξ, hξ, hi⟩ := sc_graph_numbering_l hZF hω hZ hm theory hωZ hσZ hωZ hηZ hηZ countable hn
  refine ⟨hσV, sc_indexed_rank_l hZF hω hZ hm theory hωZ hαZ hne hVZ hv bound hηZ hξ
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) hi) (fun p hp => ?_)⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hn.1 p hp
  exact hv.kpair_mem_l hZF hZ hVZ hl (ht σ hσV x hx) (hωV y hy) (hZ η hηZ p hp) hxy

end YesMetaZFC.SetTheory.Internal
