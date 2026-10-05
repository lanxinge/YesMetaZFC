import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSmallRestriction
import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingCountableBound

/-! # 复制的序数限制在目标内还原为完整小域限制

所属模型内的旧图 σ 在 κ 以下有共同小界时，先分离 σ↾κ，再由已证明的
有限幂一致性搬运此图。复制在支撑上等于 σ，故该图正是新复制的限制。
随后关系回拉与塌缩自动恢复整个小传递域上的复制图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_restriction_l {ω κ K X R μ K₀ Z V K' Y S c d j σ U ζ B f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω μ K₀ Z V)
    (target : Ep_source_d hZF ω μ K' Y S) (agree : Ea_agree_d ω μ Z Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hU : M.TransitiveSet U) (hσ : Fn0_d U Z σ) (hσZ : M.mem σ Z) (hκσ : Rd_entry_d κ ζ σ)
    (bounded : ∀ a b, M.mem a κ → Rd_entry_d a b σ → M.mem a μ ∧ M.mem b μ)
    (fixed : ∀ a b, M.mem a κ → Rd_entry_d a b σ → Rd_entry_d a b j)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  have κZ := (rd_entry_transitive_l owner.transitive hσZ hκσ).1
  obtain ⟨b, code⟩ := owner.code
  let ρ : Env M 2 := ⟨Fin.cases κ (fun _ => μ), fun _ => κ⟩
  let φ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)) }
  have sat q : φ.denote ρ q ↔ ∃ a, M.mem a κ ∧ ∃ v, M.mem v μ ∧ KPair_d M q a v := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨p, hpZ, spec⟩ := sc_separate_source_l I hZF source.omega owner.transitive code owner.theory φ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ρ (Fin.cases κZ (fun _ => owner.cardinal_mem)) hσZ
  have shape q (hq : M.mem q p) : ∃ a, M.mem a κ ∧ ∃ v, M.mem v μ ∧ KPair_d M q a v :=
    (sat q).mp ((spec q).mp hq).2
  have entry a v : Rd_entry_d a v p ↔ M.mem a κ ∧ Rd_entry_d a v σ := by
    constructor
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨a', ha', v', _, hq'⟩ := shape q hqp
      obtain ⟨ea, _⟩ := kpair_injective_l M hq' hq
      exact ⟨ea ▸ ha', q, hq, ((spec q).mp hqp).1⟩
    · rintro ⟨ha, q, hq, hqσ⟩
      exact ⟨q, hq, (spec q).mpr ⟨hqσ, (sat q).mpr ⟨a, ha, v, (bounded a v ha ⟨q, hq, hqσ⟩).2, hq⟩⟩⟩
  have hpY := agree.relation_l hZF owner target hpZ (fun q hq => by
    obtain ⟨a, ha, v, hv, hq'⟩ := shape q hq
    exact ⟨a, (bounded a v ha ((entry a v).mp ⟨q, hq', hq⟩).2).1, v, hv, hq'⟩)
  have res : M.IsRestrictionOf I p j κ := by
    refine ⟨fun q hq => (shape q hq).elim fun a ha => ha.2.elim fun v hv => ⟨a, v, hv.2⟩, fun a v => ⟨?_, ?_⟩⟩
    · intro hav
      obtain ⟨ha, hav⟩ := (entry a v).mp hav
      exact ⟨ha, fixed a v ha hav⟩
    · rintro ⟨ha, hav⟩
      obtain ⟨w, _, haw⟩ := hσ.2.1 a (hU κ (hσ.bound_l hκσ).1 a ha)
      exact (entry a v).mpr ⟨ha, hj.1.1.1.2 a w v (fixed a w ha haw) hav ▸ haw⟩
  exact smap_small_restriction_l hZF source target hm hn hj hpY res hB hf bij

/-- 模型内可数性实际产生小界，故只要求 φ 以下逐层一致，无需 φ 上的全部子集一致。 -/
theorem ep_copy_countable_restriction_l
    {ω κ K X R φ K₀ Z V K' Y S c d j σ U R₀ c₀ d₀ ι B f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω φ K₀ Z V)
    (target : Ep_source_d hZF ω φ K' Y S) (agree : ∀ μ, M.mem μ φ → Ea_agree_d ω μ Z Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hU : M.TransitiveSet U) (h₀ : Smem_d I c₀ U R₀) (h₁ : Smem_d I d₀ Z V)
    (hσ : Smap_d I ω c₀ d₀ U Z σ) (hσZ : M.mem σ Z) (hιZ : M.mem ι Z)
    (countable : M.IsSetInjectionFromTo I ι σ ω) (hκ : M.IsOrdinal κ) (hκφ : Rd_entry_d κ φ σ)
    (regular : Sc_omega_bound_d ω Z φ)
    (fixed : ∀ a b, M.mem a κ → Rd_entry_d a b σ → Rd_entry_d a b j)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  obtain ⟨μ, hμ, bounded⟩ := smap_countable_bound_l hZF owner hU h₀ h₁ hσ hσZ hιZ countable hκ hκφ regular
  have hωμ : M.MemberSubset ω μ := by
    intro i hi
    have hiκ := source.below i hi
    obtain ⟨v, _, hiv⟩ := hσ.1.1.2.2 i (hU κ (hσ.1.1.input_mem_of_pairMember hκφ) i hiκ)
    exact (bounded i v hiκ hiv).1
  obtain ⟨K₁, owner'⟩ := owner.rebase_l hZF (owner.transitive φ owner.cardinal_mem μ hμ) hωμ
  obtain ⟨K₂, target'⟩ := target.rebase_l hZF (target.transitive φ target.cardinal_mem μ hμ) hωμ
  exact ep_copy_restriction_l hZF source owner' target' (agree μ hμ) hm hn hj hU
    (fn0_of_function_l (ZF.modelsKP hZF) hσ.1.1) hσZ hκφ bounded fixed hB hf bij

end YesMetaZFC.SetTheory.LargeCardinal
