import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.SetTheory.IndexedChoice
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 内部可数有向族的链化与 club 闭性

单射的反向函数给出内部 ω 枚举，依赖选择逐项吸收枚举值；所得递增链与原族
具有相同的并。因此 club 的链闭性足以处理任意非空内部可数有向子族。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem cc_directed_chain_l (hZFC : M.Models ZFC) {ω A U} (hω : M.IsOmega ω)
    (hA : M.CardinalLessOrEqual I A ω) (hn : ∃ a, M.mem a A)
    (hd : ∀ a b, M.mem a A → M.mem b A → ∃ c, M.mem c A ∧ M.MemberSubset a c ∧ M.MemberSubset b c)
    (hU : M.IsUnionOf U A) : ∃ F, M.IsSetFunctionFromTo I F ω A ∧ Cc_increasing_d I F ∧ Cc_union_d I F U := by
  have hZF := models_zf_l hZFC
  obtain ⟨a, ha⟩ := hn
  obtain ⟨G, hG⟩ := hA
  obtain ⟨g, hg, hgr⟩ := ZF.injection_retract_l I hZF hG (fun _ h => h) ha
  let ρ : Env M 1 := ⟨fun _ => g, fun _ => g⟩
  let φ : UnarySchema 3 := {
    body := .conj (Formula.subset (.bound 1) .newest) (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4)) (Formula.subset .newest (.bound 1)))) }
  have hφ i x y : φ.denote ((ρ.push i).push x) y ↔ M.MemberSubset x y ∧
      ∀ b, M.PairMember I i b g → M.MemberSubset b y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨F, hF, _, hf⟩ := indexed_choice_l I hZFC φ ρ hω ha (by
    intro i x hi hx
    obtain ⟨b, hb, hib⟩ := hg.2.2 i hi
    obtain ⟨c, hc, hxc, hbc⟩ := hd x b hx hb
    exact ⟨c, hc, (hφ i x c).mpr ⟨hxc, fun b' hib' => hg.1.2 i b' b hib' hib ▸ hbc⟩⟩)
  refine ⟨F, hF, ZF.cc_increasing_of_successor_l I hZF hω hF
    (fun i j x y hij hix hjy => ((hφ i x y).mp (hf i j x y hij hix hjy)).1), fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨b, hb, hxb⟩ := (hU x).mp hx
    obtain ⟨i, hi, hbi⟩ := hG.1.2.2 b hb
    obtain ⟨j, hij, hj⟩ := hω.1.2 i hi
    obtain ⟨c, _, hic⟩ := hF.2.2 i hi
    obtain ⟨d, _, hjd⟩ := hF.2.2 j hj
    exact ⟨j, d, hjd, ((hφ i c d).mp (hf i j c d hij hic hjd)).2 b (hgr b i hbi) x hxb⟩
  · rintro ⟨i, b, hib, hxb⟩
    exact (hU x).mpr ⟨b, hF.output_mem_of_pairMember hib, hxb⟩

theorem cc_club_directed_l (hZFC : M.Models ZFC) {ω X C A U} (hω : M.IsOmega ω)
    (hC : Cc_club_d I ω X C) (hAC : M.MemberSubset A C) (hA : M.CardinalLessOrEqual I A ω)
    (hn : ∃ a, M.mem a A)
    (hd : ∀ a b, M.mem a A → M.mem b A → ∃ c, M.mem c A ∧ M.MemberSubset a c ∧ M.MemberSubset b c)
    (hU : M.IsUnionOf U A) : M.mem U C := by
  obtain ⟨F, hF, hm, hu⟩ := cc_directed_chain_l I hZFC hω hA hn hd hU
  exact hC.closed F U (hF.mono_target_l I hAC) hm hu

end YesMetaZFC.SetTheory.ZFC
