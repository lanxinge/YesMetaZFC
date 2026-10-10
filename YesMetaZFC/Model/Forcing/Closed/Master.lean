import YesMetaZFC.Model.Forcing.Closed.Basic
import YesMetaZFC.Model.Forcing.Proper.Master.Basic
import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.SetTheory.IndexedChoice
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.CountableChain

/-! # 可数闭偏序的实际内部主下降链

枚举内部可数集合 N，在 N 内逐项遇到其稠密集。内部依赖选择产生整张 ω 链，
闭性给出下界；每个稠密集中的已选条件都在该下界以上，因而给出主性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z ω : M.Domain}
variable (O : Preord_d M B R) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 对稠密见证闭合的实际可数 N 中，每个正条件都有 N 主加强。 -/
theorem closed_mstr_l (hω : M.IsOmega ω) (hc : Closed_d I B R z ω) {N p}
    (hN : M.CardinalLessOrEqual I N ω) (hpN : M.mem p N) (hp : M.mem p B) (hz : p ≠ z)
    (hcl : ∀ D r, M.mem D N → M.mem r N → Dense_set_d M B R z D → M.mem r B → r ≠ z →
      ∃ q, M.mem q N ∧ M.mem q D ∧ Below_d M B R z q r) :
    ∃ q, Below_d M B R z q p ∧ Mstr_d M B R z N q := by
  classical
  obtain ⟨G, hG⟩ := hN
  obtain ⟨g, hg, hgr⟩ := ZF.injection_retract_l I hZF hG (fun _ h => h) hpN
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let θ : UnarySchema 3 := {
    body := .conj (.mem .newest (.bound 3)) (.neg (Formula.extensionalEq .newest (.bound 1))) }
  obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF θ ρ N
  have hA r : M.mem r A ↔ M.mem r N ∧ M.mem r B ∧ r ≠ z := by
    simpa only [θ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZFC.1] using! hA r
  let φ : UnarySchema 6 := {
    body := .conj (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))
      (.forallE (.imp (entry_m (.bound 3) .newest (.bound 4))
        (.imp (dense_set_m (.bound 7) (.bound 6) (.bound 5) .newest) (.mem (.bound 1) .newest)))) }
  have hφ i r q : φ.denote ((((ρ.push g).push i).push r)) q ↔
      Below_d M B R z q r ∧ ∀ D, Entry_d M i D g → Dense_set_d M B R z D → M.mem q D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, below_sat_l M hZFC.1,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, entry_sat_l M hZFC.1,
      dense_set_sat_l M hZFC.1, Formula.satisfies_mem_iff]
    rfl
  obtain ⟨F, hF, hf₀, hf⟩ := ZFC.indexed_choice_l I hZFC φ (ρ.push g) hω ((hA p).mpr ⟨hpN, hp, hz⟩) (by
    intro i r hi hr
    obtain ⟨hrN, hrB, hrz⟩ := (hA r).mp hr
    obtain ⟨D, hDN, hiD⟩ := hg.2.2 i hi
    by_cases hd : Dense_set_d M B R z D
    · obtain ⟨q, hqN, hqD, hqr⟩ := hcl D r hDN hrN hd hrB hrz
      exact ⟨q, (hA q).mpr ⟨hqN, hqr.1, hqr.2.1⟩,
        (hφ i r q).mpr ⟨hqr, fun D' hiD' _ => hg.1.2 i D D' hiD hiD' ▸ hqD⟩⟩
    · exact ⟨r, hr, (hφ i r r).mpr ⟨⟨hrB, hrz, O.1 r hrB⟩, fun D' hiD' hd' =>
        (hd (hg.1.2 i D' D hiD' hiD ▸ hd')).elim⟩⟩)
  have state {i r} (hir : Entry_d M i r F) := (hA r).mp (hF.output_mem_of_pairMember hir)
  have chain : Chain_d I B R z ω F := ⟨hF.mono_target_l I (fun r hr => ((hA r).mp hr).2.1),
    (fun _ _ hir => (state hir).2.2),
    fun i j r q hji hir hjq => ((hφ i r q).mp (hf i j r q hji hir hjq)).1.2.2⟩
  obtain ⟨q, hqB, hqz, hq⟩ := hc F chain
  obtain ⟨o, ho, _⟩ := hω.1.1
  refine ⟨q, ⟨hqB, hqz, hq o p (hf₀ o ho)⟩, hqB, hqz, fun D hDN hd r hr => ?_⟩
  obtain ⟨i, hi, hDi⟩ := hG.1.2.2 D hDN
  obtain ⟨j, hji, hj⟩ := hω.1.2 i hi
  obtain ⟨s, _, his⟩ := hF.2.2 i hi
  obtain ⟨t, _, hjt⟩ := hF.2.2 j hj
  have htD := ((hφ i s t).mp (hf i j s t hji his hjt)).2 D (hgr D i hDi) hd
  exact ⟨t, htD, (state hjt).1, r, ⟨hr.1, hr.2.1, O.1 r hr.1⟩,
    O.2 r q t hr.1 hqB (state hjt).2.1 hr.2.2 (hq j t hjt)⟩

end YesMetaZFC.Model.Forcing.Internal
