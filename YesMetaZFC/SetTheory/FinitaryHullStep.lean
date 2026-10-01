import YesMetaZFC.SetTheory.FinitaryHullSyntax
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 有限元闭包的一步构造及可数性

一步取旧集合与全部运算值的并。参数列空间的可数性由实际内部编号给出，
运算图限制到规则与参数的积后，其值域仍可数。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ZF.fc_step_exists_l (hZF : M.Models ZF) {ω X T D K A}
    (hK : M.IsSetFunctionFromTo I K D X) (hA : M.MemberSubset A X) :
    ∃ B, Fc_step_d I ω T K A B ∧ M.MemberSubset B X := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push T).push K).push A
  let φ : UnarySchema 4 := {
    body := .disj (.mem .newest (.bound 1)) (fc_value_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hφ x : φ.denote ρ x ↔ M.mem x A ∨ Fc_value_d I ω T K A x := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, fc_value_sat_l I hZF.1]
    rfl
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ X
  refine ⟨B, fun x => (hB x).trans ?_, fun x hx => ((hB x).mp hx).1⟩
  rw [show Formula.satisfies (ρ.push x) φ.body ↔ _ from hφ x]
  exact ⟨And.right, fun h => ⟨h.elim (hA x)
    (fun ⟨_, _, _, _, _, _, _, _, hx⟩ => hK.output_mem_of_pairMember hx), h⟩⟩

theorem ZF.fc_step_countable_l (hZF : M.Models ZF) {ω X S T D K A B} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hT : M.CardinalLessOrEqual I T ω)
    (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) (hB : Fc_step_d I ω T K A B) :
    M.CardinalLessOrEqual I B ω := by
  obtain ⟨L, hL, hl⟩ := ZF.fseq_countable_space_l I hZF hω ha
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I T L
  have hw := ZF.countable_product_l I hZF hω hT hl hW
  have hWD : M.MemberSubset W D := by
    intro p hp
    obtain ⟨t, ht, s, hs, hc⟩ := (hW p).mp hp
    obtain ⟨n, hn, hs⟩ := (hL s).mp hs
    exact (hD p).mpr ⟨t, ht, s, (hS s).mpr ⟨n, hn, hs.mono_target_l I hA⟩, hc⟩
  obtain ⟨G, hG⟩ := ZF.exists_restriction hZF I K W
  have hg := hG.isSetFunctionFromTo hK hWD
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hg.1 hg.2.1
  have hgY : M.IsSetFunctionFromTo I G W Y := ⟨hg.1, hg.2.1, fun p hp => by
    obtain ⟨x, _, hx⟩ := hg.2.2 p hp
    exact ⟨x, (hY x).mpr ⟨p, hx⟩, hx⟩⟩
  have hy := ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) hw hgY (fun x hx => by
    obtain ⟨p, hp⟩ := (hY x).mp hx
    exact ⟨p, hg.input_mem_of_pairMember hp, hp⟩)
  have values x : Fc_value_d I ω T K A x ↔ M.mem x Y := by
    constructor
    · rintro ⟨n, s, t, p, hn, hs, ht, hp, hx⟩
      exact (hY x).mpr ⟨p, (hG.2 p x).mpr ⟨(hW p).mpr ⟨t, ht, s, (hL s).mpr ⟨n, hn, hs⟩, hp⟩, hx⟩⟩
    · intro hx
      obtain ⟨p, hp⟩ := (hY x).mp hx
      obtain ⟨hpW, hx⟩ := (hG.2 p x).mp hp
      obtain ⟨t, ht, s, hs, hc⟩ := (hW p).mp hpW
      obtain ⟨n, hn, hs⟩ := (hL s).mp hs
      exact ⟨n, s, t, p, hn, hs, ht, hc, hx⟩
  exact ZF.countable_union_two_l I hZF hω ha hy (fun x => (hB x).trans (or_congr Iff.rfl (values x)))

end YesMetaZFC.SetTheory
