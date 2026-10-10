import YesMetaZFC.SetTheory.LargeCardinal.Measurable
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication
import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.CountableChain

/-! # 可测基数的正则性

每个有界初段的补集测度一。若短序列共尾，对其全部值取这些补集的交，
完备性给出非空的测度一集合，而共尾性迫使该交为空。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Measurable_d.regular_l (hZF : M.Models ZF) {κ : M.Domain} (h : Measurable_d I κ) : M.IsRegularCardinal I κ := by
  obtain ⟨card, ω, U, hω, hωκ, hU, hn, hc⟩ := h
  have limit := ZF.infiniteCardinal_isLimitOrdinal hZF I hω (ZF.omega_cardinal_l I hZF hω)
    ⟨card, ZF.exists_inclusionInjection hZF I (card.1.transitive ω hωκ)⟩
  have tail α (hα : M.mem α κ) : ∃ r, M.mem r U ∧ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ M.mem x α := by
    obtain ⟨f, ff⟩ := ZF.exists_identityBijection hZF I α
    obtain ⟨r, hr, rs⟩ := ed_range_complement_l I hZF hU hn hc hα (ff.1.1.mono_target_l I (card.1.transitive α hα))
    exact ⟨r, hr, fun x => (rs x).trans (and_congr_right fun _ => not_congr
      ⟨fun ⟨_, _, hx⟩ => ff.1.1.output_mem_of_pairMember hx, fun hx => ff.2 x hx⟩)⟩
  refine ⟨card, limit.hasCofinalOrdinalSequence_self hZF I, fun μ ⟨f, seq⟩ => ?_⟩
  rcases card.1.trichotomy hZF.1 seq.isIncreasing.1.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with eq | lt | small
  · exact Or.inl (hZF.1.eq_of_same_members κ μ eq)
  · exact Or.inr lt
  apply False.elim
  have fn := seq.isSetFunctionFromTo
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => κ), fun _ => κ⟩
  let φ : BinarySchema 2 := {
    body := .forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
      (.neg (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4)) (.mem (.bound 1) .newest)))))) }
  have read i r : φ.denote ρ i r ↔ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ ∃ α, M.PairMember I i α f ∧ M.mem x α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  have total i (hi : M.mem i μ) : ∃ r, φ.denote ρ i r ∧ M.mem r U := by
    obtain ⟨α, hα, hiα⟩ := fn.2.2 i hi
    obtain ⟨r, hr, rs⟩ := tail α hα
    exact ⟨r, (read i r).mpr (fun x => (rs x).trans (and_congr_right fun _ => not_congr
      ⟨fun hx => ⟨α, hiα, hx⟩, fun ⟨β, hiβ, hx⟩ => fn.1.2 i β α hiβ hiα ▸ hx⟩)), hr⟩
  have unique i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s :=
    hZF.1.eq_of_same_members r s (fun x => ((read i r).mp hr x).trans ((read i s).mp hs x).symm)
  obtain ⟨g, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (fun i hi => (total i hi).imp fun _ hr => hr.1) (fun i _ => unique i) (fun i r hi hr => by
      obtain ⟨s, hs, hsU⟩ := total i hi
      exact unique i s r hs hr ▸ hsU)
  obtain ⟨r, hr, rs⟩ := hc μ small g (fn0_of_function_l (ZF.modelsKP hZF) gf)
  obtain ⟨x, hx⟩ := hU.2.1 r hr
  obtain ⟨hxκ, all⟩ := (rs x).mp hx
  obtain ⟨A, range, un⟩ := seq.isLimit.2.2
  obtain ⟨α, hα, hxα⟩ := (un x).mp hxκ
  obtain ⟨i, hiα⟩ := (range α).mp hα
  have hi := fn.input_mem_of_pairMember hiα
  obtain ⟨s, hs, his⟩ := gf.2.2 i hi
  exact (((read i s).mp ((gs i s).mp his).2 x).mp (all i hi s hs his)).2 ⟨α, hiα, hxα⟩

end YesMetaZFC.SetTheory.LargeCardinal
