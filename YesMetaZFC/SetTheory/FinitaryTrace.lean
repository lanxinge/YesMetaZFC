import YesMetaZFC.SetTheory.FinitaryTraceSyntax
import YesMetaZFC.SetTheory.FinitaryClub

/-! # 最小有限元闭包在指定子集上的实际 club

club 的成员恰是自身最小闭包在 X 上的交集。闭包最小性把任意内部递增链
同步提升成递增闭包链，有限参数截取证明其并闭合，故无需猜测交集像的闭性。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem fc_trace_club_l (hZFC : M.Models ZFC) {ω H S T D K A X} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω H S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D H) (hT : M.CardinalLessOrEqual I T ω)
    (hA : M.MemberSubset A H) (ha : M.CardinalLessOrEqual I A ω) (hX : M.MemberSubset X H) :
    ∃ C, Cc_club_d I ω X C ∧ ∀ Y, M.mem Y C ↔ ∃ N, Fc_trace_d I ω H T K A X Y N := by
  have hZF := models_zf_l hZFC
  obtain ⟨C₀, hC₀, e₀⟩ := cc_all_l I hZFC hω H
  obtain ⟨C₁, hC₁, e₁⟩ := cc_all_l I hZFC hω X
  have count {Y N} (hYN : M.MemberSubset Y N) (hn : M.CardinalLessOrEqual I N ω) : M.CardinalLessOrEqual I Y ω := by
    obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I hYN
    obtain ⟨g, hg⟩ := hn
    exact ZF.exists_compositionInjection hZF I hf hg
  have hull Y (hY : M.MemberSubset Y X) (hy : M.CardinalLessOrEqual I Y ω) :
      ∃ N, Fc_seed_d I ω H T K A Y N ∧ M.CardinalLessOrEqual I N ω := by
    obtain ⟨B, hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A Y
    have hb := ZF.countable_union_two_l I hZF hω ha hy hB
    obtain ⟨L, hL, hBL, hcL⟩ := fc_club_hull_l I hZFC hω hS hD hK hT hC₀
      (fun x hx => ((hB x).mp hx).elim (hA x) (fun hx => hX x (hY x hx))) hb
    obtain ⟨N, hn⟩ := ZF.fc_seed_exists_l I hZF hω hK hA (fun x hx => hX x (hY x hx))
    exact ⟨N, hn, count (hn.2.2.2.2 L (fun x hx => hBL x ((hB x).mpr (Or.inl hx)))
      (fun x hx => hBL x ((hB x).mpr (Or.inr hx))) hcL) (hC₀.members L hL).2⟩
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H).push T).push K).push A).push X
  let φ : UnarySchema 6 := { body := .existsE (fc_trace_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5)
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hφ Y : φ.denote ρ Y ↔ ∃ N, Fc_trace_d I ω H T K A X Y N := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, fc_trace_sat_l I hZF.1]
    rfl
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF φ ρ C₁
  have hC Y : M.mem Y C ↔ M.mem Y C₁ ∧ ∃ N, Fc_trace_d I ω H T K A X Y N :=
    (hC' Y).trans (and_congr_right fun _ => hφ Y)
  refine ⟨C, ⟨fun Y hY => hC₁.members Y ((hC Y).mp hY).1, ?_, ?_⟩, ?_⟩
  · intro Y hY hy
    obtain ⟨N, hn, hc⟩ := hull Y hY hy
    obtain ⟨Z, hZ⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) N X
    have hYZ x (hx : M.mem x Y) : M.mem x Z := (hZ x).mpr ⟨hn.2.1 x hx, hY x hx⟩
    have hn' : Fc_seed_d I ω H T K A Z N := ⟨hn.1, (fun x hx => ((hZ x).mp hx).1), hn.2.2.1, hn.2.2.2.1,
      fun B hAB hZB hB => hn.2.2.2.2 B hAB (fun x hx => hZB x (hYZ x hx)) hB⟩
    exact ⟨Z, (hC Z).mpr ⟨(e₁ Z).mpr ⟨fun x hx => ((hZ x).mp hx).2,
      count (fun x hx => ((hZ x).mp hx).1) hc⟩, N, hn', hc, hZ⟩, hYZ⟩
  · intro f Y hf hm hu
    have hf₁ := hf.mono_target_l I (fun B hB => ((hC B).mp hB).1)
    have hYC₁ := hC₁.closed f Y hf₁ hm hu
    -- 为每项取唯一最小闭包，得到真实函数图；不使用任意外部见证序列。
    let ψ : BinarySchema 7 := {
      body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
        (fc_trace_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
    have hψ i N : ψ.denote (ρ.push f) i N ↔ ∃ B, M.PairMember I i B f ∧ Fc_trace_d I ω H T K A X B N := by
      simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_orderedPairMem_iff I, fc_trace_sat_l I hZF.1]
      rfl
    obtain ⟨g, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ (ρ.push f) (source := ω) (target := C₀) (by
      intro i hi
      obtain ⟨B, hBC, hiB⟩ := hf.2.2 i hi
      obtain ⟨N, hn⟩ := ((hC B).mp hBC).2
      exact ⟨N, (hψ i N).mpr ⟨B, hiB, hn⟩⟩) (by
      intro i _ N L hn hl
      obtain ⟨B, hiB, hn⟩ := (hψ i N).mp hn
      obtain ⟨E, hiE, hl⟩ := (hψ i L).mp hl
      have he := hf.1.2 i B E hiB hiE
      subst E
      exact fc_seed_unique_l I hZF.1 hn.1 hl.1) (by
      intro i N _ hn
      obtain ⟨B, _, hn⟩ := (hψ i N).mp hn
      exact (e₀ N).mpr ⟨hn.1.2.2.1, hn.2.1⟩)
    have state i N (hi : M.PairMember I i N g) : ∃ B, M.PairMember I i B f ∧ Fc_trace_d I ω H T K A X B N :=
      (hψ i N).mp ((eg i N).mp hi).2
    have inc : Cc_increasing_d I g := by
      intro i j N L hij hi hj
      obtain ⟨B, hiB, hn⟩ := state i N hi
      obtain ⟨E, hjE, hl⟩ := state j L hj
      exact fc_seed_mono_l I hn.1 hl.1 (hm i j B E hij hiB hjE)
    obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I hg.1 hg.2.1
    obtain ⟨N, hN⟩ := KP.exists_union (ZF.modelsKP hZF) R
    have hn : Cc_union_d I g N := fun x => (hN x).trans
      ⟨fun ⟨B, hB, hx⟩ => (hR B).mp hB |>.elim fun i hi => ⟨i, B, hi, hx⟩,
        fun ⟨i, B, hi, hx⟩ => ⟨B, (hR B).mpr ⟨i, hi⟩, hx⟩⟩
    have hNC₀ := hC₀.closed g N hg inc hn
    have trace x : M.mem x Y ↔ M.mem x N ∧ M.mem x X := by
      constructor
      · intro hx
        obtain ⟨i, B, hiB, hxB⟩ := (hu x).mp hx
        obtain ⟨L, _, hiL⟩ := hg.2.2 i (hf.input_mem_of_pairMember hiB)
        obtain ⟨E, hiE, hl⟩ := state i L hiL
        have he := hf.1.2 i E B hiE hiB
        subst E
        obtain ⟨hxL, hxX⟩ := (hl.2.2 x).mp hxB
        exact ⟨(hn x).mpr ⟨i, L, hiL, hxL⟩, hxX⟩
      · rintro ⟨hx, hxX⟩
        obtain ⟨i, L, hiL, hxL⟩ := (hn x).mp hx
        obtain ⟨B, hiB, hl⟩ := state i L hiL
        exact (hu x).mpr ⟨i, B, hiB, (hl.2.2 x).mpr ⟨hxL, hxX⟩⟩
    have closed : Fc_closed_d I ω T K N := by
      rintro x ⟨n, s, t, p, hnω, hs, ht, hp, hx⟩
      obtain ⟨i, L, hiL, hsL⟩ := ZF.cc_fseq_bound_l I hZF hω hg inc hn hnω hs
      obtain ⟨B, _, hl⟩ := state i L hiL
      exact (hn x).mpr ⟨i, L, hiL, hl.1.2.2.2.1 x ⟨n, s, t, p, hnω, hsL, ht, hp, hx⟩⟩
    obtain ⟨o, _, hoω⟩ := hω.1.1
    obtain ⟨L, _, hoL⟩ := hg.2.2 o hoω
    obtain ⟨B, _, hL⟩ := state o L hoL
    have hseed : Fc_seed_d I ω H T K A Y N := ⟨
      (fun x hx => (hn x).mpr ⟨o, L, hoL, hL.1.1 x hx⟩),
      (fun x hx => ((trace x).mp hx).1), (hC₀.members N hNC₀).1, closed, fun B hAB hYB hB x hx => by
        obtain ⟨i, L, hiL, hxL⟩ := (hn x).mp hx
        obtain ⟨E, hiE, hL⟩ := state i L hiL
        exact hL.1.2.2.2.2 B hAB (fun z hz => hYB z ((hu z).mpr ⟨i, E, hiE, hz⟩)) hB x hxL⟩
    exact (hC Y).mpr ⟨hYC₁, N, hseed, (hC₀.members N hNC₀).2, trace⟩
  · intro Y
    refine (hC Y).trans ⟨And.right, fun ⟨N, hn⟩ => ?_⟩
    exact ⟨(e₁ Y).mpr ⟨fun x hx => ((hn.2.2 x).mp hx).2, count hn.1.2.1 hn.2.1⟩, N, hn⟩

end YesMetaZFC.SetTheory.ZFC
