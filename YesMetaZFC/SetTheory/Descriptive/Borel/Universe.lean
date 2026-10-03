import YesMetaZFC.SetTheory.Descriptive.Borel.Canonical
import YesMetaZFC.SetTheory.Collapse.RelationEvaluationExistence

/-! # 全部内部 Borel 码组成集合

地址、边、补标记、叶标记各有固定幂集界。这给代码上的良基递归提供实际值域。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_universe_l (hZF : M.Models ZF) (ω A S : M.Domain) :
    ∃ C, ∀ c, M.mem c C ↔ Bcode_d I ω A S c := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF (kp_pair_l (ZF.modelsKP hZF)) A A
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF D
  obtain ⟨V, hV⟩ := ZF.exists_cartesianProduct hZF I A S
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF V
  obtain ⟨U, hU⟩ := ZF.exists_cartesianProduct hZF I P W
  obtain ⟨L, hL⟩ := ZF.exists_cartesianProduct hZF I Q U
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I P L
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S
  let φ : UnarySchema 3 := { body := bcode_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ K
  refine ⟨C, fun c => ((hC c).trans (and_congr_right fun _ => bcode_sat_l I hZF.1 _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨T, R, N, F, ⟨p, q, hc, hp, hq⟩, ht⟩ := h
  have hR : M.mem R Q := (hQ R).mpr (fun r hr => by
    obtain ⟨b, a, hb⟩ := ht.edges.1 r hr
    have ha := (ht.edges.2 a b).mp ⟨r, hb, hr⟩
    exact (hD r).mpr ⟨b, ht.tree.1 b ha.2.1, a, ht.tree.1 a ha.1, hb⟩)
  have hN : M.mem N P := (hP N).mpr (fun a ha => ht.tree.1 a (ht.neg_sub a ha))
  have hF : M.mem F W := (hW F).mpr (fun r hr => by
    obtain ⟨a, s, ha⟩ := ht.leaf_fn.1 r hr
    have hh := ht.leaf a s ⟨r, ha, hr⟩
    exact (hV r).mpr ⟨a, ht.tree.1 a hh.1, s, hh.2.1, ha⟩)
  exact (hK c).mpr ⟨T, (hP T).mpr ht.tree.1, p,
    (hL p).mpr ⟨R, hR, q, (hU q).mpr ⟨N, hN, F, hF, hq⟩, hp⟩, hc⟩

/-- 原公式给出的单值部分码族自动集合化；允许空指标域。 -/
theorem bf_defined_l (hZF : M.Models ZF) {ω A S} {n} (φ : BinarySchema n) (ρ : Env M n)
    (unique : ∀ i c d, φ.denote ρ i c → φ.denote ρ i d → c = d)
    (bound : ∀ i c, φ.denote ρ i c → M.mem i ω ∧ Bcode_d I ω A S c) :
    ∃ H, Bfam_d I ω A S H ∧ ∀ i c, M.PairMember I i c H ↔ φ.denote ρ i c := by
  obtain ⟨C, hC⟩ := bcode_universe_l I hZF ω A S
  obtain ⟨V, hV⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω C
  obtain ⟨H, hh, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ V
  have pair i c : M.PairMember I i c H ↔ φ.denote ρ i c := (he i c).trans
    ⟨fun h => h.2.2, fun h => ⟨(hV i).mpr (Or.inl (bound i c h).1),
      (hV c).mpr (Or.inr ((hC c).mpr (bound i c h).2)), h⟩⟩
  exact ⟨H, ⟨⟨hh.1, fun i c d hc hd => unique i c d ((pair i c).mp hc) ((pair i d).mp hd)⟩,
    fun i c hc => bound i c ((pair i c).mp hc)⟩, pair⟩

end YesMetaZFC.SetTheory.Descriptive
