import YesMetaZFC.SetTheory.FinitaryHullSyntax

/-! # 内部可数运算族的统一有限元闭包

用 (运算图,原规则编号) 作为新规则编号。新运算图按实际函数族取值，因此
对新图闭合恰好等于对全部原图闭合；构造及规则域可数性都只需 ZF。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem fc_family_l (hZF : M.Models ZF) {ω H S T D O} (hω : M.IsOmega ω)
    (hD : M.IsCartesianProduct I D T S) (hT : M.CardinalLessOrEqual I T ω)
    (hO : M.CardinalLessOrEqual I O ω) (ho : ∀ K, M.mem K O → M.IsSetFunctionFromTo I K D H) :
    ∃ W E L, M.IsCartesianProduct I W O T ∧ M.IsCartesianProduct I E W S ∧
      M.IsSetFunctionFromTo I L E H ∧ M.CardinalLessOrEqual I W ω ∧
      ∀ N, Fc_closed_d I ω W L N ↔ ∀ K, M.mem K O → Fc_closed_d I ω T K N := by
  obtain ⟨W, hW⟩ := exists_cartesianProduct hZF I O T
  obtain ⟨E, hE⟩ := exists_cartesianProduct hZF I W S
  have hCount := countable_product_l I hZF hω hO hT hW
  let ρ : Env M 1 := ⟨fun _ => O, fun _ => O⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.existsE (.existsE (.existsE (.existsE
      (.conj (𝒞.code (.bound 6) (.bound 4) (.bound 3))
        (.conj (𝒞.code (.bound 4) (.bound 2) (.bound 1))
          (.conj (𝒞.code .newest (.bound 1) (.bound 3))
            (Formula.orderedPairMem 𝒞 .newest (.bound 5) (.bound 2))))))))) }
  have hφ x y : φ.denote ρ x y ↔ ∃ l s K t p,
      I.Codes x l s ∧ I.Codes l K t ∧ I.Codes p t s ∧ M.PairMember I p y K := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨L, hL, hl⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := E) (target := H) (by
    intro x hx
    obtain ⟨l, hlW, s, hs, hxl⟩ := (hE x).mp hx
    obtain ⟨K, hKO, t, ht, hli⟩ := (hW l).mp hlW
    obtain ⟨p, hp⟩ := I.total t s
    obtain ⟨y, _, hpy⟩ := (ho K hKO).2.2 p ((hD p).mpr ⟨t, ht, s, hs, hp⟩)
    exact ⟨y, (hφ x y).mpr ⟨l, s, K, t, p, hxl, hli, hp, hpy⟩⟩) (by
    intro x hx y z hy hz
    obtain ⟨l, s, K, t, p, hxl, hli, hp, hpy⟩ := (hφ x y).mp hy
    obtain ⟨l', s', K', t', p', hxl', hli', hp', hpz⟩ := (hφ x z).mp hz
    obtain ⟨rfl, rfl⟩ := I.injective hxl hxl'
    obtain ⟨rfl, rfl⟩ := I.injective hli hli'
    have hep := I.unique hp hp'
    subst p'
    obtain ⟨l', hl', s', _, hx'⟩ := (hE x).mp hx
    obtain ⟨rfl, rfl⟩ := I.injective hxl hx'
    obtain ⟨K', hK', t', _, hl''⟩ := (hW l).mp hl'
    obtain ⟨rfl, rfl⟩ := I.injective hli hl''
    exact (ho K hK').1.2 p y z hpy hpz) (by
    intro x y hx hy
    obtain ⟨l, s, K, t, p, hxl, hli, _, hp⟩ := (hφ x y).mp hy
    obtain ⟨l', hl', s', _, hx'⟩ := (hE x).mp hx
    obtain ⟨rfl, rfl⟩ := I.injective hxl hx'
    obtain ⟨K', hK', t', _, hl''⟩ := (hW l).mp hl'
    obtain ⟨rfl, rfl⟩ := I.injective hli hl''
    exact (ho K hK').output_mem_of_pairMember hp)
  refine ⟨W, E, L, hW, hE, hL, hCount, fun N => ⟨?_, ?_⟩⟩
  · intro hc K hKO x hx
    obtain ⟨n, s, t, p, hn, hsN, ht, hp, hpx⟩ := hx
    obtain ⟨t', _, s', hs, hp'⟩ := (hD p).mp ((ho K hKO).input_mem_of_pairMember hpx)
    obtain ⟨rfl, rfl⟩ := I.injective hp hp'
    obtain ⟨l, hlit⟩ := I.total K t
    obtain ⟨v, hvl⟩ := I.total l s
    have hlW := (hW l).mpr ⟨K, hKO, t, ht, hlit⟩
    have hvx := (hl v x).mpr ⟨(hE v).mpr ⟨l, hlW, s, hs, hvl⟩,
      (hφ v x).mpr ⟨l, s, K, t, p, hvl, hlit, hp, hpx⟩⟩
    exact hc x ⟨n, s, l, v, hn, hsN, hlW, hvl, hvx⟩
  · intro hc x hx
    obtain ⟨n, s, l, v, hn, hsN, hlW, hvl, hvx⟩ := hx
    obtain ⟨K, hKO, t, ht, hlit⟩ := (hW l).mp hlW
    obtain ⟨l', s', K', t', p, hvl', hlit', hp, hpx⟩ := (hφ v x).mp ((hl v x).mp hvx).2
    obtain ⟨rfl, rfl⟩ := I.injective hvl hvl'
    obtain ⟨rfl, rfl⟩ := I.injective hlit hlit'
    exact hc K hKO x ⟨n, s, t, p, hn, hsN, ht, hp, hpx⟩

end YesMetaZFC.SetTheory.ZF
