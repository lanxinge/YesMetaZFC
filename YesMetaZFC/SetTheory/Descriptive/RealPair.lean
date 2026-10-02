import YesMetaZFC.SetTheory.Descriptive.RealPair.Sequence

/-! # Baire 空间的内部配对同胚

实际双射图配合等长度矩形基，识别 Baire×Baire 与 Baire。这里的前缀长度
仍遍历模型自身的 ω。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_type_l (hZF : M.Models ZF) {ω J D x y t} (hJ : Npair_d I ω J)
    (hx : M.IsSetFunctionFromTo I x D ω) (hy : M.IsSetFunctionFromTo I y D ω) (h : Rp_d I J x y t) :
    M.IsSetFunctionFromTo I t D ω := by
  obtain ⟨u, hu, hp⟩ := rp_exists_l I hZF hJ hx hy
  exact rp_unique_l I hZF.1 hp h ▸ hu

theorem rp_graph_l (hZF : M.Models ZF) {ω B J} (hB : Baire_d I ω B) (hJ : Npair_d I ω J) :
    ∃ P F, M.IsCartesianProduct I P B B ∧ M.IsSetBijectionFromTo I F P B ∧
      ∀ p t, M.PairMember I p t F ↔ ∃ x y, M.mem x B ∧ M.mem y B ∧ I.Codes p x y ∧ Rp_d I J x y t := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B B
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
      (rp_m (𝒞 := 𝒞) (.bound 4) (.bound 1) .newest (.bound 2)))) }
  have hp p t : φ.denote ρ p t ↔ ∃ x y, I.Codes p x y ∧ Rp_d I J x y t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, rp_sat_l I]; rfl
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := B)
    (by
      intro p hpP
      obtain ⟨x, hx, y, hy, hc⟩ := (hP p).mp hpP
      obtain ⟨t, _, ht⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy)
      exact ⟨t, (hp p t).mpr ⟨x, y, hc, ht⟩⟩)
    (by
      intro p _ t u ht hu
      obtain ⟨x, y, hc, ht⟩ := (hp p t).mp ht
      obtain ⟨x', y', hc', hu⟩ := (hp p u).mp hu
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact rp_unique_l I hZF.1 ht hu)
    (by
      intro p t hpP ht
      obtain ⟨x, hx, y, hy, hc⟩ := (hP p).mp hpP
      obtain ⟨x', y', hc', ht⟩ := (hp p t).mp ht
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact (hB.2 t).mpr (rp_type_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy) ht))
  have eqn p t : M.PairMember I p t F ↔ ∃ x y, M.mem x B ∧ M.mem y B ∧ I.Codes p x y ∧ Rp_d I J x y t := by
    rw [he, hp]
    constructor
    · rintro ⟨hpP, x, y, hc, ht⟩
      obtain ⟨x', hx, y', hy, hc'⟩ := (hP p).mp hpP
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact ⟨x, y, hx, hy, hc, ht⟩
    · rintro ⟨x, y, hx, hy, hc, ht⟩
      exact ⟨(hP p).mpr ⟨x, hx, y, hy, hc⟩, x, y, hc, ht⟩
  refine ⟨P, F, hP, ⟨⟨hF, ?_⟩, ?_⟩, eqn⟩
  · intro p q t ht hu
    obtain ⟨x, y, hx, hy, hc, ht⟩ := (eqn p t).mp ht
    obtain ⟨u, v, hu, hv, hd, hk⟩ := (eqn q t).mp hu
    obtain ⟨rfl, rfl⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy)
      ((hB.2 u).mp hu) ((hB.2 v).mp hv) ht hk
    exact I.unique hc hd
  · intro t ht
    obtain ⟨x, y, hx, hy, hr⟩ := rp_decode_l I hZF hJ ((hB.2 t).mp ht)
    obtain ⟨p, hp⟩ := I.total x y
    exact ⟨p, (hP p).mpr ⟨x, (hB.2 x).mpr hx, y, (hB.2 y).mpr hy, hp⟩,
      (eqn p t).mpr ⟨x, y, (hB.2 x).mpr hx, (hB.2 y).mpr hy, hp, hr⟩⟩

/-- 配对坐标下的开集判据恰为乘积的等长度矩形基判据。 -/
theorem rp_open_l (hZF : M.Models ZF) {ω B A J U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : Open_d A B U ↔ M.MemberSubset U B ∧
      ∀ x y z, M.mem x B → M.mem y B → Rp_d I J x y z → M.mem z U →
        ∃ n s t, M.mem n ω ∧ M.IsSetFunctionFromTo I s n ω ∧ M.IsSetFunctionFromTo I t n ω ∧
          M.MemberSubset s x ∧ M.MemberSubset t y ∧ ∀ u v w,
            M.mem u B → M.mem v B → Rp_d I J u v w → M.MemberSubset s u → M.MemberSubset t v → M.mem w U := by
  constructor
  · intro ho
    refine ⟨ho.1, fun x y z _ _ hr hz => ?_⟩
    obtain ⟨r, hrA, hrz, hru⟩ := ho.2 z hz
    obtain ⟨n, hn, hrf⟩ := (hA r).mp hrA
    obtain ⟨s, t, hs, ht, hst⟩ := rp_decode_l I hZF hJ hrf
    obtain ⟨hsx, hty⟩ := (rp_subset_l I hJ hs ht hst hr).mp hrz
    refine ⟨n, s, t, hn, hs, ht, hsx, hty, fun u v w hu hv hw hsu htv => ?_⟩
    exact hru w ((hB.2 w).mpr (rp_type_l I hZF hJ ((hB.2 u).mp hu) ((hB.2 v).mp hv) hw))
      ((rp_subset_l I hJ hs ht hst hw).mpr ⟨hsu, htv⟩)
  · rintro ⟨hUB, ho⟩
    refine ⟨hUB, fun z hz => ?_⟩
    obtain ⟨x, y, hx, hy, hr⟩ := rp_decode_l I hZF hJ ((hB.2 z).mp (hUB z hz))
    obtain ⟨n, s, t, hn, hs, ht, hsx, hty, hu⟩ := ho x y z ((hB.2 x).mpr hx) ((hB.2 y).mpr hy) hr hz
    obtain ⟨r, hrf, hst⟩ := rp_exists_l I hZF hJ hs ht
    refine ⟨r, (hA r).mpr ⟨n, hn, hrf⟩, (rp_subset_l I hJ hs ht hst hr).mpr ⟨hsx, hty⟩, fun w hw hrw => ?_⟩
    obtain ⟨u, v, huf, hvf, hp⟩ := rp_decode_l I hZF hJ ((hB.2 w).mp hw)
    obtain ⟨hsu, htv⟩ := (rp_subset_l I hJ hs ht hst hp).mp hrw
    exact hu u v w ((hB.2 u).mpr huf) ((hB.2 v).mpr hvf) hp hsu htv

end YesMetaZFC.SetTheory.Descriptive
