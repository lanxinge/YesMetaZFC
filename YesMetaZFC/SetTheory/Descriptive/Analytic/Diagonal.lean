import YesMetaZFC.SetTheory.Descriptive.Analytic.Code
import YesMetaZFC.SetTheory.Descriptive.Borel.Relabel
import YesMetaZFC.SetTheory.Descriptive.Borel.Finite

/-! # Borel 集的解析表示

对角配对给出闭嵌入。先映射原 Borel 码的叶标签，再与闭对角集相交，得到
对角像的实际 Borel 码；其投影恰为原集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Dg_d (B J D : M.Domain) : Prop := ∀ t, M.mem t D ↔ M.mem t B ∧ ∃ x, M.mem x B ∧ Rp_d I J x x t
def dg_m {d} (B J D : Term d) : Formula 1 d := .forallE (.iff (.mem .newest D.weaken)
  (.conj (.mem .newest B.weaken) (Formula.existsMem B.weaken
    (rp_m (𝒞 := 𝒞) J.weaken.weaken .newest .newest (.bound 1)))))
derive_free_closed dg_m
theorem dg_sat_l {d} (ρ : Env M d) (B J D : Term d) :
    Formula.satisfies ρ (dg_m (𝒞 := 𝒞) B J D) ↔ Dg_d I (B.eval ρ) (J.eval ρ) (D.eval ρ) := by
  simp only [dg_m, Dg_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem dg_closed_l (hZF : M.Models ZF) {ω B A J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) :
    ∃ D U, Dg_d I B J D ∧ Cm_d B D U ∧ Open_d A B U := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rp_m (𝒞 := 𝒞) (.bound 2) .newest .newest (.bound 1)) }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hD : Dg_d I B J D := by
    intro t
    simpa only [φ, Formula.satisfies_existsMem_iff, rp_sat_l I] using! hD' t
  obtain ⟨U, hU⟩ := cm_exists_l (ZF.modelsKP hZF) B D
  refine ⟨D, U, hD, hU, ⟨fun t ht => ((hU t).mp ht).1, fun t ht => ?_⟩⟩
  obtain ⟨htB, htD⟩ := (hU t).mp ht
  obtain ⟨x, y, hx, hy, hp⟩ := rp_decode_l I hZF hJ ((hB.2 t).mp htB)
  have hxy : x ≠ y := by
    intro e
    subst y
    exact htD ((hD t).mpr ⟨htB, x, (hB.2 x).mpr hx, hp⟩)
  obtain ⟨i, a, b, hi, hia, hib, hab⟩ := ds_differ_l I hZF.1 hx hy hxy
  obtain ⟨v, _, hv⟩ := np_total_l I hJ (hx.output_mem_of_pairMember hia) (hy.output_mem_of_pairMember hib)
  have hiv := (hp.2 i v).mpr ⟨a, b, hia, hib, hv⟩
  obtain ⟨n, hn, hnω⟩ := hB.1.1.2 i hi
  obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hB.1 ((hB.2 t).mp htB) hnω
  refine ⟨s, (hA s).mpr ⟨n, hnω, hs⟩, (ds_restrict_iff_l I hs ((hB.2 t).mp htB).1).mp hr, fun u hu hsu => ?_⟩
  apply (hU u).mpr
  refine ⟨hu, fun huD => ?_⟩
  obtain ⟨_, w, hw, hwu⟩ := (hD u).mp huD
  obtain ⟨p, hpc, hps⟩ := (hr.2 i v).mpr ⟨hn.predecessor_mem, hiv⟩
  obtain ⟨c, d, hic, hid, hcd⟩ := (hwu.2 i v).mp ⟨p, hpc, hsu p hps⟩
  obtain ⟨ha, hb⟩ := np_injective_l I hJ hv hcd
  exact hab (ha.trans ((((hB.2 w).mp hw).1.2 i c d hic hid).trans hb.symm))

theorem dg_prefix_graph_l (hZF : M.Models ZF) {ω A J}
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ H, M.IsSetFunctionFromTo I H A A ∧
      ∀ s t, M.PairMember I s t H ↔ M.mem s A ∧ Rp_d I J s s t := by
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := { body := rp_m (𝒞 := 𝒞) (.bound 2) (.bound 1) (.bound 1) .newest }
  have hp s t : φ.denote ρ s t ↔ Rp_d I J s s t := rp_sat_l I _ _ _ _ _
  obtain ⟨H, hH, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := A)
    (by
      intro s hs
      obtain ⟨_, _, hs⟩ := (hA s).mp hs
      obtain ⟨t, _, ht⟩ := rp_exists_l I hZF hJ hs hs
      exact ⟨t, (hp s t).mpr ht⟩)
    (fun s _ t u ht hu => rp_unique_l I hZF.1 ((hp s t).mp ht) ((hp s u).mp hu))
    (by
      intro s t hs ht
      obtain ⟨n, hn, hs⟩ := (hA s).mp hs
      exact (hA t).mpr ⟨n, hn, rp_type_l I hZF hJ hs hs ((hp s t).mp ht)⟩)
  exact ⟨H, hH, fun s t => (he s t).trans (and_congr_right fun _ => hp s t)⟩

theorem dg_borel_l (hZF : M.Models ZF) {ω B A J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hK : Borel_d I ω A A B K) : ∃ R, Borel_d I ω A A B R ∧
      ∀ z, M.mem z R ↔ ∃ x, M.mem x K ∧ Rp_d I J x x z := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨H, hH, map⟩ := dg_prefix_graph_l I hZF hA hJ
  obtain ⟨d, hd, val⟩ := bcode_relabel_l I hZF hH hc
  have value {x z} (h : Rp_d I J x x z) : Bsat_d I ω A A d z ↔ Bsat_d I ω A A c x := by
    apply val x z
    intro s t hs ht
    obtain ⟨_, _, hs⟩ := (hA s).mp hs
    exact (rp_subset_l I hJ hs hs ((map s t).mp ht).2 h).trans ⟨And.left, fun h => ⟨h, h⟩⟩
  obtain ⟨D, U, hD, hU, ho⟩ := dg_closed_l I hZF hB hA hJ
  obtain ⟨T, _, _, ht⟩ := tree_of_closed_l (ZF.modelsKP hZF) (fun x hx => ((hD x).mp hx).1) hU ho
  obtain ⟨q, hq, eqn⟩ := tree_body_borel_l I hZF hB.1 hA ha ht
  obtain ⟨e, he, ev⟩ := bcode_inter_l I hZF hB.1 hA hd hq
  obtain ⟨R, hR, _⟩ := bden_exists_unique_l I hZF ω A A B e
  refine ⟨R, ⟨e, he, hR⟩, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    obtain ⟨hzB, hz⟩ := (hR z).mp hz
    obtain ⟨hdz, hqz⟩ := (ev z).mp hz
    obtain ⟨_, x, hxB, hp⟩ := (hD z).mp ((eqn z).mpr ⟨hzB, hqz⟩)
    exact ⟨x, (hK x).mpr ⟨hxB, (value hp).mp hdz⟩, hp⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨hxB, hcx⟩ := (hK x).mp hx
    have hxF := (hB.2 x).mp hxB
    have hzB := (hB.2 z).mpr (rp_type_l I hZF hJ hxF hxF hp)
    have hzD := (hD z).mpr ⟨hzB, x, hxB, hp⟩
    exact (hR z).mpr ⟨hzB, (ev z).mpr ⟨(value hp).mpr hcx, ((eqn z).mp hzD).2⟩⟩

/-- 每个 Borel 集及其相对补都解析，故 Borel ⊆ Δ¹₁ 的关键包含实际成立。 -/
theorem borel_an_l (hZF : M.Models ZF) {ω B A J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hK : Borel_d I ω A A B K) : An_d I ω A B J K := by
  have hKB : M.MemberSubset K B := hK.elim fun c h => fun x hx => ((h.2 x).mp hx).1
  obtain ⟨R, hr, image⟩ := dg_borel_l I hZF hB hA ha hJ hK
  apply (an_proj_l I).mpr
  refine ⟨R, hr, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hxf := (hB.2 x).mp (hKB x hx)
    obtain ⟨z, hz, hp⟩ := rp_exists_l I hZF hJ hxf hxf
    exact ⟨hKB x hx, x, z, hKB x hx, (hB.2 z).mpr hz, hp, (image z).mpr ⟨x, hx, hp⟩⟩
  · rintro ⟨hxB, y, z, hyB, _, hp, hzR⟩
    obtain ⟨u, hu, hdiag⟩ := (image z).mp hzR
    have huf := (hB.2 u).mp (hKB u hu)
    have eqn := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hyB) huf huf hp hdiag
    exact eqn.1.symm ▸ hu

end YesMetaZFC.SetTheory.Descriptive
