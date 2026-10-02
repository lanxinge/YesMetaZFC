import YesMetaZFC.SetTheory.Descriptive.Compact

/-! # Baire 空间的具体非紧致开覆盖

按第零坐标的值分割为空间的开切片。任意有限子覆盖都会把 ω 单射进其有限索引集，
与内部自然数的无限性矛盾。覆盖族和这张单射都在模型内构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Slice_d (B z a U : M.Domain) : Prop := ∀ f, M.mem f U ↔ M.mem f B ∧ M.PairMember I z a f
def slice_m {d} (B z a U : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest U.weaken) (.conj (.mem .newest B.weaken)
    (Formula.orderedPairMem 𝒞 z.weaken a.weaken .newest)))
derive_free_closed slice_m
theorem slice_sat_l {d} (ρ : Env M d) (B z a U : Term d) :
    Formula.satisfies ρ (slice_m (𝒞 := 𝒞) B z a U) ↔
      Slice_d I (B.eval ρ) (z.eval ρ) (a.eval ρ) (U.eval ρ) := by
  simp only [slice_m, Slice_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

theorem ds_slice_open_l (hZF : M.Models ZF) {ω X B S z a U}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hz : M.mem z ω) (hU : Slice_d I B z a U) : Open_d S B U := by
  refine ⟨fun f hf => ((hU f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hfB, hfa⟩ := (hU f).mp hf
  obtain ⟨n, hn, hnω⟩ := hω.1.2 z hz
  obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hfB) hnω
  refine ⟨s, (hS s).mpr ⟨n, hnω, hs⟩, (ds_restrict_iff_l I hs ((hB f).mp hfB).1).mp hr,
    fun g hg hsg => (hU g).mpr ⟨hg, ?_⟩⟩
  have hsa := (hr.2 z a).mpr ⟨hn.predecessor_mem, hfa⟩
  exact hsa.elim fun p hp => ⟨p, hp.1, hsg p hp.2⟩

/-- 返回没有内部有限子覆盖的实际开覆盖族。 -/
theorem baire_noncompact_cover_l (hZF : M.Models ZF) {ω B S τ}
    (hB : Baire_d I ω B) (hS : Fseq_space_d I ω ω S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : ∃ A, M.MemberSubset A τ ∧ Cover_d B A ∧
      ∀ K, Finite_d I ω K → M.MemberSubset K A → ¬ Cover_d B K := by
  obtain ⟨z, _, hz⟩ := hB.1.1.1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push z
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 3)
      (slice_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest (.bound 1)) }
  have hp U : φ.denote ρ U ↔ ∃ a, M.mem a ω ∧ Slice_d I B z a U := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, slice_sat_l I]; rfl
  obtain ⟨A, hA'⟩ := ZF.separation_exists_d hZF φ ρ P
  have hA U : M.mem U A ↔ ∃ a, M.mem a ω ∧ Slice_d I B z a U :=
    ((hA' U).trans (and_congr_right fun _ => hp U)).trans
      ⟨And.right, fun h => ⟨(hP U).mpr (fun f hf => h.elim fun a ha => ((ha.2 f).mp hf).1), h⟩⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨a, _, ha⟩ := (hA U).mp hU
    exact (hτ U).mpr (ds_slice_open_l I hZF hB.1 hB.2 hS hz ha)
  · intro f hf
    obtain ⟨a, ha, hfa⟩ := ((hB.2 f).mp hf).2.2 z hz
    let ψ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) .newest }
    obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF ψ
      ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push a) B
    have hU : Slice_d I B z a U := fun g => (hU' g).trans (and_congr_right fun _ =>
      Formula.satisfies_orderedPairMem_iff I _ _ _ _)
    exact ⟨U, (hA U).mpr ⟨a, ha, hU⟩, (hU f).mpr ⟨hf, hfa⟩⟩
  · intro K ⟨n, hn, E, hE⟩ hKA hcover
    let δ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push z).push K
    let ψ : BinarySchema 3 := {
      body := .conj (.mem .newest (.bound 2))
        (slice_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
    have hψ a U : ψ.denote δ a U ↔ M.mem U K ∧ Slice_d I B z a U := by
      simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, slice_sat_l I]; rfl
    obtain ⟨F, hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I ψ δ (source := ω) (target := K)
      (by
        intro a ha
        obtain ⟨f, hf, he⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
        obtain ⟨U, hUK, hfU⟩ := hcover f ((hB.2 f).mpr hf)
        obtain ⟨b, _, hb⟩ := (hA U).mp (hKA U hUK)
        have e := ((he z b).mp ((hb f).mp hfU).2).2
        exact ⟨U, (hψ a U).mpr ⟨hUK, e ▸ hb⟩⟩)
      (fun a _ U V hU hV => hZF.1.eq_of_same_members U V
        (fun f => (((hψ a U).mp hU).2 f).trans (((hψ a V).mp hV).2 f).symm))
      (fun a U _ hU => ((hψ a U).mp hU).1)
      (by
        intro a b U ha _ hau hbu
        obtain ⟨f, hf, he⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
        have hfU := (((hψ a U).mp hau).2 f).mpr ⟨(hB.2 f).mpr hf, (he z a).mpr ⟨hz, rfl⟩⟩
        exact (((he z b).mp ((((hψ b U).mp hbu).2 f).mp hfU).2).2).symm)
    exact ZF.omega_not_le_finite_l I hZF hB.1 n hn (ZF.exists_compositionInjection hZF I hF hE)

theorem baire_not_compact_l (hZF : M.Models ZF) {ω B S τ}
    (hB : Baire_d I ω B) (hS : Fseq_space_d I ω ω S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : ¬ Compact_d I ω B τ := by
  obtain ⟨A, hA, hc, hn⟩ := baire_noncompact_cover_l I hZF hB hS hτ
  intro h
  obtain ⟨K, hk, hKA, hcover⟩ := h A hA hc
  exact hn K hk hKA hcover

end YesMetaZFC.SetTheory.Descriptive
