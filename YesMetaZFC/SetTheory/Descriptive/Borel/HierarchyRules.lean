import YesMetaZFC.SetTheory.Descriptive.Borel.Hierarchy

/-! # Borel 层级的基层、补集、升层与可数并规则 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bsig_nonempty_l {ω A B α K} (h : Bsig_d I ω A B α K) : ∃ β, M.mem β α := by
  obtain ⟨S, ⟨F, hf, hs⟩, hk⟩ := h
  obtain ⟨β, V, hv⟩ := ((hs K).mp hk).2.1
  exact ⟨β, (hf.1.2.2 β).mpr ⟨V, hv⟩⟩
theorem bpi_subset_l {ω A B α K} (h : Bpi_d I ω A B α K) : M.MemberSubset K B :=
  h.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
theorem bsig_open_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (ho : Open_d A B K) : Bsig_d I ω A B α K :=
  (bsig_unfold_l I hZF hα).mpr ⟨ho.1, hne, Or.inl ho⟩
theorem bpi_closed_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (hc : Cl_d A B K) : Bpi_d I ω A B α K := by
  obtain ⟨sub, L, hl, ho⟩ := hc
  exact ⟨L, bsig_open_l I hZF hα hne ho, cm_symm_l sub hl⟩

theorem bsig_compl_l (hE : Extensional M) {ω A B α K L}
    (sub : M.MemberSubset K B) (hc : Cm_d B K L) : Bsig_d I ω A B α L ↔ Bpi_d I ω A B α K :=
  ⟨fun h => ⟨L, h, cm_symm_l sub hc⟩, fun ⟨_, hv, hk⟩ =>
    cm_unique_l hE (cm_symm_l (bsig_subset_l I hv) hk) hc ▸ hv⟩
theorem bpi_compl_l (hE : Extensional M) {ω A B α K L}
    (sub : M.MemberSubset K B) (hc : Cm_d B K L) : Bpi_d I ω A B α L ↔ Bsig_d I ω A B α K := by
  exact (bsig_compl_l I hE (fun x hx => ((hc x).mp hx).1) (cm_symm_l sub hc)).symm

theorem bsig_mono_l (hZF : M.Models ZF) {ω A B α β K} (hβ : M.IsOrdinal β)
    (hab : M.MemberSubset α β) (h : Bsig_d I ω A B α K) : Bsig_d I ω A B β K := by
  obtain ⟨sub, ⟨γ, hγ⟩, ho | ⟨H, hu, hh⟩⟩ := (bsig_unfold_l I hZF (bsig_ordinal_l I h)).mp h
  · exact bsig_open_l I hZF hβ ⟨γ, hab γ hγ⟩ ho
  · exact (bsig_unfold_l I hZF hβ).mpr ⟨sub, ⟨γ, hab γ hγ⟩, Or.inr ⟨H, hu,
      fun i C hc => (hh i C hc).elim fun δ hd => ⟨δ, hab δ hd.1, hd.2⟩⟩⟩
theorem bpi_mono_l (hZF : M.Models ZF) {ω A B α β K} (hβ : M.IsOrdinal β)
    (hab : M.MemberSubset α β) (h : Bpi_d I ω A B α K) : Bpi_d I ω A B β K :=
  h.elim fun L h => ⟨L, bsig_mono_l I hZF hβ hab h.1, h.2⟩

theorem bsig_union_l (hZF : M.Models ZF) {ω A B α H K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (hu : Bu_d I ω H K)
    (hh : ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω A B β C) : Bsig_d I ω A B α K := by
  refine (bsig_unfold_l I hZF hα).mpr ⟨?_, hne, Or.inr ⟨H, hu, hh⟩⟩
  intro x hx
  obtain ⟨i, C, hc, hx⟩ := (hu.2.2 x).mp hx
  obtain ⟨_, _, h⟩ := hh i C hc
  exact bpi_subset_l I h x hx

/-- 单元素族给出严格升层 Π⁰α ⊆ Σ⁰β；这里只需 ω 非空。 -/
theorem bpi_bsig_l (hZF : M.Models ZF) {ω A B α β K} (hne : ∃ i, M.mem i ω)
    (hβ : M.IsOrdinal β) (hab : M.mem α β) (h : Bpi_d I ω A B α K) : Bsig_d I ω A B β K := by
  obtain ⟨D, hd⟩ := KP.exists_singleton (ZF.modelsKP hZF) K
  obtain ⟨H, hh, eh⟩ := ZF.exists_constantFunction hZF I (source := ω) ((hd K).mpr rfl)
  have hu : Bu_d I ω H K := by
    refine ⟨hh.1, fun i C hc => ((eh i C).mp hc).1, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, K, (eh i K).mpr ⟨hi, rfl⟩, hx⟩
    · rintro ⟨i, C, hc, hx⟩
      exact ((eh i C).mp hc).2 ▸ hx
  exact bsig_union_l I hZF hβ ⟨α, hab⟩ hu (fun i C hc => ⟨α, hab, ((eh i C).mp hc).2 ▸ h⟩)
theorem bsig_bpi_l (hZF : M.Models ZF) {ω A B α β K} (hne : ∃ i, M.mem i ω)
    (hβ : M.IsOrdinal β) (hab : M.mem α β) (h : Bsig_d I ω A B α K) : Bpi_d I ω A B β K := by
  obtain ⟨L, hl⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  exact ⟨L, bpi_bsig_l I hZF hne hβ hab ⟨K, h, hl⟩, cm_symm_l (bsig_subset_l I h) hl⟩

/-- 第一层恰好是开集；较低层只有零层，不能贡献任何非空索引。 -/
theorem bsig_one_l (hZF : M.Models ZF) {ω A B o K} (ho : M.IsOrdinalOne o) :
    Bsig_d I ω A B o K ↔ Open_d A B K := by
  obtain ⟨z, hz, hs⟩ := ho
  have hα := KP.successor_isOrdinal (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members hz) hs
  constructor
  · intro h
    obtain ⟨sub, _, hopen | ⟨H, hu, hh⟩⟩ := (bsig_unfold_l I hZF hα).mp h
    · exact hopen
    · have empty : ∀ x, ¬ M.mem x K := by
        intro x hx
        obtain ⟨i, C, hc, _⟩ := (hu.2.2 x).mp hx
        obtain ⟨β, hb, L, hl, _⟩ := hh i C hc
        rcases (hs β).mp hb with hb | hb
        · exact hz β hb
        · obtain ⟨γ, hγ⟩ := bsig_nonempty_l I hl
          exact hz γ (hZF.1.eq_of_same_members β z hb ▸ hγ)
      exact ds_open_empty_l empty
  · exact bsig_open_l I hZF hα ⟨z, hs.predecessor_mem⟩
theorem bpi_one_l (hZF : M.Models ZF) {ω A B o K} (ho : M.IsOrdinalOne o) :
    Bpi_d I ω A B o K ↔ Cl_d A B K := by
  constructor
  · rintro ⟨L, hl, hc⟩
    exact ⟨fun x hx => ((hc x).mp hx).1, L, cm_symm_l (bsig_subset_l I hl) hc, (bsig_one_l I hZF ho).mp hl⟩
  · rintro ⟨sub, L, hc, hl⟩
    exact ⟨L, (bsig_one_l I hZF ho).mpr hl, cm_symm_l sub hc⟩

end YesMetaZFC.SetTheory.Descriptive
