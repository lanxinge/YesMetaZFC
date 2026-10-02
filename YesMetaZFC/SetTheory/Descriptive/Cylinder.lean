import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 内部柱集及其基性质

柱集 [s] 是空间中包含有限函数图 s 的全部点。成员判据只用图包含，柱集本身
由 KP 的有界分离构造。空间与节点的有效性在各条基定理中显式给出。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cyl_d (B s U : M.Domain) : Prop := ∀ f, M.mem f U ↔ M.mem f B ∧ M.MemberSubset s f

def cyl_m {d} (B s U : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest U.weaken) (.conj (.mem .newest B.weaken) (Formula.subset s.weaken .newest)))
derive_free_closed cyl_m

@[prove_auto_norm semantic]
theorem cyl_sat_l {d} (ρ : Env M d) (B s U : Term d) :
    Formula.satisfies ρ (cyl_m B s U) ↔ Cyl_d (M := M) (B.eval ρ) (s.eval ρ) (U.eval ρ) := by
  simp only [cyl_m, Cyl_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

theorem cyl_exists_l (hKP : M.Models KP) (B s : M.Domain) : ∃ U, Cyl_d B s U := by
  let φ : Delta0UnarySchema 1 := { body := Formula.subset (.bound 1) .newest, delta0 := .atom _ _ _ }
  obtain ⟨U, hU⟩ := KP.separation_exists_d hKP φ ⟨fun _ => s, fun _ => s⟩ B
  exact ⟨U, fun f => (hU f).trans (and_congr_right fun _ =>
    Formula.satisfies_subset_iff _ _ _)⟩

theorem cyl_unique_l (hE : Extensional M) {B s U V : M.Domain}
    (hU : Cyl_d B s U) (hV : Cyl_d B s V) : U = V :=
  hE.eq_of_same_members U V (fun f => (hU f).trans (hV f).symm)

theorem cyl_subset_l {B s U : M.Domain} (hU : Cyl_d B s U) : M.MemberSubset U B :=
  fun f hf => ((hU f).mp hf).1

/-- 前缀越长，柱集越小。 -/
theorem cyl_antitone_l {B s t U V : M.Domain} (hU : Cyl_d B s U) (hV : Cyl_d B t V)
    (hst : M.MemberSubset s t) : M.MemberSubset V U :=
  fun f hf => (hU f).mpr ⟨((hV f).mp hf).1, fun p hp => ((hV f).mp hf).2 p (hst p hp)⟩

/-- 同一点的两个序数长度前缀按包含可比较。 -/
theorem ds_prefix_compare_l (hE : Extensional M) {ω X s t f n m}
    (hω : M.IsOrdinal ω) (hn : M.mem n ω) (hm : M.mem m ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ht : M.IsSetFunctionFromTo I t m X)
    (hf : M.IsSetFunction I f) (hsf : M.MemberSubset s f) (htf : M.MemberSubset t f) :
    M.MemberSubset s t ∨ M.MemberSubset t s := by
  have hr := (ds_restrict_iff_l I hs hf).mpr hsf
  have hk := (ds_restrict_iff_l I ht hf).mpr htf
  rcases hω.wellOrder.linear.compare n hn m hm with he | hnm | hmn
  · have e := hE.eq_of_same_members n m he
    subst m
    have e := hr.eq hE hk
    exact Or.inl (fun p hp => e ▸ hp)
  · exact Or.inl (ds_prefix_mono_l I hs ht.1 hr hk ((hω.mem hm).transitive n hnm))
  · exact Or.inr (ds_prefix_mono_l I ht hs.1 hk hr ((hω.mem hn).transitive m hmn))

/-- 非空字母表上的每个合法柱集非空。 -/
theorem cyl_nonempty_l (hZF : M.Models ZF) {ω X B s n U}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n X) (hU : Cyl_d B s U) (hX : ∃ a, M.mem a X) :
    ∃ f, M.mem f U := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨f, hf, hr, _⟩ := ds_extend_l I hZF hω hn hs ha
  exact ⟨f, (hU f).mpr ⟨(hB f).mpr hf, (ds_restrict_iff_l I hs hf.1).mp hr⟩⟩

/-- 两个合法柱集或者不交，或者其中一个包含另一个。 -/
theorem cyl_nested_l (hE : Extensional M) {ω X B s t n m U V}
    (hω : M.IsOrdinal ω) (hB : M.IsFunctionSpace I B ω X)
    (hn : M.mem n ω) (hm : M.mem m ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ht : M.IsSetFunctionFromTo I t m X)
    (hU : Cyl_d B s U) (hV : Cyl_d B t V) :
    M.IsDisjoint U V ∨ M.MemberSubset U V ∨ M.MemberSubset V U := by
  classical
  by_cases h : ∃ f, M.mem f U ∧ M.mem f V
  · obtain ⟨f, hf, hg⟩ := h
    have a := (hU f).mp hf
    have b := (hV f).mp hg
    exact Or.inr ((ds_prefix_compare_l I hE hω hn hm hs ht ((hB f).mp a.1).1 a.2 b.2).elim
      (fun h => Or.inr (cyl_antitone_l hU hV h)) (fun h => Or.inl (cyl_antitone_l hV hU h)))
  · exact Or.inl (fun f hf => h ⟨f, hf⟩)

/-- 不同点有不交的基本邻域，见证前缀的长度也属于内部 ω。 -/
theorem ds_separate_l (hZF : M.Models ZF) {ω X B S f g}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hf : M.mem f B) (hg : M.mem g B) (hne : f ≠ g) :
    ∃ s t U V, M.mem s S ∧ M.mem t S ∧ Cyl_d B s U ∧ Cyl_d B t V ∧
      M.mem f U ∧ M.mem g V ∧ M.IsDisjoint U V := by
  obtain ⟨i, a, b, hi, hfa, hgb, hab⟩ := ds_differ_l I hZF.1 ((hB f).mp hf) ((hB g).mp hg) hne
  obtain ⟨n, hni, hn⟩ := hω.1.2 i hi
  obtain ⟨s, hs, hsf, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hf) hn
  obtain ⟨t, ht, htg, _⟩ := ds_prefix_l I hZF hω ((hB g).mp hg) hn
  obtain ⟨U, hU⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
  obtain ⟨V, hV⟩ := cyl_exists_l (ZF.modelsKP hZF) B t
  refine ⟨s, t, U, V, (hS s).mpr ⟨n, hn, hs⟩, (hS t).mpr ⟨n, hn, ht⟩, hU, hV,
    (hU f).mpr ⟨hf, (ds_restrict_iff_l I hs ((hB f).mp hf).1).mp hsf⟩,
    (hV g).mpr ⟨hg, (ds_restrict_iff_l I ht ((hB g).mp hg).1).mp htg⟩, ?_⟩
  intro x ⟨hxU, hxV⟩
  obtain ⟨hx, hsx⟩ := (hU x).mp hxU
  have htx := ((hV x).mp hxV).2
  have ha := ((ds_restrict_iff_l I hs ((hB x).mp hx).1).mpr hsx).2 i a
  have hb := ((ds_restrict_iff_l I ht ((hB x).mp hx).1).mpr htx).2 i b
  exact hab (((hB x).mp hx).1.2 i a b
    ((ha.mp ((hsf.2 i a).mpr ⟨hni.predecessor_mem, hfa⟩)).2)
    ((hb.mp ((htg.2 i b).mpr ⟨hni.predecessor_mem, hgb⟩)).2))

/-- 柱集外的每个点都有与它不交的柱邻域，供补集开放性直接调用。 -/
theorem cyl_outside_l (hZF : M.Models ZF) {ω X B S s n U f}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (hU : Cyl_d B s U)
    (hf : M.mem f B) (hfu : ¬ M.mem f U) :
    ∃ t V, M.mem t S ∧ Cyl_d B t V ∧ M.mem f V ∧ M.IsDisjoint U V := by
  obtain ⟨t, ht, htf, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hf) hn
  obtain ⟨V, hV⟩ := cyl_exists_l (ZF.modelsKP hZF) B t
  have hsub := (ds_restrict_iff_l I ht ((hB f).mp hf).1).mp htf
  refine ⟨t, V, (hS t).mpr ⟨n, hn, ht⟩, hV, (hV f).mpr ⟨hf, hsub⟩, ?_⟩
  intro g ⟨hgu, hgv⟩
  obtain ⟨hg, hsg⟩ := (hU g).mp hgu
  have htg := ((hV g).mp hgv).2
  have e := ((ds_restrict_iff_l I hs ((hB g).mp hg).1).mpr hsg).eq hZF.1
    ((ds_restrict_iff_l I ht ((hB g).mp hg).1).mpr htg)
  exact hfu ((hU f).mpr ⟨hf, e.symm ▸ hsub⟩)

end YesMetaZFC.SetTheory.Descriptive
