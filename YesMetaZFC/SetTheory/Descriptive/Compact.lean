import YesMetaZFC.SetTheory.Descriptive.Path
import YesMetaZFC.SetTheory.Card.Finite

/-! # 内部开覆盖紧致性

有限子覆盖由模型内部的有限集合见证。Cantor 的证明先构造不能有限覆盖的前缀树，
再由其二分后继生成内部坏分支，与原开覆盖矛盾；整个证明仅用 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cover_d (B A : M.Domain) : Prop := ∀ f, M.mem f B → ∃ U, M.mem U A ∧ M.mem f U
def cover_m {d} (B A : Term d) : Formula 1 d :=
  Formula.forallMem B (Formula.existsMem A.weaken (.mem (.bound 1) .newest))
derive_free_closed cover_m
theorem cover_sat_l {d} (ρ : Env M d) (B A : Term d) :
    Formula.satisfies ρ (cover_m B A) ↔ Cover_d (M := M) (B.eval ρ) (A.eval ρ) := by
  simp only [cover_m, Cover_d, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fcyl_d (ω B A s : M.Domain) : Prop := ∃ K, Finite_d I ω K ∧ M.MemberSubset K A ∧
  ∀ f, M.mem f B → M.MemberSubset s f → ∃ U, M.mem U K ∧ M.mem f U
def fcyl_m {d} (ω B A s : Term d) : Formula 1 d := .existsE (.conj
  (finite_m 𝒞 ω.weaken .newest) (.conj (Formula.subset .newest A.weaken)
    (Formula.forallMem B.weaken (.imp (Formula.subset s.weaken.weaken .newest)
      (Formula.existsMem (.bound 1) (.mem (.bound 1) .newest))))))
derive_free_closed fcyl_m
theorem fcyl_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B A s : Term d) :
    Formula.satisfies ρ (fcyl_m (𝒞 := 𝒞) ω B A s) ↔ Fcyl_d I (ω.eval ρ) (B.eval ρ) (A.eval ρ) (s.eval ρ) := by
  simp only [fcyl_m, Fcyl_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    finite_sat_l I hE, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Compact_d (ω B τ : M.Domain) : Prop := ∀ A, M.MemberSubset A τ → Cover_d B A →
  ∃ K, Finite_d I ω K ∧ M.MemberSubset K A ∧ Cover_d B K
def compact_m {d} (ω B τ : Term d) : Formula 1 d := .forallE
  (.imp (Formula.subset .newest τ.weaken) (.imp (cover_m B.weaken .newest) (.existsE
    (.conj (finite_m 𝒞 ω.weaken.weaken .newest) (.conj (Formula.subset .newest (.bound 1))
      (cover_m B.weaken.weaken .newest))))))
derive_free_closed compact_m
@[prove_auto_norm semantic]
theorem compact_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B τ : Term d) :
    Formula.satisfies ρ (compact_m (𝒞 := 𝒞) ω B τ) ↔ Compact_d I (ω.eval ρ) (B.eval ρ) (τ.eval ρ) := by
  simp only [compact_m, Compact_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, cover_sat_l, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, finite_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 两个后继柱集的有限覆盖合并为父柱集的有限覆盖。 -/
theorem ds_fcyl_join_l (hZF : M.Models ZF) {ω D B A s n t u a b}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω D)
    (hD : ∀ x, M.mem x D ↔ x = a ∨ x = b) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n D) (ht : Fseq_end_d I ω t s a) (hu : Fseq_end_d I ω u s b)
    (h : Fcyl_d I ω B A t) (k : Fcyl_d I ω B A u) : Fcyl_d I ω B A s := by
  obtain ⟨K, hk, hKA, hc⟩ := h
  obtain ⟨L, hl, hLA, hd⟩ := k
  obtain ⟨J, hJ⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) K L
  refine ⟨J, ZF.finite_union_l I hZF hω hk hl hJ,
    fun V hV => ((hJ V).mp hV).elim (hKA V) (hLA V), fun f hf hsf => ?_⟩
  obtain ⟨x, hx, hnx⟩ := ((hB f).mp hf).2.2 n hn
  rcases (hD x).mp hx with rfl | rfl
  · obtain ⟨V, hV, hfV⟩ := hc f hf (ds_append_sub_l I hZF.1 hs ht hsf hnx)
    exact ⟨V, (hJ V).mpr (Or.inl hV), hfV⟩
  · obtain ⟨V, hV, hfV⟩ := hd f hf (ds_append_sub_l I hZF.1 hs hu hsf hnx)
    exact ⟨V, (hJ V).mpr (Or.inr hV), hfV⟩

/-- 任意内部二元字母表的序列空间满足开覆盖紧致性。 -/
theorem ds_binary_compact_l (hZF : M.Models ZF) {ω D B S τ a b}
    (hω : M.IsOmega ω) (hD : ∀ x, M.mem x D ↔ x = a ∨ x = b)
    (hB : M.IsFunctionSpace I B ω D) (hS : Fseq_space_d I ω D S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : Compact_d I ω B τ := by
  classical
  intro A hA hcover
  apply Classical.byContradiction
  intro hno
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push A
  let φ : UnarySchema 3 := { body := .neg (fcyl_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ S
  have hT s : M.mem s T ↔ M.mem s S ∧ ¬ Fcyl_d I ω B A s := by
    have h := hT' s
    simp only [φ, Formula.satisfies_neg_iff, fcyl_sat_l I hZF.1] at h
    exact h
  obtain ⟨e, he, heω⟩ := hω.1.1
  have het : M.mem e T := (hT e).mpr ⟨(hS e).mpr ⟨e, heω, ds_empty_fun_l I he⟩,
    fun ⟨K, hk, hKA, hc⟩ => hno ⟨K, hk, hKA, fun f hf => hc f hf (fun p hp => (he p hp).elim)⟩⟩
  have serial s (hsT : M.mem s T) : ∃ t, M.mem t T ∧
      (Fseq_end_d I ω t s a ∨ Fseq_end_d I ω t s b) := by
    obtain ⟨hsS, hsbad⟩ := (hT s).mp hsT
    obtain ⟨n, hn, hs⟩ := (hS s).mp hsS
    obtain ⟨m, t, hm, ht, hta⟩ := ZF.fseq_end_exists_l I hZF hω hn hs ((hD a).mpr (Or.inl rfl))
    obtain ⟨k, u, hk, hu, hub⟩ := ZF.fseq_end_exists_l I hZF hω hn hs ((hD b).mpr (Or.inr rfl))
    by_cases h : Fcyl_d I ω B A t
    · exact ⟨u, (hT u).mpr ⟨(hS u).mpr ⟨k, hk, hu⟩,
        fun g => hsbad (ds_fcyl_join_l I hZF hω hB hD hn hs hta hub h g)⟩, Or.inr hub⟩
    · exact ⟨t, (hT t).mpr ⟨(hS t).mpr ⟨m, hm, ht⟩, h⟩, Or.inl hta⟩
  obtain ⟨f, hf, branch⟩ := ds_binary_path_l I hZF hω
    (fun s hs => (hS s).mp ((hT s).mp hs).1) he het serial
  obtain ⟨U, hUA, hfU⟩ := hcover f ((hB f).mpr hf)
  obtain ⟨s, hsS, hsf, hU⟩ := ((hτ U).mp (hA U hUA)).2 f hfU
  obtain ⟨n, hn, hs⟩ := (hS s).mp hsS
  obtain ⟨t, htT, ht, htf⟩ := branch n hn
  have e := ((ds_restrict_iff_l I hs hf.1).mpr hsf).eq hZF.1 ((ds_restrict_iff_l I ht hf.1).mpr htf)
  subst t
  apply ((hT s).mp htT).2
  obtain ⟨E, hE⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := KP.exists_insert (ZF.modelsKP hZF) E U
  have hk := ZF.finite_insert_l I hZF hω (ZF.finite_empty_l I hZF hω hE) hK
  exact ⟨K, hk, fun V hV => ((hK V).mp hV).elim (fun h => (hE V h).elim) (fun e => e ▸ hUA),
    fun g hg hsg => ⟨U, (hK U).mpr (Or.inr rfl), hU g hg hsg⟩⟩

/-- Cantor 紧致性的最终接口；字母表和二分选择均由已有具体构造提供。 -/
theorem cantor_compact_l (hZF : M.Models ZF) {ω D C S τ}
    (hω : M.IsOmega ω) (hD : M.IsOrdinalTwo D) (hC : M.IsFunctionSpace I C ω D)
    (hS : Fseq_space_d I ω D S) (hτ : ∀ U, M.mem U τ ↔ Open_d S C U) : Compact_d I ω C τ := by
  obtain ⟨a, b, _, hd⟩ := ds_two_l hZF.1 hD
  exact ds_binary_compact_l I hZF hω hd hC hS hτ

end YesMetaZFC.SetTheory.Descriptive
