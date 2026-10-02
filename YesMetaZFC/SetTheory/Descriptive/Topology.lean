import YesMetaZFC.SetTheory.Descriptive.Cylinder
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 由内部有限前缀生成的拓扑

开集及拓扑族本身都是模型中的集合。任意并仅量化模型中的开集族；基本邻域
使用全部内部有限列。先核验基，再由幂集分离构造完整拓扑。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Open_d (S B U : M.Domain) : Prop := M.MemberSubset U B ∧ ∀ f, M.mem f U →
  ∃ s, M.mem s S ∧ M.MemberSubset s f ∧ ∀ g, M.mem g B → M.MemberSubset s g → M.mem g U

def open_m {d} (S B U : Term d) : Formula 1 d := .conj (Formula.subset U B)
  (Formula.forallMem U (Formula.existsMem S.weaken (.conj (Formula.subset .newest (.bound 1))
    (Formula.forallMem B.weaken.weaken (.imp (Formula.subset (.bound 1) .newest)
      (.mem .newest U.weaken.weaken.weaken))))))
derive_free_closed open_m

@[prove_auto_norm semantic]
theorem open_sat_l {d} (ρ : Env M d) (S B U : Term d) :
    Formula.satisfies ρ (open_m S B U) ↔ Open_d (M := M) (S.eval ρ) (B.eval ρ) (U.eval ρ) := by
  simp only [open_m, Open_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 给定内部开集族的通常拓扑公理。 -/
def Top_d (B τ : M.Domain) : Prop :=
  (∀ U, M.mem U τ → M.MemberSubset U B) ∧ M.mem B τ ∧
  (∃ e, (∀ x, ¬ M.mem x e) ∧ M.mem e τ) ∧
  (∀ U V, M.mem U τ → M.mem V τ → ∃ W,
    (∀ x, M.mem x W ↔ M.mem x U ∧ M.mem x V) ∧ M.mem W τ) ∧
  ∀ A, M.MemberSubset A τ → ∃ U, M.IsUnionOf U A ∧ M.mem U τ

def top_m {d} (B τ : Term d) : Formula 1 d := .conj
  (Formula.forallMem τ (Formula.subset .newest B.weaken)) (.conj (.mem B τ) (.conj
    (.existsE (.conj (Formula.isEmpty .newest) (.mem .newest τ.weaken))) (.conj
      (Formula.forallMem τ (Formula.forallMem τ.weaken (.existsE (.conj
        (.forallE (.iff (.mem .newest (.bound 1))
          (.conj (.mem .newest (.bound 3)) (.mem .newest (.bound 2)))))
        (.mem .newest τ.weaken.weaken.weaken)))))
      (.forallE (.imp (Formula.subset .newest τ.weaken) (.existsE
        (.conj (Formula.isUnion .newest (.bound 1)) (.mem .newest τ.weaken.weaken))))))))

@[simp] theorem top_closed_l {d} (B τ : Term d) (hB : B.freeSupport = []) (hτ : τ.freeSupport = []) :
    (top_m B τ).FreeClosed := by
  simp -implicitDefEqProofs [top_m, Definitional.Formula.FreeClosed, hB, hτ]

@[prove_auto_norm semantic]
theorem top_sat_l {d} (ρ : Env M d) (B τ : Term d) :
    Formula.satisfies ρ (top_m B τ) ↔ Top_d (M := M) (B.eval ρ) (τ.eval ρ) := by
  simp only [top_m, Top_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isUnion_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨h, hB, he, hi, hu⟩
    exact ⟨h, hB, he, fun U V hU hV => hi U hU V hV, hu⟩
  · rintro ⟨h, hB, he, hi, hu⟩
    exact ⟨h, hB, he, fun U hU V hV => hi U V hU hV, hu⟩

theorem ds_open_empty_l {S B e : M.Domain} (he : ∀ x, ¬ M.mem x e) : Open_d S B e :=
  ⟨fun x hx => (he x hx).elim, fun x hx => (he x hx).elim⟩

theorem ds_open_cyl_l {S B s U : M.Domain} (hs : M.mem s S) (hU : Cyl_d B s U) : Open_d S B U :=
  ⟨cyl_subset_l hU, fun f hf => ⟨s, hs, ((hU f).mp hf).2, fun g hg hsg => (hU g).mpr ⟨hg, hsg⟩⟩⟩

theorem ds_open_union_l {S B A U : M.Domain} (hA : ∀ V, M.mem V A → Open_d S B V)
    (hU : M.IsUnionOf U A) : Open_d S B U := by
  refine ⟨fun f hf => ((hU f).mp hf).elim fun V h => (hA V h.1).1 f h.2, ?_⟩
  intro f hf
  obtain ⟨V, hV, hf⟩ := (hU f).mp hf
  obtain ⟨s, hs, hsf, h⟩ := (hA V hV).2 f hf
  exact ⟨s, hs, hsf, fun g hg hsg => (hU g).mpr ⟨V, hV, h g hg hsg⟩⟩

theorem ds_open_inter_l (hE : Extensional M) {ω X B S U V W}
    (hω : M.IsOrdinal ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hU : Open_d S B U) (hV : Open_d S B V)
    (hW : ∀ f, M.mem f W ↔ M.mem f U ∧ M.mem f V) : Open_d S B W := by
  refine ⟨fun f hf => hU.1 f ((hW f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hu, hv⟩ := (hW f).mp hf
  obtain ⟨s, hs, hsf, hsu⟩ := hU.2 f hu
  obtain ⟨t, ht, htf, htv⟩ := hV.2 f hv
  obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
  obtain ⟨m, hm, htm⟩ := (hS t).mp ht
  rcases ds_prefix_compare_l I hE hω hn hm hsn htm ((hB f).mp (hU.1 f hu)).1 hsf htf with hst | hts
  · exact ⟨t, ht, htf, fun g hg htg => (hW g).mpr
      ⟨hsu g hg (fun p hp => htg p (hst p hp)), htv g hg htg⟩⟩
  · exact ⟨s, hs, hsf, fun g hg hsg => (hW g).mpr
      ⟨hsu g hg hsg, htv g hg (fun p hp => hsg p (hts p hp))⟩⟩

theorem ds_open_whole_l (hZF : M.Models ZF) {ω X B S}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S) : Open_d S B B := by
  refine ⟨fun _ h => h, fun f hf => ?_⟩
  obtain ⟨n, _, hn⟩ := hω.1.1
  obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hf) hn
  exact ⟨s, (hS s).mpr ⟨n, hn, hs⟩, (ds_restrict_iff_l I hs ((hB f).mp hf).1).mp hr, fun _ h _ => h⟩

/-- 从实际空间和全部有限列直接构造拓扑，并核验全部内部拓扑公理。 -/
theorem ds_topology_l (hZF : M.Models ZF) {ω X B S}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S) :
    ∃ τ, Top_d B τ ∧ ∀ U, M.mem U τ ↔ Open_d S B U := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 2 := (⟨fun _ => S, fun _ => S⟩ : Env M 1).push B
  let φ : UnarySchema 2 := { body := open_m (.bound 2) (.bound 1) .newest }
  obtain ⟨τ, hτ⟩ := ZF.separation_exists_d hZF φ ρ P
  have ht U : M.mem U τ ↔ Open_d S B U := by
    have h := (hτ U).trans (and_congr_right fun _ => open_sat_l (ρ.push U) _ _ _)
    exact h.trans ⟨And.right, fun h => ⟨(hP U).mpr h.1, h⟩⟩
  refine ⟨τ, ⟨fun U hU => ((ht U).mp hU).1, (ht B).mpr (ds_open_whole_l I hZF hω hB hS), ?_, ?_, ?_⟩, ht⟩
  · obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact ⟨e, he, (ht e).mpr (ds_open_empty_l he)⟩
  · intro U V hU hV
    obtain ⟨W, hW⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) U V
    exact ⟨W, hW, (ht W).mpr (ds_open_inter_l I hZF.1 (hω.isOrdinal hZF) hB hS
      ((ht U).mp hU) ((ht V).mp hV) hW)⟩
  · intro A hA
    obtain ⟨U, hU⟩ := KP.exists_union (ZF.modelsKP hZF) A
    exact ⟨U, hU, (ht U).mpr (ds_open_union_l (fun V hV => (ht V).mp (hA V hV)) hU)⟩

/-- 柱集的相对补也是开集。 -/
theorem ds_cyl_clopen_l (hZF : M.Models ZF) {ω X B S s U}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hs : M.mem s S) (hU : Cyl_d B s U) : Open_d S B U ∧
      ∃ V, (∀ f, M.mem f V ↔ M.mem f B ∧ ¬ M.mem f U) ∧ Open_d S B V := by
  obtain ⟨V, hV⟩ := KP.difference_exists_d (ZF.modelsKP hZF) U B
  refine ⟨ds_open_cyl_l hs hU, V, hV, fun f hf => ((hV f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
  obtain ⟨hfB, hfU⟩ := (hV f).mp hf
  obtain ⟨t, W, ht, hW, hfW, hUW⟩ := cyl_outside_l I hZF hω hB hS hn hsn hU hfB hfU
  exact ⟨t, ht, ((hW f).mp hfW).2, fun g hg htg => (hV g).mpr
    ⟨hg, fun hgu => hUW g ⟨hgu, (hW g).mpr ⟨hg, htg⟩⟩⟩⟩

/-- 字母表至少有两个元素时，每个点的任意开邻域都含有另一个点。 -/
theorem ds_no_isolated_l (hZF : M.Models ZF) {ω X B S U f a b}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (ha : M.mem a X) (hb : M.mem b X) (hab : a ≠ b) (hU : Open_d S B U) (hf : M.mem f U) :
    ∃ g, M.mem g U ∧ g ≠ f := by
  classical
  obtain ⟨s, hs, _, hu⟩ := hU.2 f hf
  obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
  obtain ⟨g, h, hg, hh, hsg, hsh, hgh⟩ := ds_split_l I hZF hω hn hsn ha hb hab
  by_cases e : g = f
  · exact ⟨h, hu h ((hB h).mpr hh) hsh, fun eh => hgh (e.trans eh.symm)⟩
  · exact ⟨g, hu g ((hB g).mpr hg) hsg, e⟩

/-- 有限列到柱集的索引也是内部函数图，可直接作为可数基的编码使用。 -/
theorem ds_basis_l (hZF : M.Models ZF) {B S P : M.Domain} (hP : M.IsPowerSetOf P B) :
    ∃ F, M.IsSetFunctionFromTo I F S P ∧ ∀ s U, M.PairMember I s U F ↔ M.mem s S ∧ Cyl_d B s U := by
  let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let φ : BinarySchema 1 := { body := cyl_m (.bound 2) (.bound 1) .newest }
  have hp s U : φ.denote ρ s U ↔ Cyl_d B s U := cyl_sat_l _ _ _ _
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := S) (target := P)
    (fun s _ => (cyl_exists_l (ZF.modelsKP hZF) B s).imp fun U hU => (hp s U).mpr hU)
    (fun s _ U V hU hV => cyl_unique_l hZF.1 ((hp s U).mp hU) ((hp s V).mp hV))
    (fun s U _ hU => (hP U).mpr (cyl_subset_l ((hp s U).mp hU)))
  exact ⟨F, hF, fun s U => (hf s U).trans (and_congr_right fun _ => hp s U)⟩

/-- 把可数前缀索引收集为实际可数基；重名柱集通过最小原像编号消去。 -/
theorem ds_countable_basis_l (hZF : M.Models ZF) {ω B S : M.Domain}
    (hω : M.IsOmega ω) (hs : M.CardinalLessOrEqual I S ω) : ∃ K,
    M.CardinalLessOrEqual I K ω ∧
    (∀ V, M.mem V K ↔ ∃ s, M.mem s S ∧ Cyl_d B s V) ∧
    ∀ U, Open_d S B U ↔ M.MemberSubset U B ∧
      ∀ f, M.mem f U → ∃ V, M.mem V K ∧ M.mem f V ∧ M.MemberSubset V U := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  obtain ⟨F, hF, hf⟩ := ds_basis_l I hZF (S := S) hP
  obtain ⟨K, hK⟩ := ZF.exists_range_of_setFunction hZF I hF.1 hF.2.1
  have hk V : M.mem V K ↔ ∃ s, M.mem s S ∧ Cyl_d B s V :=
    (hK V).trans (exists_congr fun s => hf s V)
  have fk : M.IsSetFunctionFromTo I F S K := ⟨hF.1, hF.2.1, fun s hs =>
    (hF.2.2 s hs).elim fun V hV => ⟨V, (hK V).mpr ⟨s, hV.2⟩, hV.2⟩⟩
  have fs : M.IsSetSurjectiveOnto I F S K := fun V hV =>
    ((hK V).mp hV).elim fun s hs => ⟨s, hF.input_mem_of_pairMember hs, hs⟩
  refine ⟨K, ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) hs fk fs, hk, fun U => ⟨?_, ?_⟩⟩
  · intro hU
    refine ⟨hU.1, fun f hfU => ?_⟩
    obtain ⟨s, hs, hsf, hu⟩ := hU.2 f hfU
    obtain ⟨V, hV⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
    exact ⟨V, (hk V).mpr ⟨s, hs, hV⟩, (hV f).mpr ⟨hU.1 f hfU, hsf⟩,
      fun g hg => hu g ((hV g).mp hg).1 ((hV g).mp hg).2⟩
  · rintro ⟨hUB, hU⟩
    refine ⟨hUB, fun f hfU => ?_⟩
    obtain ⟨V, hVK, hfV, hVU⟩ := hU f hfU
    obtain ⟨s, hs, hV⟩ := (hk V).mp hVK
    exact ⟨s, hs, ((hV f).mp hfV).2, fun g hg hsg => hVU g ((hV g).mpr ⟨hg, hsg⟩)⟩

end YesMetaZFC.SetTheory.Descriptive
