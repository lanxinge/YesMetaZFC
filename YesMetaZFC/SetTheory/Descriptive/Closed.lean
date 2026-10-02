import YesMetaZFC.SetTheory.Descriptive.Projection

/-! # 闭集的规范前缀树表示 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cl_d (A B K : M.Domain) : Prop := M.MemberSubset K B ∧ ∃ U, Cm_d B K U ∧ Open_d A B U
def cl_m {d} (A B K : Term d) : Formula 1 d := .conj (Formula.subset K B)
  (.existsE (.conj (cm_m B.weaken K.weaken .newest) (open_m A.weaken B.weaken .newest)))
derive_free_closed cl_m

theorem cl_sat_l {d} (ρ : Env M d) (A B K : Term d) :
    Formula.satisfies ρ (cl_m A B K) ↔ Cl_d (M := M) (A.eval ρ) (B.eval ρ) (K.eval ρ) := by
  simp only [cl_m, Cl_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, cm_sat_l, open_sat_l, Definitional.Term.eval_weaken]; rfl

omit I in
theorem closed_tree_l (hKP : M.Models KP) {A B K : M.Domain} :
    Cl_d A B K ↔ ∃ T, Tree_d A T ∧ Body_d A B T K := by
  constructor
  · rintro ⟨hKB, U, hU, ho⟩
    obtain ⟨T, _, ht, hb⟩ := tree_of_closed_l hKP hKB hU ho
    exact ⟨T, ht, hb⟩
  · rintro ⟨T, _, hb⟩
    exact ⟨fun x hx => ((hb x).mp hx).1, tree_body_closed_l hKP hb⟩

omit I in
theorem closed_ktree_l (hKP : M.Models KP) {A B K : M.Domain} (h : Cl_d A B K) :
    ∃ T, Ktree_d A K T ∧ Tree_d A T ∧ Body_d A B T K ∧ ∀ U, Ktree_d A K U → U = T := by
  obtain ⟨hKB, U, hU, ho⟩ := h
  obtain ⟨T, hk, ht, hb⟩ := tree_of_closed_l hKP hKB hU ho
  exact ⟨T, hk, ht, hb, fun U hu => ktree_unique_l hKP.1 hu hk⟩

/-- 规范树中的每个节点都有下一层延拓，包括非标准长度的节点。 -/
theorem ktree_pruned_l (hZF : M.Models ZF) {ω A B K T} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hK : M.MemberSubset K B) (hT : Ktree_d A K T) :
    ∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t := by
  intro s hs
  obtain ⟨hsA, f, hfK, hsf⟩ := (hT s).mp hs
  obtain ⟨n, hn, hs⟩ := (hA s).mp hsA
  have hf := (hB.2 f).mp (hK f hfK)
  obtain ⟨m, hm, hmω⟩ := hB.1.1.2 n hn
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 hf hmω
  have htf := (ds_restrict_iff_l I ht hf.1).mp hr
  have hst := ds_prefix_mono_l I hs ht.1 ((ds_restrict_iff_l I hs hf.1).mpr hsf) hr (fun i hi => (hm i).mpr (Or.inl hi))
  exact ⟨t, (hT t).mpr ⟨(hA t).mpr ⟨m, hmω, ht⟩, f, hfK, htf⟩,
    (tree_step_iff_l I hZF hB.1 hn hmω hs ht).mpr ⟨hm, hst⟩⟩

end YesMetaZFC.SetTheory.Descriptive
