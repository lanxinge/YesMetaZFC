import YesMetaZFC.Model.Forcing.TwoStep.Flatten.Syntax

/-! # 三层条目递归的唯一性及部分图装配

摊平的递归参数严格沿三层原名称条目下降。部分图以实际模型集合取并及添根，
唯一性由固定深度的内部公式归纳给出。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

private def flat_unique_m {n} (B R z C x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (.conj (flat_m B.weaken.weaken R.weaken.weaken z.weaken.weaken C.weaken.weaken x.weaken.weaken (.bound 1))
      (flat_m B.weaken.weaken R.weaken.weaken z.weaken.weaken C.weaken.weaken x.weaken.weaken .newest))
    (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed flat_unique_m

theorem flat_unique_l (hE : Extensional M) (hI : Mem_ind_d M) (B R z C x : M.Domain) :
    ∀ s t, Flat_d M B R z C x s → Flat_d M B R z C x t → s = t := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push C
  let φ : UnarySchema 4 := { body := flat_unique_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Flat_d M B R z C x s ∧ Flat_d M B R z C x t → s = t := by
    simp only [UnarySchema.denote, φ, flat_unique_m, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, flat_sat_l M hE,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    rfl
  have hall := entry_path_ind_l hE hI 3 (by decide) φ ρ (fun x ih => (hφ x).mpr (by
    rintro s t ⟨⟨H, hH, hs⟩, ⟨J, hJ, ht⟩⟩
    have sub {H J s t} (hH : Flat_graph_d M B R z C H) (hJ : Flat_graph_d M B R z C J)
        (hs : Entry_d M x s H) (ht : Entry_d M x t J) : ∀ v, M.mem v s → M.mem v t := by
      intro v hv
      obtain ⟨a, c, p, b, u, ha, hc, hcp, hf, hau, hv⟩ := ((hH.2 x s hs).2 v).mp hv
      obtain ⟨w, haw⟩ := (hJ.2 x t ht).1 a ha
      have he := (hφ a).mp (ih a ha) u w ⟨⟨H, hH, hau⟩, ⟨J, hJ, haw⟩⟩
      exact ((hJ.2 x t ht).2 v).mpr ⟨a, c, p, b, w, ha, hc, hcp, hf, haw, he ▸ hv⟩
    exact hE.eq_of_same_members s t (fun v => ⟨sub hH hJ hs ht v, sub hJ hH ht hs v⟩)))
  exact fun s t hs ht => (hφ x).mp (hall x) s t ⟨hs, ht⟩

/-- 摊平后的成员递归式直接消费子名称的摊平关系。 -/
theorem flat_mem_l (hE : Extensional M) (hI : Mem_ind_d M) {B R z C x t}
    (h : Flat_d M B R z C x t) (v) : M.mem v t ↔ ∃ a c p s u,
      Entry_path_d M 3 x a ∧ M.mem c C ∧ KPair_d M c p s ∧ Rel_force_d M B R z x p a s ∧
        Flat_d M B R z C a u ∧ KPair_d M v u c := by
  obtain ⟨H, hH, ht⟩ := h
  constructor
  · intro hv
    obtain ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩ := ((hH.2 x t ht).2 v).mp hv
    exact ⟨a, c, p, s, u, ha, hc, hcp, hf, ⟨H, hH, hau⟩, hv⟩
  · rintro ⟨a, c, p, s, u, ha, hc, hcp, hf, hu, hv⟩
    obtain ⟨w, haw⟩ := (hH.2 x t ht).1 a ha
    have he := flat_unique_l M hE hI B R z C a u w hu ⟨H, hH, haw⟩
    exact ((hH.2 x t ht).2 v).mpr ⟨a, c, p, s, w, ha, hc, hcp, hf, haw, he ▸ hv⟩

theorem flat_union_l (hE : Extensional M) (hI : Mem_ind_d M) {B R z C A H}
    (hA : ∀ J, M.mem J A → Flat_graph_d M B R z C J) (hH : M.IsUnionOf H A) : Flat_graph_d M B R z C H := by
  refine ⟨fun v hv => ?_, fun x t ht => ?_⟩
  · obtain ⟨J, hJ, hv⟩ := (hH v).mp hv
    exact (hA J hJ).1 v hv
  · obtain ⟨J, hJ, ht⟩ := (entry_union_l M hH x t).mp ht
    have hj := hA J hJ
    refine ⟨fun a ha => ?_, fun v => ?_⟩
    · obtain ⟨u, hau⟩ := (hj.2 x t ht).1 a ha
      exact ⟨u, (entry_union_l M hH a u).mpr ⟨J, hJ, hau⟩⟩
    · constructor
      · intro hv
        obtain ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩ := ((hj.2 x t ht).2 v).mp hv
        exact ⟨a, c, p, s, u, ha, hc, hcp, hf, (entry_union_l M hH a u).mpr ⟨J, hJ, hau⟩, hv⟩
      · rintro ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩
        obtain ⟨F, hF, hau⟩ := (entry_union_l M hH a u).mp hau
        obtain ⟨w, haw⟩ := (hj.2 x t ht).1 a ha
        have he := flat_unique_l M hE hI B R z C a u w ⟨F, hA F hF, hau⟩ ⟨J, hj, haw⟩
        exact ((hj.2 x t ht).2 v).mpr ⟨a, c, p, s, w, ha, hc, hcp, hf, haw, he ▸ hv⟩

theorem flat_adjoin_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) (hU : ∀ F, ∃ S, M.IsUnionOf S F)
    {B R z C H x t} (hH : Flat_graph_d M B R z C H) (ht : Flat_step_d M B R z C H x t) : Flat_d M B R z C x t := by
  obtain ⟨p, hp⟩ := (kpair_interpretation_l M hE hP).total x t
  obtain ⟨J, hJ⟩ := set_insert_l M hP hU H p
  have hj y s : Entry_d M y s J ↔ Entry_d M y s H ∨ (y = x ∧ s = t) := by
    constructor
    · rintro ⟨v, hv, hvJ⟩
      rcases (hJ v).mp hvJ with hvH | rfl
      · exact Or.inl ⟨v, hv, hvH⟩
      · exact Or.inr (kpair_injective_l M hv hp)
    · rintro (⟨v, hv, hvH⟩ | ⟨rfl, rfl⟩)
      · exact ⟨v, hv, (hJ v).mpr (Or.inl hvH)⟩
      · exact ⟨p, hp, (hJ p).mpr (Or.inr rfl)⟩
  have agree {y s a} (hs : Entry_d M y s J) (ha : Entry_d M y a H) : s = a := by
    rcases (hj y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact flat_unique_l M hE hI B R z C y s a ⟨H, hH, hs⟩ ⟨H, hH, ha⟩
    · exact hE.eq_of_same_members _ _ (fun v => (ht.2 v).trans ((hH.2 y a ha).2 v).symm)
  have step {y s} (hs : Flat_step_d M B R z C H y s) : Flat_step_d M B R z C J y s := by
    refine ⟨fun a ha => ?_, fun v => ?_⟩
    · obtain ⟨u, hau⟩ := hs.1 a ha
      exact ⟨u, (hj a u).mpr (Or.inl hau)⟩
    · constructor
      · intro hv
        obtain ⟨a, c, p, b, u, ha, hc, hcp, hf, hau, hv⟩ := (hs.2 v).mp hv
        exact ⟨a, c, p, b, u, ha, hc, hcp, hf, (hj a u).mpr (Or.inl hau), hv⟩
      · rintro ⟨a, c, p, b, u, ha, hc, hcp, hf, hau, hv⟩
        obtain ⟨w, haw⟩ := hs.1 a ha
        exact (hs.2 v).mpr ⟨a, c, p, b, w, ha, hc, hcp, hf, haw, agree hau haw ▸ hv⟩
  refine ⟨J, ⟨?_, ?_⟩, (hj x t).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro v hv
    rcases (hJ v).mp hv with hv | rfl
    · exact hH.1 v hv
    · exact ⟨x, t, hp⟩
  · intro y s hs
    rcases (hj y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact step (hH.2 y s hs)
    · exact step ht

theorem flat_entry_l (hE : Extensional M) (hI : Mem_ind_d M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    {B R z C x t} (h : Flat_d M B R z C x t) (u c) : Entry_d M u c t ↔ ∃ a p s,
      Entry_path_d M 3 x a ∧ M.mem c C ∧ KPair_d M c p s ∧ Rel_force_d M B R z x p a s ∧ Flat_d M B R z C a u := by
  constructor
  · rintro ⟨v, hv, hvt⟩
    obtain ⟨a, c', p, s, u', ha, hc, hcp, hf, hau, hv'⟩ := (flat_mem_l M hE hI h v).mp hvt
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨a, p, s, ha, hc, hcp, hf, hau⟩
  · rintro ⟨a, p, s, ha, hc, hcp, hf, hau⟩
    obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total u c
    exact ⟨v, hv, (flat_mem_l M hE hI h v).mpr ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩⟩

end YesMetaZFC.Model.Forcing.Internal
