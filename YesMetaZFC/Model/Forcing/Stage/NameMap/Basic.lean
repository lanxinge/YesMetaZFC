import YesMetaZFC.Model.Forcing.Stage.NameMap.Syntax
import YesMetaZFC.Model.Forcing.Internal.Extension.Foundation

/-! # 名称搬运递归的唯一性与部分图装配

唯一性使用原公式的内部条目归纳。部分图的并与添加新根由此相容，所有标签
关系和递归图都保留为模型内集合；不选取外部递归函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

private def nmap_unique_m {n} (K x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (.conj (nmap_m K.weaken.weaken x.weaken.weaken (.bound 1))
    (nmap_m K.weaken.weaken x.weaken.weaken .newest)) (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed nmap_unique_m

theorem nmap_unique_l (hE : Extensional M) (hI : Mem_ind_d M) (K x : M.Domain) :
    ∀ s t, Nmap_d M K x s → Nmap_d M K x t → s = t := by
  let ρ : Env M 1 := ⟨fun _ => K, fun _ => K⟩
  let φ : UnarySchema 1 := { body := nmap_unique_m (.bound 1) .newest }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Nmap_d M K x s ∧ Nmap_d M K x t → s = t := by
    simp only [UnarySchema.denote, φ, nmap_unique_m, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, nmap_sat_l M hE,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken,
      Definitional.Term.eval_newest]
    rfl
  have hall := entry_ind_l hI φ ρ (fun x ih => (hφ x).mpr (by
    rintro s t ⟨⟨H, hH, hs⟩, ⟨J, hJ, ht⟩⟩
    have sub {H J s t} (hH : Nmap_graph_d M K H) (hJ : Nmap_graph_d M K J)
        (hs : Entry_d M x s H) (ht : Entry_d M x t J) : ∀ v, M.mem v s → M.mem v t := by
      intro v hv
      obtain ⟨a, b, c, d, hab, hac, hbd, hv⟩ := ((hH.2 x s hs).2 v).mp hv
      obtain ⟨e, hae⟩ := (hJ.2 x t ht).1 a b hab
      have he := (hφ a).mp (ih a b hab) c e ⟨⟨H, hH, hac⟩, ⟨J, hJ, hae⟩⟩
      exact ((hJ.2 x t ht).2 v).mpr ⟨a, b, e, d, hab, hae, hbd, he ▸ hv⟩
    exact hE.eq_of_same_members s t (fun v => ⟨sub hH hJ hs ht v, sub hJ hH ht hs v⟩)))
  exact fun s t hs ht => (hφ x).mp (hall x) s t ⟨hs, ht⟩

/-- 搬运后的逐成员递归式，不再向调用者暴露部分递归图。 -/
theorem nmap_mem_l (hE : Extensional M) (hI : Mem_ind_d M) {K x t} (h : Nmap_d M K x t) (v) :
    M.mem v t ↔ ∃ s b a c, Entry_d M s b x ∧ Nmap_d M K s a ∧ Entry_d M b c K ∧ KPair_d M v a c := by
  obtain ⟨H, hH, ht⟩ := h
  constructor
  · intro hv
    obtain ⟨s, b, a, c, hs, ha, hc, hv⟩ := ((hH.2 x t ht).2 v).mp hv
    exact ⟨s, b, a, c, hs, ⟨H, hH, ha⟩, hc, hv⟩
  · rintro ⟨s, b, a, c, hs, ha, hc, hv⟩
    obtain ⟨a', ha'⟩ := (hH.2 x t ht).1 s b hs
    have he := nmap_unique_l M hE hI K s a a' ha ⟨H, hH, ha'⟩
    exact ((hH.2 x t ht).2 v).mpr ⟨s, b, a', c, hs, ha', hc, he ▸ hv⟩

theorem nmap_union_l (hE : Extensional M) (hI : Mem_ind_d M) {K A H}
    (hA : ∀ J, M.mem J A → Nmap_graph_d M K J) (hH : M.IsUnionOf H A) : Nmap_graph_d M K H := by
  constructor
  · intro v hv
    obtain ⟨J, hJ, hv⟩ := (hH v).mp hv
    exact (hA J hJ).1 v hv
  · intro x t ht
    obtain ⟨J, hJ, ht⟩ := (entry_union_l M hH x t).mp ht
    have hj := hA J hJ
    refine ⟨fun s b hs => ?_, fun v => ?_⟩
    · obtain ⟨a, ha⟩ := (hj.2 x t ht).1 s b hs
      exact ⟨a, (entry_union_l M hH s a).mpr ⟨J, hJ, ha⟩⟩
    · constructor
      · intro hv
        obtain ⟨s, b, a, c, hs, ha, hc, hv⟩ := ((hj.2 x t ht).2 v).mp hv
        exact ⟨s, b, a, c, hs, (entry_union_l M hH s a).mpr ⟨J, hJ, ha⟩, hc, hv⟩
      · rintro ⟨s, b, a, c, hs, ha, hc, hv⟩
        obtain ⟨F, hF, ha⟩ := (entry_union_l M hH s a).mp ha
        obtain ⟨a', ha'⟩ := (hj.2 x t ht).1 s b hs
        have he := nmap_unique_l M hE hI K s a a' ⟨F, hA F hF, ha⟩ ⟨J, hj, ha'⟩
        exact ((hj.2 x t ht).2 v).mpr ⟨s, b, a', c, hs, ha', hc, he ▸ hv⟩

theorem nmap_adjoin_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) (hU : ∀ F, ∃ S, M.IsUnionOf S F)
    {K H x t} (hH : Nmap_graph_d M K H) (ht : Nmap_step_d M K H x t) : Nmap_d M K x t := by
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
    · exact nmap_unique_l M hE hI K y s a ⟨H, hH, hs⟩ ⟨H, hH, ha⟩
    · exact hE.eq_of_same_members _ _ (fun v => (ht.2 v).trans ((hH.2 y a ha).2 v).symm)
  have step {y s} (hs : Nmap_step_d M K H y s) : Nmap_step_d M K J y s := by
    refine ⟨fun a b hab => ?_, fun v => ?_⟩
    · obtain ⟨c, hc⟩ := hs.1 a b hab
      exact ⟨c, (hj a c).mpr (Or.inl hc)⟩
    · constructor
      · intro hv
        obtain ⟨a, b, c, d, hab, hac, hbd, hv⟩ := (hs.2 v).mp hv
        exact ⟨a, b, c, d, hab, (hj a c).mpr (Or.inl hac), hbd, hv⟩
      · rintro ⟨a, b, c, d, hab, hac, hbd, hv⟩
        obtain ⟨c', hc'⟩ := hs.1 a b hab
        exact (hs.2 v).mpr ⟨a, b, c', d, hab, hc', hbd, agree hac hc' ▸ hv⟩
  refine ⟨J, ⟨?_, ?_⟩, (hj x t).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro v hv
    rcases (hJ v).mp hv with hv | rfl
    · exact hH.1 v hv
    · exact ⟨x, t, hp⟩
  · intro y s hs
    rcases (hj y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact step (hH.2 y s hs)
    · exact step ht

theorem nmap_entry_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {K x t} (h : Nmap_d M K x t) (a c) :
    Entry_d M a c t ↔ ∃ s b, Entry_d M s b x ∧ Nmap_d M K s a ∧ Entry_d M b c K := by
  constructor
  · rintro ⟨v, hv, hvt⟩
    obtain ⟨s, b, a', c', hs, ha, hc, hv'⟩ := (nmap_mem_l M hE hI h v).mp hvt
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨s, b, hs, ha, hc⟩
  · rintro ⟨s, b, hs, ha, hc⟩
    obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total a c
    exact ⟨v, hv, (nmap_mem_l M hE hI h v).mpr ⟨s, b, a, c, hs, ha, hc, hv⟩⟩

end YesMetaZFC.Model.Forcing.Internal
