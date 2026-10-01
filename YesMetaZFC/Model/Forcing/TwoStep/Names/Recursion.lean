import YesMetaZFC.Model.Forcing.TwoStep.Names.Syntax
import YesMetaZFC.Model.Forcing.Internal.Extension.Foundation

/-! # 两步名称转换的内部递归

部分图的唯一性沿实际条目公式归纳。由此可把任意内部集合族的部分解取并，
再加入下一转换值；整个递归不使用外部良基次序。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

private def curry_unique_m {n} (B C x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (.conj (curry_m B.weaken.weaken C.weaken.weaken x.weaken.weaken (.bound 1))
    (curry_m B.weaken.weaken C.weaken.weaken x.weaken.weaken .newest)) (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed curry_unique_m

theorem curry_unique_l (hE : Extensional M) (hI : Mem_ind_d M) (B C x : M.Domain) :
    ∀ s t, Curry_d M B C x s → Curry_d M B C x t → s = t := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push C
  let φ : UnarySchema 2 := { body := curry_unique_m (.bound 2) (.bound 1) .newest }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Curry_d M B C x s ∧ Curry_d M B C x t → s = t := by
    simp only [UnarySchema.denote, φ, curry_unique_m, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, curry_sat_l M hE,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    rfl
  have hall := entry_ind_l hI φ ρ (fun x ih => (hφ x).mpr (by
    rintro s t ⟨⟨H, hH, hs⟩, ⟨J, hJ, ht⟩⟩
    have sub {H J s t} (hH : Curry_graph_d M B C H) (hJ : Curry_graph_d M B C J)
        (hs : Entry_d M x s H) (ht : Entry_d M x t J) : ∀ v, M.mem v s → M.mem v t := by
      intro v hv
      obtain ⟨a, c, u, p, b, k, hac, hc, hcp, hau, hk, hv⟩ := ((hH.2 x s hs).2 v).mp hv
      obtain ⟨u', hau'⟩ := (hJ.2 x t ht).1 a c hac
      have he := (hφ a).mp (ih a c hac) u u' ⟨⟨H, hH, hau⟩, ⟨J, hJ, hau'⟩⟩
      exact ((hJ.2 x t ht).2 v).mpr ⟨a, c, u', p, b, k, hac, hc, hcp, hau', he ▸ hk, hv⟩
    exact hE.eq_of_same_members s t (fun v => ⟨sub hH hJ hs ht v, sub hJ hH ht hs v⟩)))
  exact fun s t hs ht => (hφ x).mp (hall x) s t ⟨hs, ht⟩

theorem curry_mem_l (hE : Extensional M) (hI : Mem_ind_d M) {B C x t} (h : Curry_d M B C x t) (v) :
    M.mem v t ↔ ∃ a c u p s k, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧
      Curry_d M B C a u ∧ Nkpair_d M B u s k ∧ KPair_d M v k p := by
  obtain ⟨H, hH, ht⟩ := h
  constructor
  · intro hv
    obtain ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩ := ((hH.2 x t ht).2 v).mp hv
    exact ⟨a, c, u, p, s, k, hac, hc, hcp, ⟨H, hH, hau⟩, hk, hv⟩
  · rintro ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩
    obtain ⟨u', hau'⟩ := (hH.2 x t ht).1 a c hac
    have he := curry_unique_l M hE hI B C a u u' hau ⟨H, hH, hau'⟩
    exact ((hH.2 x t ht).2 v).mpr ⟨a, c, u', p, s, k, hac, hc, hcp, hau', he ▸ hk, hv⟩

theorem curry_union_l (hE : Extensional M) (hI : Mem_ind_d M) {B C A H}
    (hA : ∀ J, M.mem J A → Curry_graph_d M B C J) (hH : M.IsUnionOf H A) : Curry_graph_d M B C H := by
  constructor
  · intro v hv
    obtain ⟨J, hJ, hv⟩ := (hH v).mp hv
    exact (hA J hJ).1 v hv
  · intro x t ht
    obtain ⟨J, hJ, ht⟩ := (entry_union_l M hH x t).mp ht
    have hj := hA J hJ
    refine ⟨fun a c hac => ?_, fun v => ?_⟩
    · obtain ⟨u, hu⟩ := (hj.2 x t ht).1 a c hac
      exact ⟨u, (entry_union_l M hH a u).mpr ⟨J, hJ, hu⟩⟩
    · constructor
      · intro hv
        obtain ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩ := ((hj.2 x t ht).2 v).mp hv
        exact ⟨a, c, u, p, s, k, hac, hc, hcp, (entry_union_l M hH a u).mpr ⟨J, hJ, hau⟩, hk, hv⟩
      · rintro ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩
        obtain ⟨F, hF, hau⟩ := (entry_union_l M hH a u).mp hau
        obtain ⟨u', hau'⟩ := (hj.2 x t ht).1 a c hac
        have he := curry_unique_l M hE hI B C a u u' ⟨F, hA F hF, hau⟩ ⟨J, hj, hau'⟩
        exact ((hj.2 x t ht).2 v).mpr ⟨a, c, u', p, s, k, hac, hc, hcp, hau', he ▸ hk, hv⟩

theorem curry_adjoin_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) (hU : ∀ F, ∃ S, M.IsUnionOf S F)
    {B C H x t} (hH : Curry_graph_d M B C H) (ht : Curry_step_d M B C H x t) : Curry_d M B C x t := by
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
    · exact curry_unique_l M hE hI B C y s a ⟨H, hH, hs⟩ ⟨H, hH, ha⟩
    · exact hE.eq_of_same_members _ _ (fun v => (ht.2 v).trans ((hH.2 y a ha).2 v).symm)
  have step {y s} (hs : Curry_step_d M B C H y s) : Curry_step_d M B C J y s := by
    refine ⟨fun a c hac => ?_, fun v => ?_⟩
    · obtain ⟨u, hu⟩ := hs.1 a c hac
      exact ⟨u, (hj a u).mpr (Or.inl hu)⟩
    · constructor
      · intro hv
        obtain ⟨a, c, u, p, b, k, hac, hc, hcp, hau, hk, hv⟩ := (hs.2 v).mp hv
        exact ⟨a, c, u, p, b, k, hac, hc, hcp, (hj a u).mpr (Or.inl hau), hk, hv⟩
      · rintro ⟨a, c, u, p, b, k, hac, hc, hcp, hau, hk, hv⟩
        obtain ⟨u', hau'⟩ := hs.1 a c hac
        exact (hs.2 v).mpr ⟨a, c, u', p, b, k, hac, hc, hcp, hau', agree hau hau' ▸ hk, hv⟩
  refine ⟨J, ⟨?_, ?_⟩, (hj x t).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro v hv
    rcases (hJ v).mp hv with hv | rfl
    · exact hH.1 v hv
    · exact ⟨x, t, hp⟩
  · intro y s hs
    rcases (hj y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact step (hH.2 y s hs)
    · exact step ht

theorem curry_entry_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {B C x t} (h : Curry_d M B C x t) (k p) :
    Entry_d M k p t ↔ ∃ a c u s, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧
      Curry_d M B C a u ∧ Nkpair_d M B u s k := by
  constructor
  · rintro ⟨v, hv, hvt⟩
    obtain ⟨a, c, u, p', s, k', hac, hc, hcp, hau, hk, hv'⟩ := (curry_mem_l M hE hI h v).mp hvt
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨a, c, u, s, hac, hc, hcp, hau, hk⟩
  · rintro ⟨a, c, u, s, hac, hc, hcp, hau, hk⟩
    obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total k p
    exact ⟨v, hv, (curry_mem_l M hE hI h v).mpr ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩⟩

end YesMetaZFC.Model.Forcing.Internal
