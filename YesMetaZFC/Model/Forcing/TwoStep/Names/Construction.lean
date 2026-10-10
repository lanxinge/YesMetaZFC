import YesMetaZFC.Model.Forcing.TwoStep.Names.Recursion
import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction
import YesMetaZFC.Model.Forcing.TwoStep.Order

/-! # 原模型内两步名称转换的实际存在性

按源条目收集递归图，以规范名称配对替换有效条目并加入新根。原 ZF 已足够；
第一阶段名称性由实际二步条件的坐标规格及内部条目归纳推出。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

private def Curry_wit_d (B H v w : M.Domain) : Prop := ∃ a c u p s k,
  KPair_d M v a c ∧ KPair_d M c p s ∧ Entry_d M a u H ∧ Nkpair_d M B u s k ∧ KPair_d M w k p

private def curry_wit_m {n} (B H v w : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m v.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4))
      (.conj (kpair_m (.bound 4) (.bound 2) (.bound 1))
        (.conj (entry_m (.bound 5) (.bound 3) H.weaken.weaken.weaken.weaken.weaken.weaken)
          (.conj (nkpair_m B.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
            (kpair_m w.weaken.weaken.weaken.weaken.weaken.weaken .newest (.bound 2)))))))))))
derive_free_closed curry_wit_m

private theorem curry_wit_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B H v w : Term n) :
    Formula.satisfies ρ (curry_wit_m B H v w) ↔ Curry_wit_d M (B.eval ρ) (H.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [curry_wit_m, Curry_wit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, entry_sat_l M hE, nkpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

private theorem curry_image_l (hZF : M.Models ZF) (B C H x : M.Domain)
    (hd : ∀ a c, Entry_d M a c x → ∃ u, Entry_d M a u H)
    (hf : ∀ a u v, Entry_d M a u H → Entry_d M a v H → u = v) :
    ∃ t, ∀ v, M.mem v t ↔ ∃ a c u p s k, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧
      Entry_d M a u H ∧ Nkpair_d M B u s k ∧ KPair_d M v k p := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => C, fun _ => C⟩
  let φ : UnarySchema 1 := {
    body := .existsE (.existsE (.existsE (.existsE
      (.conj (kpair_m (.bound 4) (.bound 3) (.bound 2))
        (.conj (.mem (.bound 2) (.bound 5)) (kpair_m (.bound 2) (.bound 1) .newest)))))) }
  have hφ v : φ.denote ρ v ↔ ∃ a c p s, KPair_d M v a c ∧ M.mem c C ∧ KPair_d M c p s := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, kpair_sat_l M hZF.1]
    rfl
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ x
  let η : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push H
  let ψ : BinarySchema 2 := { body := curry_wit_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ v w : ψ.denote η v w ↔ Curry_wit_d M B H v w := curry_wit_sat_l M hZF.1 ((η.push v).push w) _ _ _ _
  obtain ⟨t, ht⟩ := ZF.exists_functionalImageOn hZF ψ η D (fun v hv => by
    obtain ⟨hvx, hvc⟩ := (hD v).mp hv
    obtain ⟨a, c, p, s, hac, _, hcp⟩ := (hφ v).mp hvc
    obtain ⟨u, hau⟩ := hd a c ⟨v, hac, hvx⟩
    obtain ⟨k, hk⟩ := nkpair_l M hZF B u s
    obtain ⟨w, hw⟩ := I.total k p
    exact ⟨w, (hψ v w).mpr ⟨a, c, u, p, s, k, hac, hcp, hau, hk, hw⟩⟩) (by
      intro v _ w w' hw hw'
      obtain ⟨a, c, u, p, s, k, hac, hcp, hau, hk, hw⟩ := (hψ v w).mp hw
      obtain ⟨a', c', u', p', s', k', hac', hcp', hau', hk', hw'⟩ := (hψ v w').mp hw'
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hac hac'
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hcp hcp'
      have he := hf _ _ _ hau hau'
      subst u'
      have he := nkpair_unique_l M hZF.1 hk hk'
      subst k'
      exact kpair_unique_l M hZF.1 hw hw')
  refine ⟨t, fun v => (ht v).trans ?_⟩
  constructor
  · rintro ⟨w, hwD, hv⟩
    obtain ⟨hwx, hwc⟩ := (hD w).mp hwD
    obtain ⟨a, c, u, p, s, k, hac, hcp, hau, hk, hv⟩ := (hψ w v).mp hv
    obtain ⟨a', c', _, _, hac', hc', _⟩ := (hφ w).mp hwc
    have hc : M.mem c C := (kpair_injective_l M hac hac').2.symm ▸ hc'
    exact ⟨a, c, u, p, s, k, ⟨w, hac, hwx⟩, hc, hcp, hau, hk, hv⟩
  · rintro ⟨a, c, u, p, s, k, ⟨w, hac, hwx⟩, hc, hcp, hau, hk, hv⟩
    exact ⟨w, (hD w).mpr ⟨hwx, (hφ w).mpr ⟨a, c, p, s, hac, hc, hcp⟩⟩,
      (hψ w v).mpr ⟨a, c, u, p, s, k, hac, hcp, hau, hk, hv⟩⟩

private theorem curry_collect_l (hZF : M.Models ZF) (B C x : M.Domain)
    (h : ∀ a c, Entry_d M a c x → ∃ t, Curry_d M B C a t) :
    ∃ D, (∀ H, M.mem H D → Curry_graph_d M B C H) ∧
      ∀ a c, Entry_d M a c x → ∃ H t, M.mem H D ∧ Entry_d M a t H := by
  obtain ⟨A, hA⟩ := entry_domain_l M hZF x
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push C
  let φ : BinarySchema 2 := {
    body := .conj (curry_graph_m (.bound 3) (.bound 2) .newest) (.existsE (entry_m (.bound 2) .newest (.bound 1))) }
  have hφ a H : φ.denote ρ a H ↔ Curry_graph_d M B C H ∧ ∃ t, Entry_d M a t H := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
      curry_graph_sat_l M hZF.1, entry_sat_l M hZF.1]
    rfl
  obtain ⟨D₀, hd⟩ := ZF.collection_exists_d hZF φ ρ A (fun a ha => by
    obtain ⟨c, hac⟩ := (hA a).mp ha
    obtain ⟨t, H, hH, ht⟩ := h a c hac
    exact ⟨H, (hφ a H).mpr ⟨hH, t, ht⟩⟩)
  let ψ : UnarySchema 2 := { body := curry_graph_m (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF ψ ρ D₀
  have hD H : M.mem H D ↔ M.mem H D₀ ∧ Curry_graph_d M B C H :=
    (hD' H).trans (and_congr_right fun _ => curry_graph_sat_l M hZF.1 (ρ.push H) _ _ _)
  refine ⟨D, fun H hH => ((hD H).mp hH).2, fun a c hac => ?_⟩
  obtain ⟨H, hH, hφH⟩ := hd a ((hA a).mpr ⟨c, hac⟩)
  obtain ⟨hH', t, ht⟩ := (hφ a H).mp hφH
  exact ⟨H, t, (hD H).mpr ⟨hH, hH'⟩, ht⟩

theorem curry_exists_l (hZF : M.Models ZF) (B C x : M.Domain) : ∃ t, Curry_d M B C x t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push C
  let φ : UnarySchema 2 := { body := .existsE (curry_m (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hφ x : φ.denote ρ x ↔ ∃ t, Curry_d M B C x t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, curry_sat_l M hZF.1]
    rfl
  apply (hφ x).mp
  apply entry_ind_l hI φ ρ
  intro x ih
  apply (hφ x).mpr
  obtain ⟨D, hD, hd⟩ := curry_collect_l M hZF B C x (fun a c hac => (hφ a).mp (ih a c hac))
  obtain ⟨H, hH⟩ := KP.exists_union (ZF.modelsKP hZF) D
  have hg := curry_union_l M hZF.1 hI hD hH
  have ht a c (hac : Entry_d M a c x) : ∃ u, Entry_d M a u H := by
    obtain ⟨J, u, hJ, hau⟩ := hd a c hac
    exact ⟨u, (entry_union_l M hH a u).mpr ⟨J, hJ, hau⟩⟩
  obtain ⟨t, hImage⟩ := curry_image_l M hZF B C H x ht
    (fun a u v hu hv => curry_unique_l M hZF.1 hI B C a u v ⟨H, hg, hu⟩ ⟨H, hg, hv⟩)
  exact ⟨t, curry_adjoin_l M hZF.1 hI (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hg ⟨ht, hImage⟩⟩

theorem curry_name_l (hZF : M.Models ZF) {B C : M.Domain}
    (hC : ∀ c p s, M.mem c C → KPair_d M c p s → M.mem p B ∧ Name_d M B s)
    {x t} (h : Curry_d M B C x t) : Name_d M B t := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push C
  let φ : UnarySchema 2 := {
    body := .forallE (.imp (curry_m (.bound 3) (.bound 2) (.bound 1) .newest) (name_m (.bound 3) .newest)) }
  have hφ x : φ.denote ρ x ↔ ∀ t, Curry_d M B C x t → Name_d M B t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      curry_sat_l M hZF.1, name_sat_l M hZF.1]
    rfl
  have hall := entry_ind_l (check_ind_l M hZF) φ ρ (fun x ih => (hφ x).mpr (by
    intro t ht
    apply (name_unfold_l M (name_ops_l M hZF) B t).mpr
    intro v hv
    obtain ⟨a, c, u, p, s, k, hac, hc, hcp, hau, hk, hv⟩ := (curry_mem_l M hZF.1 (check_ind_l M hZF) ht v).mp hv
    have hn := (hφ a).mp (ih a c hac) u hau
    exact ⟨k, p, hv, (hC c p s hc hcp).1, nkpair_name_l M hZF hn (hC c p s hc hcp).2 hk⟩))
  exact (hφ x).mp (hall x) t h

/-- 实际二步条件规格自动提供转换后的第一阶段名称及唯一性。 -/
theorem two_step_curry_l (hZF : M.Models ZF) {B R z b A T W C S}
    (h : Two_step_d M B R z b A T W C S) (x : M.Domain) :
    ∃ t, Curry_d M B C x t ∧ Name_d M B t ∧ ∀ s, Curry_d M B C x s → s = t := by
  obtain ⟨t, ht⟩ := curry_exists_l M hZF B C x
  refine ⟨t, ht, curry_name_l M hZF ?_ ht,
    fun s hs => curry_unique_l M hZF.1 (check_ind_l M hZF) B C x s t hs ht⟩
  intro c p s hc hcp
  obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
  exact ⟨hp.1, W, hs, h.closed⟩

end YesMetaZFC.Model.Forcing.Internal
