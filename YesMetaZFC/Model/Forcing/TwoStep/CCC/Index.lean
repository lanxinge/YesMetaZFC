import YesMetaZFC.Model.Forcing.TwoStep.CCC.IndexSyntax
import YesMetaZFC.Model.Forcing.Internal.Functions.Generic

/-! # 泛型索引及第二坐标图的实际名称构造 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S D : M.Domain}

theorem step_index_l (hZF : M.Models ZF) (h : Two_step_d M B R z b A T W C S)
    (hd : M.MemberSubset D C) : ∃ t g, Name_d M B t ∧ Name_d M B g ∧ Step_index_d M B b D t g := by
  obtain ⟨X, hX, hx⟩ := check_image_l hZF h.base D
  let ρ : Env M 2 := (⟨fun _ => b, fun _ => b⟩ : Env M 1).push D
  let φ : BinarySchema 2 := { body := step_idx_entry_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ a p : φ.denote ρ a p ↔ ∃ x s, M.mem x D ∧ KPair_d M x p s ∧ Check_d M b x a :=
    step_idx_entry_sat_l hZF.1 _ _ _ _ _
  obtain ⟨t, ht, _, he⟩ := name_comp_l M hZF φ ρ B X hx
  have htE a p : Entry_d M a p t ↔ ∃ x s, M.mem x D ∧ KPair_d M x p s ∧ Check_d M b x a := by
    refine (he a p).trans ⟨fun hh => (hφ a p).mp hh.2.2, ?_⟩
    rintro ⟨x, s, hxd, hxp, hxa⟩
    exact ⟨(hX a).mpr ⟨x, hxd, hxa⟩, ((two_step_mem_l h hxp).mp (hd x hxd)).2.1.1,
      (hφ a p).mpr ⟨x, s, hxd, hxp, hxa⟩⟩
  let η : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push b
  let ψ : BinarySchema 2 := {
    body := .existsE (.existsE (.existsE (.conj (kpair_m (.bound 4) (.bound 2) (.bound 1))
      (.conj (check_m (.bound 5) (.bound 4) .newest) (nkpair_m (.bound 6) .newest (.bound 1) (.bound 3)))))) }
  have hψ x a : ψ.denote η x a ↔ ∃ p s c, KPair_d M x p s ∧ Check_d M b x c ∧ Nkpair_d M B c s a := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, check_sat_l M hZF.1, nkpair_sat_l M hZF.1]
    rfl
  obtain ⟨Y, hY⟩ := ZF.exists_functionalImageOn hZF ψ η D (fun x hxD => by
    obtain ⟨p, s, hxp, _⟩ := (h.conditions x).mp (hd x hxD)
    obtain ⟨c, hc, _, _⟩ := zf_check_l M hZF h.base x
    obtain ⟨a, ha⟩ := nkpair_l M hZF B c s
    exact ⟨a, (hψ x a).mpr ⟨p, s, c, hxp, hc, ha⟩⟩) (fun x _ a a' ha ha' => by
    obtain ⟨p, s, c, hxp, hc, ha⟩ := (hψ x a).mp ha
    obtain ⟨p', s', c', hxp', hc', ha'⟩ := (hψ x a').mp ha'
    obtain ⟨_, he⟩ := kpair_injective_l M hxp hxp'
    subst s'
    have he := check_unique_l M hZF.1 (check_ind_l M hZF) b x c c' hc hc'
    subst c'
    exact nkpair_unique_l M hZF.1 ha ha')
  have hn a (ha : M.mem a Y) : Name_d M B a := by
    obtain ⟨x, hxD, hxa⟩ := (hY a).mp ha
    obtain ⟨p, s, c, hxp, hc, ha⟩ := (hψ x a).mp hxa
    obtain ⟨v, hv, hvN, _⟩ := zf_check_l M hZF h.base x
    have he := check_unique_l M hZF.1 (check_ind_l M hZF) b x v c hv hc
    exact nkpair_name_l M hZF (he ▸ hvN) ⟨W, ((two_step_mem_l h hxp).mp (hd x hxD)).1, h.closed⟩ ha
  let ν := η.push D
  let χ : BinarySchema 3 := { body := step_graph_entry_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hχ a p : χ.denote ν a p ↔ ∃ x s c, M.mem x D ∧ KPair_d M x p s ∧ Check_d M b x c ∧ Nkpair_d M B c s a :=
    step_graph_entry_sat_l hZF.1 _ _ _ _ _ _
  obtain ⟨g, hg, _, hgE⟩ := name_comp_l M hZF χ ν B Y hn
  refine ⟨t, g, ht, hg, htE, fun a p => (hgE a p).trans ⟨fun hh => (hχ a p).mp hh.2.2, ?_⟩⟩
  rintro ⟨x, s, c, hxD, hxp, hc, ha⟩
  exact ⟨(hY a).mpr ⟨x, hxD, (hψ x a).mpr ⟨p, s, c, hxp, hc, ha⟩⟩,
    ((two_step_mem_l h hxp).mp (hd x hxD)).2.1.1, (hχ a p).mpr ⟨x, s, c, hxD, hxp, hc, ha⟩⟩

end YesMetaZFC.Model.Forcing.Internal
