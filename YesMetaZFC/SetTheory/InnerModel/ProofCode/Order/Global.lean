import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Names

/-! # 所有规范码名的模型内部良序 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem pn_irrefl_l (hM : M.Models KPi) {v : M.Domain} (hv : Pn_valid_d v) : ¬ Pn_lt_d v v := by
  obtain ⟨a, h, c, hv⟩ := hv
  intro he
  rcases (pn_lt_iff_l hv.1 hv.1).mp he with he | ⟨_, he | ⟨_, he⟩⟩
  · exact KP.mem_irrefl_d (KPi.models_iff_l.mp hM).1 a he
  · exact KP.mem_irrefl_d (KPi.models_iff_l.mp hM).1 h he
  · exact po_irrefl_l hM hv.2.2.2.1.valid_l he

theorem pn_compare_l (hM : M.Models KPi) {v w : M.Domain} (hv : Pn_valid_d v) (hw : Pn_valid_d w) :
    v = w ∨ Pn_lt_d v w ∨ Pn_lt_d w v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, h, c, hv⟩ := hv
  obtain ⟨b, m, d, hw⟩ := hw
  have cmp x y (hx : M.IsOrdinal x) (hy : M.IsOrdinal y) : x = y ∨ M.mem x y ∨ M.mem y x :=
    (Structure.IsOrdinal.trichotomy hKP.1 hx hy (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP x y)).imp_left (hKP.1.eq_of_same_members _ _)
  rcases cmp a b hv.2.1 hw.2.1 with he | he | he
  · subst b
    rcases cmp h m (KPi.n0_ordinal_l hM hv.2.2.1) (KPi.n0_ordinal_l hM hw.2.2.1) with he | he | he
    · subst m
      rcases po_compare_l hM hv.2.2.2.1.valid_l hw.2.2.2.1.valid_l with he | he | he
      · subst d; exact Or.inl (pn_triple_unique_l hKP.1 hv.1 hw.1)
      · exact Or.inr (Or.inl ((pn_lt_iff_l hv.1 hw.1).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, he⟩⟩)))
      · exact Or.inr (Or.inr ((pn_lt_iff_l hw.1 hv.1).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, he⟩⟩)))
    · exact Or.inr (Or.inl ((pn_lt_iff_l hv.1 hw.1).mpr (Or.inr ⟨rfl, Or.inl he⟩)))
    · exact Or.inr (Or.inr ((pn_lt_iff_l hw.1 hv.1).mpr (Or.inr ⟨rfl, Or.inl he⟩)))
  · exact Or.inr (Or.inl ((pn_lt_iff_l hv.1 hw.1).mpr (Or.inl he)))
  · exact Or.inr (Or.inr ((pn_lt_iff_l hw.1 hv.1).mpr (Or.inl he)))

theorem pn_trans_l (hM : M.Models KPi) {u v w : M.Domain} (hu : Pn_valid_d u) (hv : Pn_valid_d v) (hw : Pn_valid_d w)
    (h : Pn_lt_d u v) (g : Pn_lt_d v w) : Pn_lt_d u w := by
  obtain ⟨a, i, c, hu⟩ := hu
  obtain ⟨b, j, d, hv⟩ := hv
  obtain ⟨e, k, f, hw⟩ := hw
  apply (pn_lt_iff_l hu.1 hw.1).mpr
  rcases (pn_lt_iff_l hu.1 hv.1).mp h with h | ⟨h, h' | ⟨h', h''⟩⟩ <;>
    rcases (pn_lt_iff_l hv.1 hw.1).mp g with g | ⟨g, g' | ⟨g', g''⟩⟩
  · exact Or.inl (hw.2.1.transitive b g a h)
  · exact Or.inl (g ▸ h)
  · exact Or.inl (g ▸ h)
  · exact Or.inl (h.symm ▸ g)
  · exact Or.inr ⟨h.trans g, Or.inl (hw.2.2.1.1 j g' i h')⟩
  · exact Or.inr ⟨h.trans g, Or.inl (g' ▸ h')⟩
  · exact Or.inl (h.symm ▸ g)
  · exact Or.inr ⟨h.trans g, Or.inl (h'.symm ▸ g')⟩
  · exact Or.inr ⟨h.trans g, Or.inr ⟨h'.trans g',
      po_trans_l hM hu.2.2.2.1.valid_l hv.2.2.2.1.valid_l hw.2.2.2.1.valid_l h'' g''⟩⟩

/-- 任意模型内部的非空合法码名集合都有最小元。 -/
theorem pn_min_l (hM : M.Models KPi) {X : M.Domain} (hv : ∀ v, M.mem v X → Pn_valid_d v)
    (hn : ∃ v, M.mem v X) : Po_min_d Pn_lt_d X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨T, ht, hXT⟩ := KPi.transitive_cover_l hM X
  have xt := ht X hXT
  let ρ := (jh_env_l T).push T
  have total (i : Fin 3) v (hvX : M.mem v X) : ∃ a, Pn_proj_d i T v a := by
    obtain ⟨a, h, c, hv⟩ := hv v hvX
    exact ⟨_, pn_fields_l ht (xt v hvX) hv.1 i⟩
  have select (i : Fin 3) (V : M.Domain) (vx : M.MemberSubset V X) {R : M.Domain → M.Domain → Prop}
      (hl : ∀ Y, (∀ a, M.mem a Y ↔ ∃ v, M.mem v V ∧ Pn_proj_d i T v a) → Po_min_d R Y) :
      ∃ a U, (∀ v, M.mem v U ↔ M.mem v V ∧ Pn_proj_d i T v a) ∧ (∃ v, M.mem v U) ∧
        ∀ v, M.mem v V → ∀ b, Pn_proj_d i T v b → a = b ∨ R a b := by
    have sat v a := pn_proj_sat_l hKP.1 i ρ v a
    obtain ⟨a, U, hU, hn, hm⟩ := po_minfiber_l hKP (pn_proj_s i) ρ V
      (fun v hv => (total i v (vx v hv)).imp (fun a ha => (sat v a).mpr ha))
      (fun v _ a b ha hb => pn_proj_unique_l i ((sat v a).mp ha) ((sat v b).mp hb))
      (fun Y hY => hl Y (fun a => (hY a).trans (exists_congr fun v => and_congr_right fun _ => sat v a)))
    exact ⟨a, U, fun v => (hU v).trans (and_congr_right fun _ => sat v a), hn,
      fun v hv b hb => hm v hv b ((sat v b).mpr hb)⟩
  have ordinal (i : Fin 3) (hi : i = 0 ∨ i = 1) v (hvX : M.mem v X) a (ha : Pn_proj_d i T v a) : M.IsOrdinal a := by
    obtain ⟨b, m, c, hv⟩ := hv v hvX
    rw [pn_proj_value_l i hv.1 ha]
    rcases hi with rfl | rfl
    · exact hv.2.1
    · exact KPi.n0_ordinal_l hM hv.2.2.1
  have ord_min (i : Fin 3) (hi : i = 0 ∨ i = 1) V (vx : M.MemberSubset V X) (hn : ∃ v, M.mem v V) Y
      (hY : ∀ a, M.mem a Y ↔ ∃ v, M.mem v V ∧ Pn_proj_d i T v a) : Po_min_d M.mem Y := by
    apply po_ordinal_min_l hKP
    · intro a ha; obtain ⟨v, hv, ha⟩ := (hY a).mp ha; exact ordinal i hi v (vx v hv) a ha
    · obtain ⟨v, hv⟩ := hn; obtain ⟨a, ha⟩ := total i v (vx v hv); exact ⟨a, (hY a).mpr ⟨v, hv, ha⟩⟩
  -- 先固定最小序数界，再固定最小内部高度，最后应用该高度的树良序。
  obtain ⟨a, A, hA, hAn, ha⟩ := select 0 X (fun _ h => h) (ord_min 0 (Or.inl rfl) X (fun _ h => h) hn)
  have ax v hv := ((hA v).mp hv).1
  obtain ⟨h, B, hB, hBn, hh⟩ := select 1 A ax (ord_min 1 (Or.inr rfl) A ax hAn)
  have ba v hv := ((hB v).mp hv).1
  have bx v hv := ax v (ba v hv)
  have name v (hvB : M.mem v B) : ∃ c, Pn_name_d v a h c := by
    obtain ⟨b, m, c, hn⟩ := hv v (bx v hvB)
    have he : a = b := pn_proj_value_l 0 hn.1 ((hA v).mp (ba v hvB)).2; subst b
    have he : h = m := pn_proj_value_l 1 hn.1 ((hB v).mp hvB).2; subst m
    exact ⟨c, hn⟩
  obtain ⟨c, C, hC, ⟨v, hvC⟩, hc⟩ := select 2 B bx (by
    intro Y hY
    obtain ⟨v, hvB⟩ := hBn
    obtain ⟨c, hn⟩ := name v hvB
    apply po_height_min_l hM hn.2.2.1
    · intro d hd
      obtain ⟨w, hwB, hd⟩ := (hY d).mp hd
      obtain ⟨e, he⟩ := name w hwB
      have heq : d = e := pn_proj_value_l 2 he.1 hd
      exact heq.symm ▸ he.2.2.2.1
    · exact ⟨c, (hY c).mpr ⟨v, hvB, pn_fields_l ht (xt v (bx v hvB)) hn.1 2⟩⟩)
  have hvB := ((hC v).mp hvC).1
  obtain ⟨c', hnv⟩ := name v hvB
  have he : c = c' := pn_proj_value_l 2 hnv.1 ((hC v).mp hvC).2; subst c'
  refine ⟨v, bx v hvB, fun w hwX => ?_⟩
  obtain ⟨b, m, d, hnw⟩ := hv w hwX
  have fields := pn_fields_l ht (xt w hwX) hnw.1
  have less (h : Pn_key_d a h c b m d) : Pn_lt_d v w := (pn_lt_iff_l hnv.1 hnw.1).mpr h
  rcases ha w hwX b (fields 0) with he | he
  · have hwA : M.mem w A := (hA w).mpr ⟨hwX, he.symm ▸ fields 0⟩
    rcases hh w hwA m (fields 1) with hf | hf
    · have hwB : M.mem w B := (hB w).mpr ⟨hwA, hf.symm ▸ fields 1⟩
      rcases hc w hwB d (fields 2) with hg | hg
      · subst b; subst m; subst d; exact Or.inl (pn_triple_unique_l hKP.1 hnv.1 hnw.1)
      · exact Or.inr (less (Or.inr ⟨he, Or.inr ⟨hf, hg⟩⟩))
    · exact Or.inr (less (Or.inr ⟨he, Or.inl hf⟩))
  · exact Or.inr (less (Or.inl he))

end YesMetaZFC.SetTheory.InnerModel
