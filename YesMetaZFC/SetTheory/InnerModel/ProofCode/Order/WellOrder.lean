import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.ShapeMinimum

/-! # 固定内部高度的字典良序

对最小构造符的纤维，依次最小化三个子码坐标。每个坐标像都是实际集合，
且语法高度下降到内部前驱；因此证明也适用于非标准有限高度。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

private theorem node_min_l (hM : M.Models KPi) {T X p : M.Domain} {k}
    (ht : M.TransitiveSet T) (hx : M.MemberSubset X T)
    (hs : ∀ c, M.mem c X → ∃ a b d, Pc_node_d T k c a b d)
    (hp : ∀ c, M.mem c X → ∀ i a, Po_arg_d i T c a → Ps_height_d p a)
    (ih : ∀ Y, (∀ a, M.mem a Y → Ps_height_d p a) → (∃ a, M.mem a Y) → Po_min_d Po_lt_d Y)
    (hn : ∃ c, M.mem c X) : Po_min_d Po_lt_d X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := (jh_env_l T).push T
  have total i c (hc : M.mem c X) : ∃ a, Po_arg_d i T c a := by
    obtain ⟨a, b, d, hc'⟩ := hs c hc
    exact ⟨_, (po_node_fields_l ht (hx c hc) hc').2 i⟩
  have select (i : Fin 3) (V : M.Domain) (hv : M.MemberSubset V X) (hn : ∃ c, M.mem c V) :
      ∃ a U, (∀ c, M.mem c U ↔ M.mem c V ∧ Po_arg_d i T c a) ∧ (∃ c, M.mem c U) ∧
        ∀ c, M.mem c V → ∀ b, Po_arg_d i T c b → a = b ∨ Po_lt_d a b := by
    have sat c a := po_arg_sat_l hKP.1 i ρ c a
    obtain ⟨a, U, hU, hn, hm⟩ := po_minfiber_l hKP (po_arg_s i) ρ V
      (fun c hc => (total i c (hv c hc)).imp (fun a ha => (sat c a).mpr ha))
      (fun c _ a b ha hb => po_arg_unique_l i ((sat c a).mp ha) ((sat c b).mp hb)) (by
        intro Y hY
        apply ih Y
        · intro a ha
          obtain ⟨c, hc, ha⟩ := (hY a).mp ha
          exact hp c (hv c hc) i a ((sat c a).mp ha)
        · obtain ⟨c, hc⟩ := hn
          obtain ⟨a, ha⟩ := total i c (hv c hc)
          exact ⟨a, (hY a).mpr ⟨c, hc, (sat c a).mpr ha⟩⟩)
    exact ⟨a, U, fun c => (hU c).trans (and_congr_right fun _ => sat c a), hn,
      fun c hc b hb => hm c hc b ((sat c b).mpr hb)⟩
  -- X ⊇ A ⊇ B ⊇ D：逐坐标取最小值，只保留取得该值的非空纤维。
  obtain ⟨a, A, hA, hAn, ha⟩ := select 0 X (fun _ h => h) hn
  have ax c hc := ((hA c).mp hc).1
  obtain ⟨b, B, hB, hBn, hb⟩ := select 1 A ax hAn
  have ba c hc := ((hB c).mp hc).1
  obtain ⟨d, D, hD, ⟨c, hc⟩, hd⟩ := select 2 B (fun c hc => ax c (ba c hc)) hBn
  have cb := ((hD c).mp hc).1
  have ca := ba c cb
  have cx := ax c ca
  obtain ⟨a', b', d', hsc⟩ := hs c cx
  have fields := (po_node_fields_l ht (hx c cx) hsc).2
  have he : a' = a := po_arg_unique_l 0 (fields 0) ((hA c).mp ca).2; subst a'
  have he : b' = b := po_arg_unique_l 1 (fields 1) ((hB c).mp cb).2; subst b'
  have he : d' = d := po_arg_unique_l 2 (fields 2) ((hD c).mp hc).2; subst d'
  refine ⟨c, cx, fun e he => ?_⟩
  obtain ⟨x, y, z, he'⟩ := hs e he
  have ef := (po_node_fields_l ht (hx e he) he').2
  have less (h : Po_lex_d Po_lt_d a b d x y z) : Po_lt_d c e := (po_node_iff_l hM hsc he').mpr (Or.inr ⟨rfl, h⟩)
  rcases ha e he x (ef 0) with h | h
  · have ea : M.mem e A := (hA e).mpr ⟨he, h.symm ▸ ef 0⟩
    rcases hb e ea y (ef 1) with g | g
    · have eb : M.mem e B := (hB e).mpr ⟨ea, g.symm ▸ ef 1⟩
      rcases hd e eb z (ef 2) with f | f
      · subst x; subst y; subst z; exact Or.inl (pc_node_unique_l hKP.1 hsc he')
      · exact Or.inr (less (Or.inr ⟨h, Or.inr ⟨g, f⟩⟩))
    · exact Or.inr (less (Or.inr ⟨h, Or.inl g⟩))
  · exact Or.inr (less (Or.inl h))

theorem po_height_min_l (hM : M.Models KPi) {h X : M.Domain} (hh : KP.N0_d h)
    (hx : ∀ c, M.mem c X → Ps_height_d h c) (hn : ∃ c, M.mem c X) : Po_min_d Po_lt_d X := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let φ : UnarySchema 0 := { body := .imp (KP.n0_m .newest) (.forallE
    (.imp (Formula.forallMem .newest (ps_height_m (.bound 2) .newest))
      (.imp (Formula.existsMem .newest .truth)
        (Formula.existsMem .newest (Formula.forallMem (.bound 1)
          (.disj (Formula.extensionalEq (.bound 1) .newest) (po_lt_m (.bound 1) .newest))))))) }
  have hφ n : φ.denote (jh_env_l h) n ↔ KP.N0_d n → ∀ X, (∀ c, M.mem c X → Ps_height_d n c) →
      (∃ c, M.mem c X) → Po_min_d Po_lt_d X := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.n0_sat_l hKP.1,
      Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, ps_height_sat_l hKP,
      Formula.satisfies_existsMem_iff, Formula.satisfies_truth_iff, and_true,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1, po_lt_formula_l hKP]; rfl
  apply (hφ h).mp (hi φ (jh_env_l h) ?_ h) hh X hx hn
  intro h ih
  apply (hφ h).mpr
  intro hh X hx hn
  obtain ⟨T, U, ht, xt, ux, hun, hs, hm⟩ := po_top_min_l hM (fun c hc => (hx c hc).valid_l) hn
  have inner : Po_min_d Po_lt_d U := by
    rcases hs with hl | ⟨k, hk⟩
    · exact po_leaf_min_l hM hl hun
    · -- 内部自然数非零即为后继；所有子码的高度可统一降到这个前驱。
      rcases hh.2.1 with he | ⟨p, hph, hp⟩
      · obtain ⟨c, hc⟩ := hun
        obtain ⟨a, b, d, hs⟩ := hk c hc
        rcases ps_height_unfold_l hh (hx c (ux c hc)) with ⟨V, x, hv, _⟩ | ⟨V, l, x, y, z, _, ⟨m, hmh, _⟩, _⟩
        · exact (pc_leaf_node_false_l hKP hv hs).elim
        · exact (he m hmh).elim
      · apply node_min_l hM ht (fun c hc => xt c (ux c hc)) hk ?_ ((hφ p).mp (ih p hph) (hh.mem_l hph)) hun
        intro c hc i a ha
        obtain ⟨x, y, z, hn⟩ := hk c hc
        have hc' := ps_height_children_l hKP hh hp (hx c (ux c hc)) hn
        have fields := (po_node_fields_l ht (xt c (ux c hc)) hn).2
        have he := po_arg_unique_l i ha (fields i)
        rw [he]
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl
        · exact hc'.1
        · exact hc'.2.1
        · exact hc'.2.2
  obtain ⟨c, hc, hl⟩ := inner
  exact ⟨c, ux c hc, fun d hd => (hm c hc d hd).elim (hl d) Or.inr⟩

end YesMetaZFC.SetTheory.InnerModel
