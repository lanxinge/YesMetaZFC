import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Equations

/-! # 合法构造码上的严格线序

三条序律分别对模型内部语法高度作成员归纳；不要求模型外部良基。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def ps_valid_m {n} (c : Term n) : Formula 1 n := .existsE (ps_rank_m .newest c.weaken)
derive_free_closed ps_valid_m
theorem ps_valid_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (c : Term n) :
    Formula.satisfies ρ (ps_valid_m c) ↔ Ps_valid_d (c.eval ρ) := by
  simp only [ps_valid_m, Formula.satisfies_exists_iff, ps_rank_formula_l hKP,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken, Ps_valid_d]

theorem ps_rank_unfold_l {n c : M.Domain} (hc : Ps_rank_d n c) :
    (∃ T a, Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
      ∃ T k a b d, Pc_node_d T k c a b d ∧
        (∃ m, M.mem m n ∧ Ps_rank_d m a) ∧ (∃ m, M.mem m n ∧ Ps_rank_d m b) ∧
          (∃ m, M.mem m n ∧ Ps_rank_d m d) := by
  obtain ⟨T, F, hf, hc⟩ := hc
  have child {d} (h : Ps_read_d F n d) : ∃ m, M.mem m n ∧ Ps_rank_d m d :=
    h.imp (fun m hm => ⟨hm.1, T, F, hf, hm.2⟩)
  rcases (hf.at_l hc).2.2.2 with ⟨a, _, h, ha⟩ | ⟨k, a, _, b, _, d, _, h, ha, hb, hd⟩
  · exact Or.inl ⟨T, a, h, ha⟩
  · exact Or.inr ⟨T, k, a, b, d, h, child ha, child hb, child hd⟩

theorem ps_valid_unfold_l {c : M.Domain} (hc : Ps_valid_d c) :
    (∃ T a, Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
      ∃ T k a b d, Pc_node_d T k c a b d ∧ Ps_valid_d a ∧ Ps_valid_d b ∧ Ps_valid_d d := by
  obtain ⟨n, hn⟩ := hc
  rcases ps_rank_unfold_l hn with h | ⟨T, k, a, b, d, h, ha, hb, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨T, k, a, b, d, h, ha.imp (fun _ h => h.2), hb.imp (fun _ h => h.2), hd.imp (fun _ h => h.2)⟩

theorem po_irrefl_l (hM : M.Models KPi) {c : M.Domain} (hc : Ps_valid_d c) : ¬ Po_lt_d c c := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  obtain ⟨n, hn⟩ := hc
  let φ : UnarySchema 0 := { body := .forallE (.imp (ps_rank_m (.bound 1) .newest) (.neg (po_lt_m .newest .newest))) }
  have hφ h : φ.denote (jh_env_l n) h ↔ ∀ c, Ps_rank_d h c → ¬ Po_lt_d c c := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ps_rank_formula_l hKP, Formula.satisfies_neg_iff, po_lt_formula_l hKP]; rfl
  apply (hφ n).mp (hi φ (jh_env_l n) ?_ n) c hn
  intro h ih
  apply (hφ h).mpr
  intro c hc
  have child {a} (ha : ∃ m, M.mem m h ∧ Ps_rank_d m a) : ¬ Po_lt_d a a :=
    ha.elim fun m hm => (hφ m).mp (ih m hm.1) a hm.2
  rcases ps_rank_unfold_l hc with ⟨T, a, hc, _⟩ | ⟨T, k, a, b, d, hc, ha, hb, hd⟩
  · exact fun h => KP.mem_irrefl_d hKP a ((po_leaf_iff_l hM hc hc).mp h)
  · intro h
    rcases (po_node_iff_l hM hc hc).mp h with h | ⟨_, h⟩
    · exact Nat.lt_irrefl _ h
    · exact h.elim (child ha) (fun h => h.2.elim (child hb) (fun h => child hd h.2))

theorem po_compare_l (hM : M.Models KPi) {c d : M.Domain} (hc : Ps_valid_d c) (hd : Ps_valid_d d) :
    c = d ∨ Po_lt_d c d ∨ Po_lt_d d c := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  obtain ⟨n, hn⟩ := hc
  let φ : UnarySchema 0 := { body := .forallE (.imp (ps_rank_m (.bound 1) .newest)
    (.forallE (.imp (ps_valid_m .newest) (.disj (Formula.extensionalEq (.bound 1) .newest)
      (.disj (po_lt_m (.bound 1) .newest) (po_lt_m .newest (.bound 1))))))) }
  have hφ h : φ.denote (jh_env_l n) h ↔ ∀ c, Ps_rank_d h c → ∀ d, Ps_valid_d d →
      c = d ∨ Po_lt_d c d ∨ Po_lt_d d c := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ps_rank_formula_l hKP, ps_valid_sat_l hKP, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hKP.1, po_lt_formula_l hKP]; rfl
  apply (hφ n).mp (hi φ (jh_env_l n) ?_ n) c hn d hd
  intro h ih
  apply (hφ h).mpr
  intro c hc d hd
  have child {a x} (ha : ∃ m, M.mem m h ∧ Ps_rank_d m a) (hx : Ps_valid_d x) :
      a = x ∨ Po_lt_d a x ∨ Po_lt_d x a := ha.elim fun m hm => (hφ m).mp (ih m hm.1) a hm.2 x hx
  rcases ps_rank_unfold_l hc with ⟨T, a, hc, ha⟩ | ⟨T, k, a, b, e, hc, ha, hb, he⟩ <;>
    rcases ps_valid_unfold_l hd with ⟨U, x, hd, hx⟩ | ⟨U, l, x, y, z, hd, hx, hy, hz⟩
  · rcases Structure.IsOrdinal.trichotomy hKP.1 ha hx (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP a x) with h | h | h
    · have h := hKP.1.eq_of_same_members a x h; subst x
      exact Or.inl (pc_leaf_unique_l hKP.1 hc hd)
    · exact Or.inr (Or.inl ((po_leaf_iff_l hM hc hd).mpr h))
    · exact Or.inr (Or.inr ((po_leaf_iff_l hM hd hc).mpr h))
  · exact Or.inr (Or.inl (po_leaf_node_l hM hc hd))
  · exact Or.inr (Or.inr (po_leaf_node_l hM hd hc))
  · rcases Nat.lt_trichotomy (pc_tag_l k) (pc_tag_l l) with h | h | h
    · exact Or.inr (Or.inl ((po_node_iff_l hM hc hd).mpr (Or.inl h)))
    · have h := pc_tag_inj_l h; subst l
      rcases child ha hx with h | h | h
      · subst x
        rcases child hb hy with h | h | h
        · subst y
          rcases child he hz with h | h | h
          · subst z; exact Or.inl (pc_node_unique_l hKP.1 hc hd)
          · exact Or.inr (Or.inl ((po_node_iff_l hM hc hd).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩⟩)))
          · exact Or.inr (Or.inr ((po_node_iff_l hM hd hc).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩⟩)))
        · exact Or.inr (Or.inl ((po_node_iff_l hM hc hd).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl h⟩⟩)))
        · exact Or.inr (Or.inr ((po_node_iff_l hM hd hc).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl h⟩⟩)))
      · exact Or.inr (Or.inl ((po_node_iff_l hM hc hd).mpr (Or.inr ⟨rfl, Or.inl h⟩)))
      · exact Or.inr (Or.inr ((po_node_iff_l hM hd hc).mpr (Or.inr ⟨rfl, Or.inl h⟩)))
    · exact Or.inr (Or.inr ((po_node_iff_l hM hd hc).mpr (Or.inl h)))

theorem po_lex_trans_l {D : Type u} {R : D → D → Prop} {a b c x y z p q r : D}
    (ha : R a x → R x p → R a p) (hb : R b y → R y q → R b q) (hc : R c z → R z r → R c r)
    (h : Po_lex_d R a b c x y z) (g : Po_lex_d R x y z p q r) : Po_lex_d R a b c p q r := by
  rcases h with h | ⟨h, g' | ⟨g', f⟩⟩ <;> rcases g with i | ⟨i, j | ⟨j, k⟩⟩
  · exact Or.inl (ha h i)
  · exact Or.inl (i ▸ h)
  · exact Or.inl (i ▸ h)
  · exact Or.inl (h.symm ▸ i)
  · exact Or.inr ⟨h.trans i, Or.inl (hb g' j)⟩
  · exact Or.inr ⟨h.trans i, Or.inl (j ▸ g')⟩
  · exact Or.inl (h.symm ▸ i)
  · exact Or.inr ⟨h.trans i, Or.inl (g'.symm ▸ j)⟩
  · exact Or.inr ⟨h.trans i, Or.inr ⟨g'.trans j, hc f k⟩⟩

theorem po_trans_l (hM : M.Models KPi) {c d e : M.Domain}
    (hc : Ps_valid_d c) (hd : Ps_valid_d d) (he : Ps_valid_d e) (hcd : Po_lt_d c d) (hde : Po_lt_d d e) : Po_lt_d c e := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  obtain ⟨n, hn⟩ := hc
  let φ : UnarySchema 0 := { body := .forallE (.imp (ps_rank_m (.bound 1) .newest)
    (.forallE (.forallE (.imp (.conj (ps_valid_m (.bound 1)) (ps_valid_m .newest))
      (.imp (po_lt_m (.bound 2) (.bound 1)) (.imp (po_lt_m (.bound 1) .newest) (po_lt_m (.bound 2) .newest))))))) }
  have hφ h : φ.denote (jh_env_l n) h ↔ ∀ c, Ps_rank_d h c → ∀ d e,
      Ps_valid_d d ∧ Ps_valid_d e → Po_lt_d c d → Po_lt_d d e → Po_lt_d c e := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ps_rank_formula_l hKP, Formula.satisfies_conj_iff, ps_valid_sat_l hKP, po_lt_formula_l hKP]; rfl
  apply (hφ n).mp (hi φ (jh_env_l n) ?_ n) c hn d e ⟨hd, he⟩ hcd hde
  intro h ih
  apply (hφ h).mpr
  intro c hc d e ⟨hd, he⟩ hcd hde
  have child {a x p} (ha : ∃ m, M.mem m h ∧ Ps_rank_d m a) (hx : Ps_valid_d x) (hp : Ps_valid_d p) :
      Po_lt_d a x → Po_lt_d x p → Po_lt_d a p := ha.elim fun m hm => (hφ m).mp (ih m hm.1) a hm.2 x p ⟨hx, hp⟩
  rcases ps_rank_unfold_l hc with ⟨T, a, hc, _⟩ | ⟨T, k, a, b, f, hc, ha, hb, hf⟩ <;>
    rcases ps_valid_unfold_l hd with ⟨U, x, hd, _⟩ | ⟨U, l, x, y, z, hd, hx, hy, hz⟩ <;>
    rcases ps_valid_unfold_l he with ⟨V, p, he, hp⟩ | ⟨V, j, p, q, r, he, hp, hq, hr⟩
  · exact (po_leaf_iff_l hM hc he).mpr (hp.transitive x ((po_leaf_iff_l hM hd he).mp hde) a ((po_leaf_iff_l hM hc hd).mp hcd))
  · exact po_leaf_node_l hM hc he
  · exact (po_node_leaf_false_l hKP hd he hde).elim
  · exact po_leaf_node_l hM hc he
  · exact (po_node_leaf_false_l hKP hc hd hcd).elim
  · exact (po_node_leaf_false_l hKP hc hd hcd).elim
  · exact (po_node_leaf_false_l hKP hd he hde).elim
  · apply (po_node_iff_l hM hc he).mpr
    rcases (po_node_iff_l hM hc hd).mp hcd with h | ⟨rfl, h⟩ <;>
      rcases (po_node_iff_l hM hd he).mp hde with g | ⟨rfl, g⟩
    · exact Or.inl (Nat.lt_trans h g)
    · exact Or.inl h
    · exact Or.inl g
    · exact Or.inr ⟨rfl, po_lex_trans_l (child ha hx hp) (child hb hy hq) (child hf hz hr) h g⟩

theorem po_asymm_l (hM : M.Models KPi) {c d : M.Domain} (hc : Ps_valid_d c) (hd : Ps_valid_d d)
    (h : Po_lt_d c d) : ¬ Po_lt_d d c := fun g => po_irrefl_l hM hc (po_trans_l hM hc hd hc h g)

end YesMetaZFC.SetTheory.InnerModel
