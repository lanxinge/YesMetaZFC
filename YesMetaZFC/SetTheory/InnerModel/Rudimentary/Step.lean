import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph

/-! # Jensen 有限基的一步集合扩张 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rd_menu_l : List Rd_sym := [.pair, .diff, .prod, .mid, .last, .union, .range, .mem,
  .fibers, .opair, .triple, .adj, .fiber]

theorem rd_menu_mem_l (k : Rd_sym) : k ∈ rd_menu_l := by cases k <;> simp [rd_menu_l]

def rd_any_m {n} (L : List Rd_sym) (f : Rd_sym → Formula 1 n) : Formula 1 n :=
  L.foldr (fun k p => .disj (f k) p) .falsum

@[simp] theorem rd_any_closed_l {n} (L : List Rd_sym) (f : Rd_sym → Formula 1 n)
    (h : ∀ k, (f k).FreeClosed) : (rd_any_m L f).FreeClosed := by
  induction L with
  | nil => simp only [rd_any_m, List.foldr_nil, Definitional.Formula.FreeClosed]
  | cons k L ih =>
    simpa only [rd_any_m, List.foldr_cons, Definitional.Formula.FreeClosed] using! And.intro (h k) ih

theorem rd_any_delta_l {n} (L : List Rd_sym) (f : Rd_sym → Formula 1 n)
    (h : ∀ k, (f k).IsDelta0) : (rd_any_m L f).IsDelta0 := by
  induction L with
  | nil => exact .falsum
  | cons k L ih => exact .disj (h k) ih

theorem rd_any_sat_l {n} (ρ : Env M n) (L : List Rd_sym) (f : Rd_sym → Formula 1 n) :
    Formula.satisfies ρ (rd_any_m L f) ↔ ∃ k, k ∈ L ∧ Formula.satisfies ρ (f k) := by
  induction L with
  | nil => simp only [rd_any_m, List.foldr_nil, Formula.satisfies_falsum_iff, List.not_mem_nil, false_and, exists_false]
  | cons k L ih => simpa only [rd_any_m, List.foldr_cons, Formula.satisfies_disj_iff,
      List.mem_cons, exists_eq_or_imp] using or_congr Iff.rfl ih

def Rd_value_d (U t : M.Domain) : Prop := ∃ k a b c,
  M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c t

def rd_value_m {n} (U t : Term n) : Formula 1 n :=
  Formula.existsMem U (Formula.existsMem U.weaken (Formula.existsMem U.weaken.weaken
    (rd_any_m rd_menu_l (fun k => rd_graph_m k (.bound 2) (.bound 1) .newest t.weaken.weaken.weaken))))
derive_free_closed rd_value_m

theorem rd_value_delta_l {n} (U t : Term n) : (rd_value_m U t).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (rd_any_delta_l _ _ (fun _ => rd_graph_delta_l ..))))

theorem rd_value_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (U t : Term n) :
    Formula.satisfies ρ (rd_value_m U t) ↔ Rd_value_d (U.eval ρ) (t.eval ρ) := by
  simp only [rd_value_m, Formula.satisfies_existsMem_iff, rd_any_sat_l, rd_graph_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨a, ha, b, hb, c, hc, k, _, h⟩ => ⟨k, a, b, c, ha, hb, hc, h⟩,
    fun ⟨k, a, b, c, ha, hb, hc, h⟩ => ⟨a, ha, b, hb, c, hc, k, rd_menu_mem_l k, h⟩⟩

theorem rd_image_exists_l (hKP : M.Models KP) (k : Rd_sym) (U : M.Domain) :
    ∃ V, ∀ t, M.mem t V ↔ ∃ a b c, M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c t := by
  obtain ⟨P, hP⟩ := rd_triples_exists_l hKP U U U
  let ρ : Env M 1 := ⟨fun _ => U, fun _ => U⟩
  let φ : Delta0BinarySchema 1 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
      (.conj (rd_triple0_m (.bound 4) (.bound 2) (.bound 1) .newest)
        (rd_graph_m k (.bound 2) (.bound 1) .newest (.bound 3)))))
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..) (rd_graph_delta_l ..)))) }
  have hφ p t : φ.toBinarySchema.denote ρ p t ↔ ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧
      Rd_triple_d p a b c ∧ Rd_fun_d k a b c t := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_triple0_sat_l hKP.1, rd_graph_sat_l hKP]
    rfl
  obtain ⟨V, hV⟩ := KP.d0_image_l hKP φ ρ P (by
    intro p hp
    obtain ⟨a, ha, b, hb, c, hc, hp⟩ := (hP p).mp hp
    obtain ⟨t, ht⟩ := rd_fun_exists_l hKP k a b c
    exact ⟨t, (hφ p t).mpr ⟨a, ha, b, hb, c, hc, hp, ht⟩⟩) (by
    intro p _ s t hs ht
    obtain ⟨a, _, b, _, c, _, ⟨q, hq, hp⟩, hs⟩ := (hφ p s).mp hs
    obtain ⟨d, _, e, _, f, _, ⟨r, hr, hp'⟩, ht⟩ := (hφ p t).mp ht
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq hr
    exact rd_fun_unique_l hKP.1 hs ht)
  refine ⟨V, fun t => (hV t).trans ?_⟩
  constructor
  · rintro ⟨p, _, h⟩
    obtain ⟨a, ha, b, hb, c, hc, _, ht⟩ := (hφ p t).mp h
    exact ⟨a, b, c, ha, hb, hc, ht⟩
  · rintro ⟨a, b, c, ha, hb, hc, ht⟩
    let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
    obtain ⟨q, hq⟩ := I.total b c
    obtain ⟨p, hp⟩ := I.total a q
    exact ⟨p, (hP p).mpr ⟨a, ha, b, hb, c, hc, q, hq, hp⟩,
      (hφ p t).mpr ⟨a, ha, b, hb, c, hc, ⟨q, hq, hp⟩, ht⟩⟩

def Rd_step_d (U V : M.Domain) : Prop := ∀ t, M.mem t V ↔ M.mem t U ∨ Rd_value_d U t

theorem rd_step_exists_l (hKP : M.Models KP) (U : M.Domain) : ∃ V, Rd_step_d U V := by
  have collect (L : List Rd_sym) : ∃ V, ∀ t, M.mem t V ↔ M.mem t U ∨ ∃ k, k ∈ L ∧ ∃ a b c,
      M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c t := by
    induction L with
    | nil => exact ⟨U, fun t => ⟨Or.inl, fun h => h.elim id (fun ⟨_, h, _⟩ => (List.not_mem_nil h).elim)⟩⟩
    | cons k L ih =>
      obtain ⟨V, hV⟩ := ih
      obtain ⟨W, hW⟩ := rd_image_exists_l hKP k U
      obtain ⟨S, hS⟩ := KP.exists_unionOfTwo hKP V W
      refine ⟨S, fun t => (hS t).trans ?_⟩
      rw [hV t, hW t]
      constructor
      · rintro ((h | ⟨j, hj, h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, h⟩
        · exact Or.inr ⟨k, List.mem_cons_self .., h⟩
      · rintro (h | ⟨j, hj, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨j, hj, h⟩)
  obtain ⟨V, hV⟩ := collect rd_menu_l
  refine ⟨V, fun t => (hV t).trans (or_congr Iff.rfl ?_)⟩
  exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, rd_menu_mem_l k, h⟩⟩

theorem rd_step_unique_l (hE : Extensional M) {U V W : M.Domain}
    (h : Rd_step_d U V) (g : Rd_step_d U W) : V = W :=
  hE.eq_of_same_members V W (fun t => (h t).trans (g t).symm)

def rd_all_m {n} (f : Rd_sym → Formula 1 n) : Formula 1 n := .neg (rd_any_m rd_menu_l (fun k => .neg (f k)))

@[simp] theorem rd_all_closed_l {n} (f : Rd_sym → Formula 1 n) (h : ∀ k, (f k).FreeClosed) :
    (rd_all_m f).FreeClosed := by simp -implicitDefEqProofs [rd_all_m, Definitional.Formula.FreeClosed, h]

theorem rd_all_delta_l {n} (f : Rd_sym → Formula 1 n) (h : ∀ k, (f k).IsDelta0) :
    (rd_all_m f).IsDelta0 := .neg (rd_any_delta_l _ _ (fun k => .neg (h k)))

theorem rd_all_sat_l {n} (ρ : Env M n) (f : Rd_sym → Formula 1 n) :
    Formula.satisfies ρ (rd_all_m f) ↔ ∀ k, Formula.satisfies ρ (f k) := by
  classical
  simp only [rd_all_m, Formula.satisfies_neg_iff, rd_any_sat_l, not_exists, not_and, Classical.not_not]
  exact ⟨fun h k => h k (rd_menu_mem_l k), fun h k _ => h k⟩

def rd_step_m {n} (U V : Term n) : Formula 1 n :=
  .conj (Formula.subset U V) (.conj (Formula.forallMem V
    (.disj (.mem .newest U.weaken) (rd_value_m U.weaken .newest)))
    (rd_all_m (fun k => Formula.forallMem U (Formula.forallMem U.weaken (Formula.forallMem U.weaken.weaken
      (Formula.existsMem V.weaken.weaken.weaken (rd_graph_m k (.bound 3) (.bound 2) (.bound 1) .newest)))))))
derive_free_closed rd_step_m

theorem rd_step_delta_l {n} (U V : Term n) : (rd_step_m U V).IsDelta0 :=
  .conj (.atom _ _ _) (.conj (.forallMem _ (.disj (.mem _ _) (rd_value_delta_l ..)))
    (rd_all_delta_l _ (fun _ => .forallMem _ (.forallMem _ (.forallMem _ (.existsMem _ (rd_graph_delta_l ..)))))))

theorem rd_step_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (U V : Term n) :
    Formula.satisfies ρ (rd_step_m U V) ↔ Rd_step_d (U.eval ρ) (V.eval ρ) := by
  simp only [rd_step_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    rd_value_sat_l hKP, rd_all_sat_l, Formula.satisfies_existsMem_iff, rd_graph_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g, f⟩ t
    refine ⟨g t, fun ht => ht.elim (h t) ?_⟩
    rintro ⟨k, a, b, c, ha, hb, hc, ht⟩
    obtain ⟨w, hw, hf⟩ := f k a ha b hb c hc
    exact (rd_fun_unique_l hKP.1 hf ht) ▸ hw
  · intro h
    refine ⟨fun t ht => (h t).mpr (Or.inl ht), fun t => (h t).mp, fun k a ha b hb c hc => ?_⟩
    obtain ⟨w, hw⟩ := rd_fun_exists_l hKP k a b c
    exact ⟨w, (h w).mpr (Or.inr ⟨k, a, b, c, ha, hb, hc, hw⟩), hw⟩

theorem rd_step_transitive_l (hE : Extensional M) {U V : M.Domain}
    (hU : M.TransitiveSet U) (h : Rd_step_d U V) : M.TransitiveSet V := by
  have old {a} (ha : M.mem a U) := (h a).mpr (Or.inl ha)
  have gen k a b c w (ha : M.mem a U) (hb : M.mem b U) (hc : M.mem c U)
      (hw : Rd_fun_d k a b c w) := (h w).mpr (Or.inr ⟨k, a, b, c, ha, hb, hc, hw⟩)
  have coords {p a b : M.Domain} (hp : M.mem p U) (h : KPair_d M p a b) : M.mem a U ∧ M.mem b U := by
    have lift t (ht : t = a ∨ t = b) : M.mem t U := by
      obtain ⟨s, hs, ht⟩ := (kpair_union_l M h t).mpr ht
      exact hU s (hU p hp s hs) t ht
    exact ⟨lift a (Or.inl rfl), lift b (Or.inr rfl)⟩
  have entry {R a b : M.Domain} (hR : M.mem R U) (h : Rd_entry_d a b R) : M.mem a U ∧ M.mem b U := by
    obtain ⟨p, hp, hpR⟩ := h
    exact coords (hU R hR p hpR) hp
  have pair {w a b : M.Domain} (ha : M.mem a U) (hb : M.mem b U) (hw : KPair_d M w a b) : M.mem w V :=
    gen .opair a b a w ha hb ha (rd_opair_value_l hE hw)
  have triple {w a b c : M.Domain} (ha : M.mem a U) (hb : M.mem b U) (hc : M.mem c U)
      (hw : Rd_triple_d w a b c) : M.mem w V := gen .triple a b c w ha hb hc (rd_triple_value_l hE hw)
  intro t ht w hw
  rcases (h t).mp ht with ht | ⟨k, a, b, c, ha, hb, hc, ht⟩
  · exact old (hU t ht w hw)
  have hw := (ht w).mp hw
  cases k with
  | pair => exact hw.elim (fun h => h.symm ▸ old ha) (fun h => h.symm ▸ old hb)
  | diff => exact old (hU a ha w hw.1)
  | prod => obtain ⟨x, y, hx, hy, hp⟩ := hw; exact pair (hU a ha x hx) (hU b hb y hy) hp
  | mid =>
    obtain ⟨x, y, z, hy, hp, ht⟩ := hw
    exact triple (entry hb hp).1 (hU a ha y hy) (entry hb hp).2 ht
  | last =>
    obtain ⟨x, y, z, hz, hp, ht⟩ := hw
    exact triple (entry hb hp).1 (entry hb hp).2 (hU a ha z hz) ht
  | union => obtain ⟨x, hx, hw⟩ := hw; exact old (hU x (hU a ha x hx) w hw)
  | range => obtain ⟨x, hp⟩ := hw; exact old (entry ha hp).2
  | mem => obtain ⟨x, y, hx, hy, _, hp⟩ := hw; exact pair (hU a ha x hx) (hU a ha y hy) hp
  | fibers => obtain ⟨y, hy, hw⟩ := hw; exact gen .fiber a y a w ha (hU b hb y hy) ha hw
  | opair =>
    rcases hw with hw | hw
    · exact gen .pair a a a w ha ha ha (fun t => (hw t).trans ⟨Or.inl, fun h => h.elim id id⟩)
    · exact gen .pair a b a w ha hb ha hw
  | triple =>
    rcases hw with hw | ⟨q, hq, hw⟩
    · exact gen .pair a a a w ha ha ha (fun t => (hw t).trans ⟨Or.inl, fun h => h.elim id id⟩)
    · exact gen .adj a b c w ha hb hc (rd_adj_value_l hE hq hw)
  | adj => exact hw.elim (fun h => h.symm ▸ old ha) (pair hb hc)
  | fiber => exact old (entry ha hw).1

end YesMetaZFC.SetTheory.InnerModel
