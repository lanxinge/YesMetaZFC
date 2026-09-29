import YesMetaZFC.Model.Forcing.InternalDefinability
import YesMetaZFC.Model.Forcing.InternalGraph

/-! # 内部原子力迫的求值真值引理

左图的良基归纳处理双向子名称匹配。泛型性仅用于由实际原子公式分离的见证集和
否定匹配集；既不假定原子真值引理，也不要求内部条件代数在宿主中完备。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph Boolean
universe u v
variable (M : SetTheory.Structure.{u})

def Wit_d (k : Bool) (B R z p s t : M.Domain) : Prop :=
  ∃ a b, Entry_d M a b t ∧ Entry_d M p b R ∧
    (if k then Eq_force_d M B R z p a s else Eq_force_d M B R z p s a)

def Bad_d (k : Bool) (B R z p s t : M.Domain) : Prop :=
  ∃ a b, Entry_d M a b s ∧ Entry_d M p b R ∧
    Neg_d M B R z (fun q => Wit_d M k B R z q a t) p

def wit_m (k : Bool) {n} (B R z p s t : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (entry_m (.bound 1) .newest t.weaken.weaken)
    (.conj (entry_m p.weaken.weaken .newest R.weaken.weaken)
      (if k then eq_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken
        p.weaken.weaken (.bound 1) s.weaken.weaken
      else eq_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken
        p.weaken.weaken s.weaken.weaken (.bound 1)))))

@[simp] theorem wit_m_freeClosed (k : Bool) {n} (B R z p s t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (wit_m k B R z p s t).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [wit_m, Definitional.Formula.FreeClosed, *]

def bad_m (k : Bool) {n} (B R z p s t : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (entry_m (.bound 1) .newest s.weaken.weaken)
    (.conj (entry_m p.weaken.weaken .newest R.weaken.weaken)
      (.forallE (.imp (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken
        z.weaken.weaken.weaken .newest p.weaken.weaken.weaken)
        (.neg (wit_m k B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
          .newest (.bound 2) t.weaken.weaken.weaken)))))))
derive_free_closed bad_m

theorem wit_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (B R z p s t : Term n) :
    Formula.satisfies ρ (wit_m k B R z p s t) ↔
      Wit_d M k (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  cases k <;> simp only [wit_m, Wit_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, entry_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

theorem bad_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (B R z p s t : Term n) :
    Formula.satisfies ρ (bad_m k B R z p s t) ↔
      Bad_d M k (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [bad_m, Bad_d, Neg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    entry_sat_l M hE, below_sat_l M hE, wit_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem wit_defined_l (hE : Extensional M) (k : Bool) (B R z s t : M.Domain) :
    Defined_d M (fun p => Wit_d M k B R z p s t) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := wit_m k (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  exact ⟨5, φ, ρ, fun p => wit_sat_l M hE k (ρ.push p)
    (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1)⟩

theorem bad_defined_l (hE : Extensional M) (B R z s t : M.Domain) :
    Defined_d M (fun p => Bad_d M false B R z p s t ∨ Bad_d M true B R z p t s) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 := {
    body := .disj
      (bad_m false (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1))
      (bad_m true (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 1) (.bound 2)) }
  refine ⟨5, φ, ρ, fun p => ?_⟩
  exact (Formula.satisfies_disj_iff _ _ _).trans
    (or_congr (bad_sat_l M hE false (ρ.push p) _ _ _ _ _ _) (bad_sat_l M hE true (ρ.push p) _ _ _ _ _ _))

theorem neq_bad_dense_l (hZF : M.Models ZF) {B R z p s t}
    (hs : Name_d M B s) (ht : Name_d M B t)
    (h : Neg_d M B R z (fun q => Eq_force_d M B R z q s t) p) :
    Dense_d M B R z (fun q => Bad_d M false B R z q s t ∨ Bad_d M true B R z q t s) p := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  apply h q hq
  apply (eq_force_unfold_l M hZF hs ht).mpr
  refine ⟨hq.1, ?_, ?_⟩
  · intro a b hab r hr hrb
    apply Classical.byContradiction
    intro hw
    exact hn ⟨r, hr, Or.inl ⟨a, b, hab, hrb, fun v hv ⟨d, c, hd, hvc, he⟩ =>
      hw ⟨v, d, c, hv, hd, hvc, he⟩⟩⟩
  · intro a b hab r hr hrb
    apply Classical.byContradiction
    intro hw
    exact hn ⟨r, hr, Or.inr ⟨a, b, hab, hrb, fun v hv ⟨d, c, hd, hvc, he⟩ =>
      hw ⟨v, d, c, hv, hd, hvc, he⟩⟩⟩

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
  {U : M.Domain → Prop} (hU : Generic_d M B R z U)
include O hZF hU

private theorem wit_truth_l (k : Bool) {s t} (hs : Name_d M B s)
    (G H : BV_graph.{v, u} M.Domain) (hH : Rep_d M B t H)
    (ih : ∀ a : H.Child H.root, ∀ d, Rep_d M B d (H.at_node a) →
      ((∃ p, U p ∧ (if k then Eq_force_d M B R z p d s else Eq_force_d M B R z p s d)) ↔
        Forcing.val_l U G = Forcing.val_l U (H.at_node a))) :
    (∃ p, U p ∧ Wit_d M k B R z p s t) ↔ Forcing.val_l U G ∈ Forcing.val_l U H := by
  constructor
  · rintro ⟨p, hp, d, b, hd, hpb, he⟩
    have hb := hU.upward p b hp (name_entry_l M hH.1 hd).2 hpb
    obtain ⟨hn, c, hc, hf, hg⟩ := hH
    obtain ⟨a, ha, had, hav⟩ := hg H.root d b (hc ▸ hd)
    have hr : Rep_d M B d (H.at_node a) := ⟨(name_entry_l M hn hd).1, c, had, hf, hg⟩
    exact (Forcing.val_mem_l U H _).mpr ⟨⟨a, ha⟩, hav.symm ▸ hb, (ih ⟨a, ha⟩ d hr).mp ⟨p, hp, he⟩⟩
  · intro h
    obtain ⟨a, ha, he⟩ := (Forcing.val_mem_l U H _).mp h
    obtain ⟨d, hd, hr⟩ := rep_child_l M hH a
    obtain ⟨p, hp, he⟩ := (ih a d hr).mpr he
    obtain ⟨q, hq, hqp, hqa⟩ := hU.directed p (H.val a H.root) hp ha
    have hq' := hU.proper q hq
    refine ⟨q, hq, d, H.val a H.root, hd, hqa, ?_⟩
    cases k
    · exact eq_force_lower_l O hZF hs hr.1 p q (hU.proper p hp).1 ⟨hq'.1, hq'.2, hqp⟩ he
    · exact eq_force_lower_l O hZF hr.1 hs p q (hU.proper p hp).1 ⟨hq'.1, hq'.2, hqp⟩ he

/-- 原子等号真值定理，泛型条件与内部公式均已由模型集合实现。 -/
theorem eq_force_truth_l {s t} (G H : BV_graph.{v, u} M.Domain)
    (hG : Rep_d M B s G) (hH : Rep_d M B t H) :
    (∃ p, U p ∧ Eq_force_d M B R z p s t) ↔ Forcing.val_l U G = Forcing.val_l U H := by
  have he (a : G.Domain) : ∀ (H : BV_graph.{v, u} M.Domain) s t,
      Rep_d M B s (G.at_node a) → Rep_d M B t H →
      ((∃ p, U p ∧ Eq_force_d M B R z p s t) ↔
        Forcing.val_l U (G.at_node a) = Forcing.val_l U H) := by
    induction a using G.wf.induction with
    | h a ih =>
      intro H s t hs ht
      have left (c : (G.at_node a).Child a) d (hd : Rep_d M B d (G.at_node c)) :=
        wit_truth_l O hZF hU false hd.1 (G.at_node c) H ht
          (fun e v hv => ih c c.2 (H.at_node e) d v hd hv)
      have right (c : H.Child H.root) d (hd : Rep_d M B d (H.at_node c)) :=
        wit_truth_l O hZF hU true hd.1 (H.at_node c) (G.at_node a) hs
          (fun e v hv => (ih e e.2 (H.at_node c) v d hv hd).trans eq_comm)
      have match_to_mem (k : Bool) {s t} (hs : Name_d M B s)
          {p d b} (hp : U p) (hb : U b) (hd : Entry_d M d b s)
          (hm : Eq_match_d M k B R z p s t) : ∃ q, U q ∧ Wit_d M k B R z q d t := by
        obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
        apply generic_pick_l hZF hU (wit_defined_l M hZF.1 k B R z d t) hr
        intro q hq
        have hqp : Below_d M B R z q p := ⟨hq.1, hq.2.1,
          O.trans q r p hq.1 (hU.proper r hr).1 (hU.proper p hp).1 hq.2.2 hrp⟩
        obtain ⟨v, e, c, hv, he, hvc, hvE⟩ := hm d b hd q hqp
          (O.trans q r b hq.1 (hU.proper r hr).1 (name_entry_l M hs hd).2 hq.2.2 hrb)
        exact ⟨v, hv, e, c, he, hvc, hvE⟩
      constructor
      · rintro ⟨p, hp, he⟩
        obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF hs.1 ht.1).mp he
        apply SG_set.ext
        intro x
        constructor
        · intro hx
          obtain ⟨c, hc, rfl⟩ := (Forcing.val_mem_l U (G.at_node a) x).mp hx
          obtain ⟨d, hd, hdG⟩ := rep_child_l M hs c
          exact (left c d hdG).mp (match_to_mem false hs.1 hp hc hd hl)
        · intro hx
          obtain ⟨c, hc, rfl⟩ := (Forcing.val_mem_l U H x).mp hx
          obtain ⟨d, hd, hdH⟩ := rep_child_l M ht c
          exact (right c d hdH).mp (match_to_mem true ht.1 hp hc hd hr)
      · intro hv
        apply Classical.byContradiction
        intro hn
        have hp := (generic_decide_l O hZF hU (eq_force_defined_l M hZF.1 B R z s t)).elim
          (fun h => False.elim (hn h)) id
        obtain ⟨p, hp, he⟩ := hp
        obtain ⟨q, hq, hbad⟩ := generic_pick_l hZF hU (bad_defined_l M hZF.1 B R z s t) hp
          (neq_bad_dense_l M hZF hs.1 ht.1 he)
        have no_wit (k : Bool) {d t} (h : Neg_d M B R z (fun p => Wit_d M k B R z p d t) q)
            (hw : ∃ p, U p ∧ Wit_d M k B R z p d t) (hD : Name_d M B d) (hT : Name_d M B t) : False := by
          obtain ⟨p, hp, e, b, he, hpb, heq⟩ := hw
          obtain ⟨r, hr, hrq, hrp⟩ := hU.directed q p hq hp
          have hr' := hU.proper r hr
          apply h r ⟨hr'.1, hr'.2, hrq⟩
          refine ⟨e, b, he, O.trans r p b hr'.1 (hU.proper p hp).1
            (name_entry_l M hT he).2 hrp hpb, ?_⟩
          cases k
          · exact eq_force_lower_l O hZF hD (name_entry_l M hT he).1 p r
              (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ heq
          · exact eq_force_lower_l O hZF (name_entry_l M hT he).1 hD p r
              (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ heq
        rcases hbad with ⟨d, b, hd, hqb, hbad⟩ | ⟨d, b, hd, hqb, hbad⟩
        · have hb := hU.upward q b hq (name_entry_l M hs.1 hd).2 hqb
          obtain ⟨hsN, c, hc, hf, hg⟩ := hs
          obtain ⟨e, he, hed, heb⟩ := hg a d b (hc ▸ hd)
          have hdG : Rep_d M B d (G.at_node e) := ⟨(name_entry_l M hsN hd).1, c, hed, hf, hg⟩
          have hm := (Forcing.val_mem_l U (G.at_node a) _).mpr
            ⟨⟨e, he⟩, heb.symm ▸ hb, rfl⟩
          rw [hv] at hm
          exact no_wit false hbad ((left ⟨e, he⟩ d hdG).mpr hm) hdG.1 ht.1
        · have hb := hU.upward q b hq (name_entry_l M ht.1 hd).2 hqb
          obtain ⟨htN, c, hc, hf, hg⟩ := ht
          obtain ⟨e, he, hed, heb⟩ := hg H.root d b (hc ▸ hd)
          have hdH : Rep_d M B d (H.at_node e) := ⟨(name_entry_l M htN hd).1, c, hed, hf, hg⟩
          have hm := (Forcing.val_mem_l U H _).mpr ⟨⟨e, he⟩, heb.symm ▸ hb, rfl⟩
          rw [← hv] at hm
          exact no_wit true hbad ((right ⟨e, he⟩ d hdH).mpr hm) hdH.1 hs.1
  exact he G.root H s t hG hH

theorem mem_force_truth_l {s t} (G H : BV_graph.{v, u} M.Domain)
    (hG : Rep_d M B s G) (hH : Rep_d M B t H) :
    (∃ p, U p ∧ Mem_force_d M B R z p s t) ↔ Forcing.val_l U G ∈ Forcing.val_l U H := by
  have hw := wit_truth_l O hZF hU false hG.1 G H hH
    (fun a d hd => eq_force_truth_l O hZF hU G (H.at_node a) hG hd)
  constructor
  · rintro ⟨p, hp, _, h⟩
    apply hw.mp
    exact generic_pick_l hZF hU (wit_defined_l M hZF.1 false B R z s t) hp
      (fun q hq => by obtain ⟨r, a, b, hr, ha, hrb, he⟩ := h q hq; exact ⟨r, hr, a, b, ha, hrb, he⟩)
  · intro h
    obtain ⟨p, hp, a, b, ha, hpb, he⟩ := hw.mpr h
    refine ⟨p, hp, (hU.proper p hp).1, fun q hq => ?_⟩
    exact ⟨q, a, b, below_refl_l O hq.1 hq.2.1, ha,
      O.trans q p b hq.1 (hU.proper p hp).1 (name_entry_l M hH.1 ha).2 hq.2.2 hpb,
      eq_force_lower_l O hZF hG.1 (name_entry_l M hH.1 ha).1 p q (hU.proper p hp).1 hq he⟩

/-- 直接对内部名称解释关系调用原子真值，不必暴露图呈现。 -/
theorem val_mem_forcing_l {s t} {x y : SG_set.{v}}
    (hs : Val_d M B U s x) (ht : Val_d M B U t y) :
    (∃ p, U p ∧ Mem_force_d M B R z p s t) ↔ x ∈ y := by
  obtain ⟨G, hG, rfl⟩ := hs
  obtain ⟨H, hH, rfl⟩ := ht
  exact mem_force_truth_l O hZF hU G H hG hH

theorem val_eq_forcing_l {s t} {x y : SG_set.{v}}
    (hs : Val_d M B U s x) (ht : Val_d M B U t y) :
    (∃ p, U p ∧ Eq_force_d M B R z p s t) ↔ x = y := by
  obtain ⟨G, hG, rfl⟩ := hs
  obtain ⟨H, hH, rfl⟩ := ht
  exact eq_force_truth_l O hZF hU G H hG hH

end YesMetaZFC.Model.Forcing.Internal
