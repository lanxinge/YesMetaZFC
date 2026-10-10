import YesMetaZFC.Model.Forcing.Internal.Forcing.Definability

/-! # 内部原子力迫的见证与反例稠密集

所有见证集合均由实际原子公式分离，适用于外部非良基的地模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
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

end YesMetaZFC.Model.Forcing.Internal
