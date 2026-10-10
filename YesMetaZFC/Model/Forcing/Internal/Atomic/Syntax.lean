import YesMetaZFC.Model.Forcing.Internal.Check.Syntax

/-! # 内部原子力迫的带条件双模拟公式

三元组 (p,s,t) 表示条件 p 下名称 s 与 t 的等同。匹配要求在每个非零加强下，
还能加强到某个带权子名称匹配；两侧同时要求这一条件。所有关系证书都是模型集合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Triple_d (q p s t : M.Domain) : Prop := ∃ a, KPair_d M a s t ∧ KPair_d M q p a
def Rel_d (F p s t : M.Domain) : Prop := ∃ q, Triple_d M q p s t ∧ M.mem q F
def Below_d (B R z q p : M.Domain) : Prop := M.mem q B ∧ q ≠ z ∧ Entry_d M q p R

def Match_wit_d (k : Bool) (B R z F q a t : M.Domain) : Prop :=
  ∃ r d c, Below_d M B R z r q ∧ Entry_d M d c t ∧ Entry_d M r c R ∧
    (if k then Rel_d M F r d a else Rel_d M F r a d)

def Match_d (k : Bool) (B R z F p s t : M.Domain) : Prop :=
  ∀ a b, Entry_d M a b s → ∀ q, Below_d M B R z q p → Entry_d M q b R →
    Match_wit_d M k B R z F q a t

def Bisim_d (B R z F : M.Domain) : Prop := ∀ p s t, Rel_d M F p s t →
  Match_d M false B R z F p s t ∧ Match_d M true B R z F p t s

/-- 对条件集中的 p，内部集合双模拟是等号力迫的证书。 -/
def Eq_force_d (B R z p s t : M.Domain) : Prop :=
  M.mem p B ∧ ∃ F, Bisim_d M B R z F ∧ Rel_d M F p s t

def triple_m {n} (q p s t : Term n) : Formula 1 n :=
  .existsE (.conj (kpair_m .newest s.weaken t.weaken) (kpair_m q.weaken p.weaken .newest))
derive_free_closed triple_m

def rel_m {n} (F p s t : Term n) : Formula 1 n :=
  .existsE (.conj (triple_m .newest p.weaken s.weaken t.weaken) (.mem .newest F.weaken))
derive_free_closed rel_m

def below_m {n} (B R z q p : Term n) : Formula 1 n :=
  .conj (.mem q B) (.conj (.neg (Formula.extensionalEq q z)) (entry_m q p R))
derive_free_closed below_m

def match_wit_m (k : Bool) {n} (B R z F q a t : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj
    (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
      (.bound 2) q.weaken.weaken.weaken)
    (.conj (entry_m (.bound 1) .newest t.weaken.weaken.weaken)
      (.conj (entry_m (.bound 2) .newest R.weaken.weaken.weaken)
        (if k then rel_m F.weaken.weaken.weaken (.bound 2) (.bound 1) a.weaken.weaken.weaken
          else rel_m F.weaken.weaken.weaken (.bound 2) a.weaken.weaken.weaken (.bound 1)))))))
@[simp] theorem match_wit_m_freeClosed (k : Bool) {n} (B R z F q a t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hF : F.freeSupport = []) (hq : q.freeSupport = []) (ha : a.freeSupport = [])
    (ht : t.freeSupport = []) : (match_wit_m k B R z F q a t).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [match_wit_m, Definitional.Formula.FreeClosed,
    hB, hR, hz, hF, hq, ha, ht]

def match_m (k : Bool) {n} (B R z F p s t : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest s.weaken.weaken)
    (.forallE (.imp
      (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        .newest p.weaken.weaken.weaken)
      (.imp (entry_m .newest (.bound 1) R.weaken.weaken.weaken)
        (match_wit_m k B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
          F.weaken.weaken.weaken .newest (.bound 2) t.weaken.weaken.weaken))))))
derive_free_closed match_m

def bisim_m {n} (B R z F : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp
    (rel_m F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
    (.conj (match_m false B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
      F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
      (match_m true B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        F.weaken.weaken.weaken (.bound 2) .newest (.bound 1))))))
derive_free_closed bisim_m

def eq_force_m {n} (B R z p s t : Term n) : Formula 1 n :=
  .conj (.mem p B) (.existsE (.conj (bisim_m B.weaken R.weaken z.weaken .newest)
    (rel_m .newest p.weaken s.weaken t.weaken)))
derive_free_closed eq_force_m

theorem triple_sat_l (hE : Extensional M) {n} (ρ : Env M n) (q p s t : Term n) :
    Formula.satisfies ρ (triple_m q p s t) ↔ Triple_d M (q.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [triple_m, Triple_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem rel_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F p s t : Term n) :
    Formula.satisfies ρ (rel_m F p s t) ↔ Rel_d M (F.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [rel_m, Rel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, triple_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem below_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z q p : Term n) :
    Formula.satisfies ρ (below_m B R z q p) ↔
      Below_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (q.eval ρ) (p.eval ρ) := by
  simp only [below_m, Below_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, entry_sat_l M hE]

theorem match_wit_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n)
    (B R z F q a t : Term n) : Formula.satisfies ρ (match_wit_m k B R z F q a t) ↔
      Match_wit_d M k (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (q.eval ρ) (a.eval ρ) (t.eval ρ) := by
  cases k <;> simp only [match_wit_m, Match_wit_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, below_sat_l M hE,
    entry_sat_l M hE, rel_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem match_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n)
    (B R z F p s t : Term n) : Formula.satisfies ρ (match_m k B R z F p s t) ↔
      Match_d M k (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [match_m, Match_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    below_sat_l M hE, entry_sat_l M hE, match_wit_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem bisim_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F : Term n) :
    Formula.satisfies ρ (bisim_m B R z F) ↔
      Bisim_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) := by
  simp only [bisim_m, Bisim_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, rel_sat_l M hE, match_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem eq_force_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z p s t : Term n) :
    Formula.satisfies ρ (eq_force_m B R z p s t) ↔
      Eq_force_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [eq_force_m, Eq_force_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, bisim_sat_l M hE, rel_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem triple_inj_l {q p s t p' s' t'} (h : Triple_d M q p s t) (k : Triple_d M q p' s' t') :
    p = p' ∧ s = s' ∧ t = t' := by
  obtain ⟨a, ha, hq⟩ := h
  obtain ⟨a', ha', hq'⟩ := k
  obtain ⟨hp, rfl⟩ := kpair_injective_l M hq hq'
  exact ⟨hp, kpair_injective_l M ha ha'⟩

theorem rel_mono_l {F G} (h : ∀ q, M.mem q F → M.mem q G) {p s t}
    (hF : Rel_d M F p s t) : Rel_d M G p s t :=
  hF.elim fun q hq => ⟨q, hq.1, h q hq.2⟩

theorem match_mono_l {F G} (h : ∀ q, M.mem q F → M.mem q G) (k : Bool) {B R z p s t}
    (hf : Match_d M k B R z F p s t) : Match_d M k B R z G p s t := by
  intro a b hab q hq hqb
  obtain ⟨r, d, c, hr, hd, hc, hf⟩ := hf a b hab q hq hqb
  refine ⟨r, d, c, hr, hd, hc, ?_⟩
  cases k <;> exact rel_mono_l M h hf

end YesMetaZFC.Model.Forcing.Internal
