import YesMetaZFC.Model.Forcing.Internal.Forcing.Truth

/-! # 内部可定义加权名称构造

在模型内的名称族与条件集的笛卡尔积上分离实际关系公式。所有成员的名称性来自
已证明的内部名称递归刻画；公式的参数和布尔条件通过显式代入传递。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def force_at_m {n m} (φ : Formula 1 n) (e : Fin n → Term m) (B R z p : Term m) : Formula 1 m :=
  (force_code_m φ).bind (Fin.cases p (Fin.cases z (Fin.cases R (Fin.cases B e))))

@[simp] theorem force_at_closed_l {n m} (φ : Formula 1 n) (e : Fin n → Term m) (B R z p : Term m)
    (hφ : φ.FreeClosed) (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = [])
    (hR : R.freeSupport = []) (hz : z.freeSupport = []) (hp : p.freeSupport = []) :
    (force_at_m φ e B R z p).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr (force_code_closed_l φ hφ)
  exact Fin.cases hp (Fin.cases hz (Fin.cases hR (Fin.cases hB he)))

theorem force_at_sat_l {M : SetTheory.Structure.{u}} {n m} (φ : Formula 1 n) (ρ : Env M m)
    (e : Fin n → Term m) (B R z p : Term m) :
    Formula.satisfies ρ (force_at_m φ e B R z p) ↔
      Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (p.eval ρ) := by
  rw [force_at_m, Formula.satisfies_bind]
  have he : Definitional.Env.substitute ρ
      (Fin.cases p (Fin.cases z (Fin.cases R (Fin.cases B e)))) =
      fenv_l (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n) (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) i
    · rfl
  rw [he]
  rfl

/-- 对全部正条件的力迫规格仍是一条带有限参数的原公式。 -/
def force_all_m {n m} (φ : Formula 1 n) (e : Fin n → Term m) (B R z : Term m) : Formula 1 m :=
  .forallE (.imp (.mem .newest B.weaken) (.imp (.neg (Formula.extensionalEq .newest z.weaken))
    (force_at_m φ (fun i => (e i).weaken) B.weaken R.weaken z.weaken .newest)))

@[simp] theorem force_all_closed_l {n m} (φ : Formula 1 n) (e : Fin n → Term m) (B R z : Term m)
    (hφ : φ.FreeClosed) (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = [])
    (hR : R.freeSupport = []) (hz : z.freeSupport = []) : (force_all_m φ e B R z).FreeClosed := by
  simp only [force_all_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨rfl, by simpa using hB⟩,
    (Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨rfl, by simpa using hz⟩,
    force_at_closed_l _ _ _ _ _ _ hφ (fun i => by simpa using he i)
      (by simpa using hB) (by simpa using hR) (by simpa using hz) rfl⟩

theorem force_all_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n m}
    (φ : Formula 1 n) (ρ : Env M m) (e : Fin n → Term m) (B R z : Term m) :
    Formula.satisfies ρ (force_all_m φ e B R z) ↔ ∀ p, M.mem p (B.eval ρ) → p ≠ z.eval ρ →
      Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ ⟨fun i => (e i).eval ρ, ρ.free⟩ p := by
  simp only [force_all_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    force_at_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem args_cons_l {M : SetTheory.Structure.{u}} {n m} (ρ : Env M m) (t : Term m) (e : Fin n → Term m) :
    (⟨fun i : Fin (n + 1) => (Fin.cases t e i : Term m).eval ρ, ρ.free⟩ : Env M (n + 1)) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (t.eval ρ) := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩

/-- 在同一条件上，若某个名称满足正文，则候选名称也满足正文。 -/
def witness_m {n m} (φ : UnarySchema n) (e : Fin n → Term m) (B R z p t : Term m) : Formula 1 m :=
  .conj (name_m B t) (.forallE (.imp
    (.conj (name_m B.weaken .newest)
      (force_at_m φ.body (Fin.cases .newest (fun i => (e i).weaken)) B.weaken R.weaken z.weaken p.weaken))
    (force_at_m φ.body (Fin.cases t.weaken (fun i => (e i).weaken)) B.weaken R.weaken z.weaken p.weaken)))

@[simp] theorem witness_closed_l {n m} (φ : UnarySchema n) (e : Fin n → Term m) (B R z p t : Term m)
    (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = []) (ht : t.freeSupport = []) :
    (witness_m φ e B R z p t).FreeClosed := by
  have hc (s : Term (m+1)) (hs : s.freeSupport = []) : ∀ i : Fin (n+1),
      (Fin.cases s (fun i => (e i).weaken) i : Term (m+1)).freeSupport = [] :=
    Fin.cases hs (fun i => by simpa using he i)
  have hn := hc .newest rfl
  have hv := hc t.weaken (by simpa using ht)
  simp only [witness_m, Definitional.Formula.FreeClosed]
  refine ⟨name_m_freeClosed _ _ hB ht, ⟨name_m_freeClosed _ _ (by simpa using hB) rfl, ?_⟩, ?_⟩
  · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed hn (by simpa using hB) (by simpa using hR)
      (by simpa using hz) (by simpa using hp)
  · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed hv (by simpa using hB) (by simpa using hR)
      (by simpa using hz) (by simpa using hp)

theorem witness_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n m}
    (φ : UnarySchema n) (ρ : Env M m) (e : Fin n → Term m) (B R z p t : Term m) :
    Formula.satisfies ρ (witness_m φ e B R z p t) ↔
      Name_d M (B.eval ρ) (t.eval ρ) ∧ ∀ v, Name_d M (B.eval ρ) v →
        Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ.body
          ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push v) (p.eval ρ) →
        Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ.body
          ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (t.eval ρ)) (p.eval ρ) := by
  simp only [witness_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, name_sat_l M hE, force_at_sat_l, args_cons_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact and_congr_right fun _ => forall_congr' fun _ =>
    ⟨fun h hn hv => h ⟨hn, hv⟩, fun h ⟨hn, hv⟩ => h hn hv⟩

variable (M : SetTheory.Structure.{u})

def Source_d (R t s p : M.Domain) : Prop := ∃ b, Entry_d M s b t ∧ Entry_d M p b R

def source_m {n} (R t s p : Term n) : Formula 1 n :=
  .existsE (.conj (entry_m s.weaken .newest t.weaken) (entry_m p.weaken .newest R.weaken))
derive_free_closed source_m

theorem source_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R t s p : Term n) :
    Formula.satisfies ρ (source_m R t s p) ↔ Source_d M (R.eval ρ) (t.eval ρ) (s.eval ρ) (p.eval ρ) := by
  simp only [source_m, Source_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem source_val_l {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {s t p} {x y : Name_quot_l M B R z U} (ht : Qval_d M B R z U t x) (hs : Qval_d M B R z U s y)
    (h : Source_d M R t s p) (hp : U p) : y ∈ x := by
  obtain ⟨b, hb, hpb⟩ := h
  have hn : Name_d M B t := qval_name_l ht
  exact (qval_mem_l O hZF hU ht).mpr ⟨s, b, hb, hU.upward p b hp (name_entry_l M hn hb).2 hpb, hs⟩

/-- 精确加权分离；源集只须逐个包含内部名称，不要求它本身是闭支撑。 -/
theorem name_comp_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    (B S : M.Domain) (hS : ∀ s, M.mem s S → Name_d M B s) :
    ∃ t, Name_d M B t ∧
      (∀ q, M.mem q t ↔ ∃ s b, M.mem s S ∧ M.mem b B ∧ KPair_d M q s b ∧ φ.denote ρ s b) ∧
      ∀ s b, Entry_d M s b t ↔ M.mem s S ∧ M.mem b B ∧ φ.denote ρ s b := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨t, ht⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  have hm q : M.mem q t ↔ ∃ s b, M.mem s S ∧ M.mem b B ∧ KPair_d M q s b ∧ φ.denote ρ s b := by
    rw [ht q, hP q, Formula.satisfies_relationMember_iff I φ ρ q]
    constructor
    · rintro ⟨⟨s, hs, b, hb, hq⟩, a, c, hq', hφ⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq hq'
      exact ⟨s, b, hs, hb, hq, hφ⟩
    · rintro ⟨s, b, hs, hb, hq, hφ⟩
      exact ⟨⟨s, hs, b, hb, hq⟩, s, b, hq, hφ⟩
  refine ⟨t, ?_, hm, ?_⟩
  · apply (name_unfold_l M (name_ops_l M hZF) B t).mpr
    intro q hq
    obtain ⟨s, b, hs, hb, hq, _⟩ := (hm q).mp hq
    exact ⟨s, b, hq, hb, hS s hs⟩
  · intro s b
    constructor
    · rintro ⟨q, hq, hqt⟩
      obtain ⟨a, c, ha, hc, hq', hφ⟩ := (hm q).mp hqt
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hq hq'
      exact ⟨ha, hc, hφ⟩
    · rintro ⟨hs, hb, hφ⟩
      obtain ⟨q, hq⟩ := I.total s b
      exact ⟨q, hq, (hm q).mpr ⟨s, b, hs, hb, hq, hφ⟩⟩

end YesMetaZFC.Model.Forcing.Internal
