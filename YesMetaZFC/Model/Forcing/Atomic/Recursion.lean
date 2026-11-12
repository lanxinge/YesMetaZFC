import YesMetaZFC.Model.Forcing.Check.Syntax
import YesMetaZFC.Model.Forcing.Names.Realization
import YesMetaZFC.SetTheory.FunctionConstruction

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

/-! ## 内部最大带条件双模拟

在内部三元组集合的幂集中分离双模拟，再取并。最大关系满足原子等号的匹配方程；
证明只用实际分离公式与集合运算，不预设递归解、真值引理或外部完备性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Triple_carrier_d (B S X : M.Domain) : Prop := ∀ q, M.mem q X ↔
  ∃ p s t, M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Triple_d M q p s t

theorem triple_exists_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (p s t : M.Domain) : ∃ q, Triple_d M q p s t := by
  obtain ⟨a, ha⟩ := (kpair_interpretation_l M hE hP).total s t
  obtain ⟨q, hq⟩ := (kpair_interpretation_l M hE hP).total p a
  exact ⟨q, a, ha, hq⟩

theorem triple_carrier_l (hZF : M.Models ZF) (B S : M.Domain) :
    ∃ X, Triple_carrier_d M B S X := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I S S
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I B T
  refine ⟨X, fun q => (hX q).trans ?_⟩
  constructor
  · rintro ⟨p, hp, a, ha, hq⟩
    obtain ⟨s, hs, t, ht, ha⟩ := (hT a).mp ha
    exact ⟨p, s, t, hp, hs, ht, a, ha, hq⟩
  · rintro ⟨p, s, t, hp, hs, ht, a, ha, hq⟩
    exact ⟨p, hp, a, (hT a).mpr ⟨s, hs, t, ht, ha⟩, hq⟩

structure Max_bisim_d (B R z X F : M.Domain) : Prop where
  subset : ∀ q, M.mem q F → M.mem q X
  bisim : Bisim_d M B R z F
  greatest : ∀ G, (∀ q, M.mem q G → M.mem q X) → Bisim_d M B R z G →
    ∀ q, M.mem q G → M.mem q F

/-- 内部幂集分离出的所有双模拟的并，仍然是双模拟。 -/
theorem bisim_max_l (hZF : M.Models ZF) (B R z X : M.Domain) :
    ∃ F, Max_bisim_d M B R z X F := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : UnarySchema 3 := { body := bisim_m (.bound 3) (.bound 2) (.bound 1) (.bound 0) }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  have hc G : M.mem G C ↔ (∀ q, M.mem q G → M.mem q X) ∧ Bisim_d M B R z G := by
    rw [hC G, hP G]
    exact and_congr_right fun _ => bisim_sat_l M hZF.1 (ρ.push G) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  obtain ⟨F, hF⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hg {G} (hG : M.mem G C) : ∀ q, M.mem q G → M.mem q F :=
    fun q hq => (hF q).mpr ⟨G, hG, hq⟩
  refine ⟨F, ⟨?_, ?_, fun G hG hb => hg ((hc G).mpr ⟨hG, hb⟩)⟩⟩
  · intro q hq
    obtain ⟨G, hG, hq⟩ := (hF q).mp hq
    exact ((hc G).mp hG).1 q hq
  · rintro p s t ⟨q, hq, hqF⟩
    obtain ⟨G, hG, hqG⟩ := (hF q).mp hqF
    obtain ⟨hl, hr⟩ := ((hc G).mp hG).2 p s t ⟨q, hq, hqG⟩
    exact ⟨match_mono_l M (hg hG) false hl, match_mono_l M (hg hG) true hr⟩

/-- 最大关系的反向匹配方程：把满足一步匹配的新三元组加入即可。 -/
theorem bisim_unfold_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B R z S X F}
    (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    {p s t} (hp : M.mem p B) (hs : M.mem s S) (ht : M.mem t S) :
    Rel_d M F p s t ↔ Match_d M false B R z F p s t ∧ Match_d M true B R z F p t s := by
  refine ⟨hF.bisim p s t, fun h => ?_⟩
  obtain ⟨q, hq⟩ := triple_exists_l M hE hP p s t
  have hqX := (hX q).mpr ⟨p, s, t, hp, hs, ht, hq⟩
  obtain ⟨G, hG⟩ := set_insert_l M hP hU F q
  have hi r (hr : M.mem r F) : M.mem r G := (hG r).mpr (Or.inl hr)
  have hg : Bisim_d M B R z G := by
    rintro a b c ⟨r, hr, hrG⟩
    rcases (hG r).mp hrG with hrF | rfl
    · have k := hF.bisim a b c ⟨r, hr, hrF⟩
      exact ⟨match_mono_l M hi false k.1, match_mono_l M hi true k.2⟩
    · obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hr hq
      exact ⟨match_mono_l M hi false h.1, match_mono_l M hi true h.2⟩
  have hb r (hr : M.mem r G) : M.mem r X :=
    ((hG r).mp hr).elim (hF.subset r) (fun e => e ▸ hqX)
  exact ⟨q, hq, hF.greatest G hb hg q ((hG q).mpr (Or.inr rfl))⟩

/-- 三元组关系限制到一个闭支撑；匹配到的子名称仍在同一支撑中。 -/
theorem bisim_restrict_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Bisim_d M B R z F) :
    ∃ G, (∀ q, M.mem q G ↔ M.mem q F ∧ M.mem q X) ∧ Bisim_d M B R z G := by
  obtain ⟨G, hG⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) F X
  refine ⟨G, hG, ?_⟩
  rintro p s t ⟨q, hq, hqG⟩
  obtain ⟨hqF, hqX⟩ := (hG q).mp hqG
  obtain ⟨p', s', t', hp, hs, ht, hq'⟩ := (hX q).mp hqX
  obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hq hq'
  have hm (k : Bool) {s t} (hs : M.mem s S) (ht : M.mem t S)
      (h : Match_d M k B R z F p s t) : Match_d M k B R z G p s t := by
    intro a b hab r hr hrb
    obtain ⟨v, d, c, hv, hd, hvc, hvF⟩ := h a b hab r hr hrb
    have ha := (supp_entry_l M hS hs hab).1
    have hdS := (supp_entry_l M hS ht hd).1
    refine ⟨v, d, c, hv, hd, hvc, ?_⟩
    cases k <;> obtain ⟨w, hw, hwF⟩ := hvF
    · exact ⟨w, hw, (hG w).mpr ⟨hwF, (hX w).mpr ⟨v, a, d, hv.1, ha, hdS, hw⟩⟩⟩
    · exact ⟨w, hw, (hG w).mpr ⟨hwF, (hX w).mpr ⟨v, d, a, hv.1, hdS, ha, hw⟩⟩⟩
  have h := hF p s t ⟨q, hq, hqF⟩
  exact ⟨hm false hs ht h.1, hm true ht hs h.2⟩

/-- 任意闭支撑上的最大关系计算全局内部等号力迫；支撑选择不改变结果。 -/
theorem eq_force_local_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    {p s t} (hp : M.mem p B) (hs : M.mem s S) (ht : M.mem t S) :
    Eq_force_d M B R z p s t ↔ Rel_d M F p s t := by
  constructor
  · rintro ⟨_, G, hg, q, hq, hqG⟩
    obtain ⟨H, hH, hh⟩ := bisim_restrict_l M hZF hS hX hg
    have hi r (hr : M.mem r H) := ((hH r).mp hr).2
    exact ⟨q, hq, hF.greatest H hi hh q
      ((hH q).mpr ⟨hqG, (hX q).mpr ⟨p, s, t, hp, hs, ht, hq⟩⟩)⟩
  · exact fun h => ⟨hp, F, hF.bisim, h⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部原子力迫的递归方程

最大双模拟在任意闭支撑上计算同一个等号谓词。将局部关系换回这个谓词，
得到通常的稠密匹配递归；隶属力迫则是带权等号匹配的稠密闭包。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Eq_match_d (k : Bool) (B R z p s t : M.Domain) : Prop :=
  ∀ a b, Entry_d M a b s → ∀ q, Below_d M B R z q p → Entry_d M q b R →
    ∃ r d c, Below_d M B R z r q ∧ Entry_d M d c t ∧ Entry_d M r c R ∧
      (if k then Eq_force_d M B R z r d a else Eq_force_d M B R z r a d)

def Mem_force_d (B R z p s t : M.Domain) : Prop := M.mem p B ∧
  ∀ q, Below_d M B R z q p → ∃ r a b,
    Below_d M B R z r q ∧ Entry_d M a b t ∧ Entry_d M r b R ∧ Eq_force_d M B R z r s a

def mem_force_m {n} (B R z p s t : Term n) : Formula 1 n :=
  .conj (.mem p B) (.forallE (.imp (below_m B.weaken R.weaken z.weaken .newest p.weaken)
    (.existsE (.existsE (.existsE (.conj
      (below_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
        z.weaken.weaken.weaken.weaken (.bound 2) (.bound 3))
      (.conj (entry_m (.bound 1) .newest t.weaken.weaken.weaken.weaken)
        (.conj (entry_m (.bound 2) .newest R.weaken.weaken.weaken.weaken)
          (eq_force_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            z.weaken.weaken.weaken.weaken (.bound 2) s.weaken.weaken.weaken.weaken (.bound 1))))))))))
derive_free_closed mem_force_m

theorem mem_force_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z p s t : Term n) :
    Formula.satisfies ρ (mem_force_m B R z p s t) ↔
      Mem_force_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [mem_force_m, Mem_force_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    below_sat_l M hE, entry_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push,
    Term.eval_bound_three_push]

private theorem match_local_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    (k : Bool) {p s t} (hs : M.mem s S) (ht : M.mem t S) :
    Match_d M k B R z F p s t ↔ Eq_match_d M k B R z p s t := by
  have he {r a d} (hr : M.mem r B) (ha : M.mem a S) (hd : M.mem d S) :
      (if k then Rel_d M F r d a else Rel_d M F r a d) ↔
      (if k then Eq_force_d M B R z r d a else Eq_force_d M B R z r a d) := by
    cases k
    · exact (eq_force_local_l M hZF hS hX hF hr ha hd).symm
    · exact (eq_force_local_l M hZF hS hX hF hr hd ha).symm
  constructor
  · intro h a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, hF⟩ := h a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he hr.1 (supp_entry_l M hS hs hab).1
      (supp_entry_l M hS ht hd).1).mp hF⟩
  · intro h a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, hE⟩ := h a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he hr.1 (supp_entry_l M hS hs hab).1
      (supp_entry_l M hS ht hd).1).mpr hE⟩

/-- 等号的双向递归方程由实际最大双模拟证明，不把该方程作为输入假设。 -/
theorem eq_force_unfold_l (hZF : M.Models ZF) {B R z p s t}
    (hs : Name_d M B s) (ht : Name_d M B t) : Eq_force_d M B R z p s t ↔
      M.mem p B ∧ Eq_match_d M false B R z p s t ∧ Eq_match_d M true B R z p t s := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht
  obtain ⟨X, hX⟩ := triple_carrier_l M hZF B S
  obtain ⟨F, hF⟩ := bisim_max_l M hZF B R z X
  have he hp : Eq_force_d M B R z p s t ↔
      Eq_match_d M false B R z p s t ∧ Eq_match_d M true B R z p t s :=
    (eq_force_local_l M hZF hS hX hF hp hsS htS).trans
      ((bisim_unfold_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
        (KP.exists_union (ZF.modelsKP hZF)) hX hF hp hsS htS).trans
          (and_congr (match_local_l M hZF hS hX hF false hsS htS)
            (match_local_l M hZF hS hX hF true htS hsS)))
  exact ⟨fun h => ⟨h.1, (he h.1).mp h⟩, fun h => (he h.1).mpr h.2⟩

/-- 原子真值是条件集内的实际可定义子集。 -/
theorem eq_force_set_l (hZF : M.Models ZF) (B R z s t : M.Domain) :
    ∃ E, ∀ p, M.mem p E ↔ Eq_force_d M B R z p s t := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨E, fun p => (hE p).trans ?_⟩
  have h := eq_force_sat_l M hZF.1 (ρ.push p) (.bound 5) (.bound 4) (.bound 3)
    (.bound 0) (.bound 2) (.bound 1)
  exact (and_congr_right fun _ => h).trans ⟨And.right, fun h => ⟨h.1, h⟩⟩

end YesMetaZFC.Model.Forcing.Internal
