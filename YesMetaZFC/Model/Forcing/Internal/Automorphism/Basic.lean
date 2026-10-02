import YesMetaZFC.Model.Forcing.Stage.NameMap.Composition
import YesMetaZFC.Model.Forcing.Stage.NameMap.Identity
import YesMetaZFC.SetTheory.Card.Basic

/-! # 条件自同构的内部集合图

自同构在整个条件集上双射，并保持序关系和排除值。零标签也保留，因此其名称
作用满足严格的恒等与逆律。所有图均为模型中的集合；不选取外部作用函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

structure Aut_d (B R z F : M.Domain) : Prop where
  graph : ∀ v, M.mem v F → ∃ p q, KPair_d M v p q
  domain : ∀ p q, Entry_d M p q F → M.mem p B ∧ M.mem q B
  total : ∀ p, M.mem p B → ∃ q, Entry_d M p q F
  onto : ∀ q, M.mem q B → ∃ p, Entry_d M p q F
  functional : ∀ p q r, Entry_d M p q F → Entry_d M p r F → q = r
  injective : ∀ p q r, Entry_d M p r F → Entry_d M q r F → p = q
  order : ∀ p q s t, Entry_d M p s F → Entry_d M q t F →
    (Entry_d M p q R ↔ Entry_d M s t R)
  zero : ∀ p q, Entry_d M p q F → (p = z ↔ q = z)

def aut_m {n} (B R z F : Term n) : Formula 1 n :=
  .conj (Formula.isBijectionFromTo kpair_convention_l F B B)
    (.conj
      (.forallE <| .forallE <| .forallE <| .forallE <| .imp
        (entry_m (.bound 3) (.bound 1) F.weaken.weaken.weaken.weaken) <| .imp
        (entry_m (.bound 2) .newest F.weaken.weaken.weaken.weaken)
        (.iff (entry_m (.bound 3) (.bound 2) R.weaken.weaken.weaken.weaken)
          (entry_m (.bound 1) .newest R.weaken.weaken.weaken.weaken)))
      (.forallE <| .forallE <| .imp (entry_m (.bound 1) .newest F.weaken.weaken)
        (.iff (Formula.extensionalEq (.bound 1) z.weaken.weaken)
          (Formula.extensionalEq .newest z.weaken.weaken))))
derive_free_closed aut_m

variable {M} {B R z F G : M.Domain}

theorem aut_bij_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (h : Aut_d M B R z F) :
    M.IsSetBijectionFromTo (kpair_interpretation_l M hE hP) F B B := by
  refine ⟨⟨⟨⟨h.graph, h.functional⟩, ?_, ?_⟩, h.injective⟩, ?_⟩
  · intro p
    exact ⟨h.total p, fun ⟨q, hpq⟩ => (h.domain p q hpq).1⟩
  · intro p hp
    obtain ⟨q, hpq⟩ := h.total p hp
    exact ⟨q, (h.domain p q hpq).2, hpq⟩
  · intro q hq
    obtain ⟨p, hpq⟩ := h.onto q hq
    exact ⟨p, (h.domain p q hpq).1, hpq⟩

theorem aut_of_bij_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (h : M.IsSetBijectionFromTo (kpair_interpretation_l M hE hP) F B B)
    (ho : ∀ p q s t, Entry_d M p s F → Entry_d M q t F →
      (Entry_d M p q R ↔ Entry_d M s t R))
    (hz : ∀ p q, Entry_d M p q F → (p = z ↔ q = z)) : Aut_d M B R z F :=
  ⟨h.1.1.1.1, fun _ _ hpq => ⟨h.1.1.input_mem_of_pairMember hpq, h.1.1.output_mem_of_pairMember hpq⟩,
    fun p hp => (h.1.1.2.2 p hp).elim fun q hq => ⟨q, hq.2⟩,
    fun q hq => (h.2 q hq).elim fun p hp => ⟨p, hp.2⟩, h.1.1.1.2, h.1.2, ho, hz⟩

theorem aut_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F : Term n) :
    Formula.satisfies ρ (aut_m B R z F) ↔
      Aut_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) := by
  have entry {k} (η : Env M k) (p q F : Term k) :
      Formula.satisfies η (Formula.orderedPairMem kpair_convention_l p q F) ↔
        Entry_d M (p.eval η) (q.eval η) (F.eval η) := entry_sat_l M hE η p q F
  have graph {k} (η : Env M k) (F : Term k) :
      Formula.satisfies η (Formula.isRelation kpair_convention_l F) ↔
        ∀ v, M.mem v (F.eval η) → ∃ p q, KPair_d M v p q := by
    simp only [Formula.isRelation, kpair_convention_l, Formula.satisfies_forallMem_iff,
      Formula.satisfies_exists_iff, kpair_sat_l M hE]
    rfl
  simp only [aut_m, Formula.isBijectionFromTo, Formula.isInjectionFromTo,
    Formula.isFunctionFromTo, Formula.isFunction, Formula.isDomain, Formula.isInjective,
    Formula.isSurjectiveOnto, graph, entry,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    entry_sat_l M hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨⟨⟨⟨⟨hg, hf⟩, hd, ht⟩, hi⟩, hs⟩, ho, hz⟩
    have dom p q (hpq : Entry_d M p q (F.eval ρ)) : M.mem p (B.eval ρ) ∧ M.mem q (B.eval ρ) := by
      have hp := (hd p).mpr ⟨q, hpq⟩
      obtain ⟨r, hr, hpr⟩ := ht p hp
      have he : r = q := hf p r q ⟨hpr, hpq⟩
      exact ⟨hp, he ▸ hr⟩
    exact ⟨hg, dom, fun p hp => (hd p).mp hp,
      fun q hq => (hs q hq).elim fun p hp => ⟨p, hp.2⟩,
      fun p q r hp hq => hf p q r ⟨hp, hq⟩, fun p q r hp hq => hi p q r ⟨hp, hq⟩, ho, hz⟩
  · intro h
    refine ⟨⟨⟨⟨⟨h.graph, fun p q r hh => h.functional p q r hh.1 hh.2⟩, ?_, ?_⟩,
      fun p q r hh => h.injective p q r hh.1 hh.2⟩, ?_⟩, h.order, h.zero⟩
    · intro p
      exact ⟨h.total p, fun ⟨q, hpq⟩ => (h.domain p q hpq).1⟩
    · intro p hp
      obtain ⟨q, hpq⟩ := h.total p hp
      exact ⟨q, (h.domain p q hpq).2, hpq⟩
    · intro q hq
      obtain ⟨p, hpq⟩ := h.onto q hq
      exact ⟨p, (h.domain p q hpq).1, hpq⟩

theorem aut_below_l (h : Aut_d M B R z F) {p q s t}
    (hps : Entry_d M p s F) (hqt : Entry_d M q t F) :
    Below_d M B R z q p ↔ Below_d M B R z t s := by
  have hd := h.domain q t hqt
  exact ⟨fun hq => ⟨hd.2, fun he => hq.2.1 ((h.zero q t hqt).mpr he),
      (h.order q p t s hqt hps).mp hq.2.2⟩,
    fun ht => ⟨hd.1, fun he => ht.2.1 ((h.zero q t hqt).mp he),
      (h.order q p t s hqt hps).mpr ht.2.2⟩⟩

/-- 恒等图是任意条件结构的实际自同构，不需要预序公理。 -/
theorem aut_id_l (hZF : M.Models ZF)
    (B R z : M.Domain) : ∃ F, Aut_d M B R z F ∧
      ∀ p q, Entry_d M p q F ↔ M.mem p B ∧ q = p := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => B⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  have hφ p q : φ.denote ρ p q ↔ q = p := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun p _ => ⟨p, (hφ p p).mpr rfl⟩)
    (fun p _ q r hq hr => ((hφ p q).mp hq).trans ((hφ p r).mp hr).symm)
    (fun p q hp hq => ((hφ p q).mp hq).symm ▸ hp)
  have he p q : Entry_d M p q F ↔ M.mem p B ∧ q = p :=
    (hf p q).trans (and_congr_right fun _ => hφ p q)
  refine ⟨F, aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨hF, ?_⟩, ?_⟩ ?_ ?_, he⟩
  · intro p q t hp hq
    exact ((he p t).mp hp).2.symm.trans ((he q t).mp hq).2
  · exact fun q hq => ⟨q, hq, (he q q).mpr ⟨hq, rfl⟩⟩
  · intro p q s t hs ht
    rw [((he p s).mp hs).2, ((he q t).mp ht).2]
  · intro p q hpq
    rw [((he p q).mp hpq).2]

/-- 逆图仍由模型内集合运算取得，并保留逐条目的反向刻画。 -/
theorem aut_inverse_l (hZF : M.Models ZF) (h : Aut_d M B R z F) :
    ∃ G, Aut_d M B R z G ∧ ∀ p q, Entry_d M p q G ↔ Entry_d M q p F := by
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  obtain ⟨G, hG, hg⟩ := ZF.exists_inverseBijectionWithPairs hZF
    (kpair_interpretation_l M hZF.1 hP) (aut_bij_l hZF.1 hP h)
  exact ⟨G, aut_of_bij_l hZF.1 hP hG (fun p q s t hs ht =>
    (h.order s t p q ((hg p s).mp hs) ((hg q t).mp ht)).symm)
    (fun p q hpq => (h.zero q p ((hg p q).mp hpq)).symm), hg⟩

/-- 复合图及其精确条目同时构造，供名称作用的复合律直接调用。 -/
theorem aut_comp_l (hZF : M.Models ZF) (h : Aut_d M B R z F) (k : Aut_d M B R z G) :
    ∃ H, Aut_d M B R z H ∧
      ∀ p r, Entry_d M p r H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q r G := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push G
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 4))
      (entry_m .newest (.bound 1) (.bound 3))) }
  have hφ p r : φ.denote ρ p r ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q r G := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨H, hH, hh⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (fun p hp => by
    obtain ⟨q, hpq⟩ := h.total p hp
    obtain ⟨r, hqr⟩ := k.total q (h.domain p q hpq).2
    exact ⟨r, (hφ p r).mpr ⟨q, hpq, hqr⟩⟩) (by
      intro p _ r s hr hs
      obtain ⟨q, hpq, hqr⟩ := (hφ p r).mp hr
      obtain ⟨q', hpq', hq's⟩ := (hφ p s).mp hs
      have he := h.functional p q q' hpq hpq'
      subst q'
      exact k.functional q r s hqr hq's)
    (fun p r _ hr => (hφ p r).mp hr |>.elim fun q hq => (k.domain q r hq.2).2)
  have he p r : Entry_d M p r H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q r G := by
    change M.PairMember I p r H ↔ _
    rw [hh p r, hφ]
    exact ⟨And.right, fun ⟨q, hpq, hqr⟩ => ⟨(h.domain p q hpq).1, q, hpq, hqr⟩⟩
  refine ⟨H, aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨hH, ?_⟩, ?_⟩ ?_ ?_, he⟩
  · intro p q r hp hq
    obtain ⟨s, hps, hsr⟩ := (he p r).mp hp
    obtain ⟨t, hqt, htr⟩ := (he q r).mp hq
    have ht := k.injective s t r hsr htr
    exact h.injective p q s hps (ht ▸ hqt)
  · intro r hr
    obtain ⟨q, hqr⟩ := k.onto r hr
    obtain ⟨p, hpq⟩ := h.onto q (k.domain q r hqr).1
    exact ⟨p, (h.domain p q hpq).1, (he p r).mpr ⟨q, hpq, hqr⟩⟩
  · intro p q s t hps hqt
    obtain ⟨a, hpa, has⟩ := (he p s).mp hps
    obtain ⟨b, hqb, hbt⟩ := (he q t).mp hqt
    exact (h.order p q a b hpa hqb).trans (k.order a b s t has hbt)
  · intro p q hpq
    obtain ⟨r, hpr, hrq⟩ := (he p q).mp hpq
    exact (h.zero p r hpr).trans (k.zero r q hrq)

end YesMetaZFC.Model.Forcing.Internal
