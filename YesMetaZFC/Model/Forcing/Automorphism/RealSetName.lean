import YesMetaZFC.Model.Forcing.Stage.NameMap.Composition
import YesMetaZFC.Model.Forcing.Stage.NameMap.Identity
import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.Model.Forcing.Stage.NameMap.Check
import YesMetaZFC.Model.Forcing.Names.CheckPools
import YesMetaZFC.Model.Forcing.Truth.OrderCongruence
import YesMetaZFC.Model.Forcing.Stage.Extension
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism

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

/-! ## 自同构在内部名称上的严格作用

直接使用已有 Nmap 递归图：每个 (σ,p) 变成 (πσ,πp)。全标签恒等图严格固定名称，
逆图给出真正的逆作用。check 名称的基条件也随之移动；基条件固定时名称本身固定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z F G : M.Domain}

/-- 逆作用恢复原名称对象，结论强于被迫相等。 -/
theorem aut_nmap_inverse_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    (hg : ∀ p q, Entry_d M p q G ↔ Entry_d M q p F)
    {x s} (hx : Name_d M B x) (hs : Nmap_d M F x s) : Nmap_d M G s x := by
  obtain ⟨H, _, hH⟩ := aut_id_l hZF B R z
  have hc p q : Entry_d M p q H ↔ ∃ a, Entry_d M p a F ∧ Entry_d M a q G := by
    rw [hH]
    constructor
    · rintro ⟨hp, rfl⟩
      obtain ⟨a, ha⟩ := h.total q hp
      exact ⟨a, ha, (hg a q).mpr ha⟩
    · rintro ⟨a, hpa, haq⟩
      exact ⟨(h.domain p a hpa).1, h.injective q p a ((hg a q).mp haq) hpa⟩
  obtain ⟨t, ht⟩ := nmap_exists_l M hZF G s
  have he := nmap_unique_l M hZF.1 (check_ind_l M hZF) H x t x
    (nmap_comp_l hZF hc hs ht) (nmap_identity_l hZF hH hx)
  exact he ▸ ht

theorem aut_nmap_injective_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y t} (hx : Name_d M B x) (hy : Name_d M B y)
    (ht : Nmap_d M F x t) (hu : Nmap_d M F y t) : x = y := by
  obtain ⟨G, _, hg⟩ := aut_inverse_l hZF h
  exact nmap_unique_l M hZF.1 (check_ind_l M hZF) G t x y
    (aut_nmap_inverse_l hZF h hg hx ht) (aut_nmap_inverse_l hZF h hg hy hu)

/-- 所有内部名称都有原像；量词搬运不要求选择一个全局名称函数。 -/
theorem aut_nmap_onto_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {t} (ht : Name_d M B t) : ∃ x, Name_d M B x ∧ Nmap_d M F x t := by
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  obtain ⟨x, hx⟩ := nmap_exists_l M hZF G t
  exact ⟨x, nmap_name_l M hZF (fun p q hpq => (k.domain p q hpq).2) hx,
    aut_nmap_inverse_l hZF k (fun p q => (hg q p).symm) ht hx⟩

/-- 实际复合自同构的名称作用恰好是两次作用。 -/
theorem aut_nmap_comp_l (hZF : M.Models ZF) (h : Aut_d M B R z F) (k : Aut_d M B R z G) :
    ∃ H, Aut_d M B R z H ∧
      (∀ p r, Entry_d M p r H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q r G) ∧
      ∀ x t, Nmap_d M H x t ↔ ∃ s, Nmap_d M F x s ∧ Nmap_d M G s t := by
  obtain ⟨H, hH, he⟩ := aut_comp_l hZF h k
  refine ⟨H, hH, he, fun x t => ⟨?_, ?_⟩⟩
  · intro ht
    obtain ⟨s, hs⟩ := nmap_exists_l M hZF F x
    obtain ⟨a, ha⟩ := nmap_exists_l M hZF G s
    have he := nmap_unique_l M hZF.1 (check_ind_l M hZF) H x a t (nmap_comp_l hZF he hs ha) ht
    exact ⟨s, hs, he ▸ ha⟩
  · rintro ⟨s, hs, ht⟩
    exact nmap_comp_l hZF he hs ht

theorem aut_check_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {b c x s t}
    (hbc : Entry_d M b c F) (hs : Check_d M b x s) (ht : Check_d M c x t) : Nmap_d M F s t :=
  nmap_check_l hZF (fun d => ⟨fun hd => h.functional b d c hd hbc, fun he => he ▸ hbc⟩) hs ht

/-- 固定基条件时，全部地模型对象的 check 名称逐对象固定。 -/
theorem aut_check_fixed_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {b x t}
    (hb : Entry_d M b b F) (ht : Check_d M b x t) : Nmap_d M F t t :=
  aut_check_l hZF h hb ht ht

end YesMetaZFC.Model.Forcing.Internal

/-! ## 条件自同构保持原子力迫

在目标名称的闭支撑上分离源等号关系的像，得到实际集合双模拟。任意目标加强
由逆条件拉回，再把源匹配送到目标。此论证只需双射保序，不额外消费预序公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

private def Aut_eq_d (B R z F q s t : M.Domain) : Prop := ∃ p x y,
  Entry_d M p q F ∧ Name_d M B x ∧ Name_d M B y ∧
    Nmap_d M F x s ∧ Nmap_d M F y t ∧ Eq_force_d M B R z p x y

private def aut_eq_m {n} (B R z F q s t : Term n) : Formula 1 n :=
  .existsE <| .existsE <| .existsE <|
    .conj (entry_m (.bound 2) q.weaken.weaken.weaken F.weaken.weaken.weaken) <|
    .conj (name_m B.weaken.weaken.weaken (.bound 1)) <|
    .conj (name_m B.weaken.weaken.weaken .newest) <|
    .conj (nmap_m F.weaken.weaken.weaken (.bound 1) s.weaken.weaken.weaken) <|
    .conj (nmap_m F.weaken.weaken.weaken .newest t.weaken.weaken.weaken)
      (eq_force_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        (.bound 2) (.bound 1) .newest)
derive_free_closed aut_eq_m

private theorem aut_eq_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F q s t : Term n) :
    Formula.satisfies ρ (aut_eq_m B R z F q s t) ↔
      Aut_eq_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [aut_eq_m, Aut_eq_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, name_sat_l M hE, nmap_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable {B R z F : M.Domain}

theorem aut_eq_push_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F)
    (he : Eq_force_d M B R z p x y) : Eq_force_d M B R z q s t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have name {a b} (hab : Nmap_d M F a b) : Name_d M B b :=
    nmap_name_l M hZF (fun c d hcd => (h.domain c d hcd).2) hab
  obtain ⟨W, hsW, htW, hW⟩ := name_support_l M hP (KP.exists_union (ZF.modelsKP hZF)) (name hs) (name ht)
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F
  let φ : BinarySchema 5 := {
    body := aut_eq_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := rel_separation_l hZF φ ρ B W
  have hk v a b : Rel_d M K v a b ↔ M.mem v B ∧ M.mem a W ∧ M.mem b W ∧ Aut_eq_d B R z F v a b := by
    simpa only [BinarySchema.denote, φ, aut_eq_sat_l hZF.1] using! hK v a b
  have symm {v a b} (hab : Rel_d M K v a b) : Rel_d M K v b a := by
    obtain ⟨hv, ha, hb, p, x, y, hpv, hx, hy, hxa, hyb, he⟩ := (hk v a b).mp hab
    exact (hk v b a).mpr ⟨hv, hb, ha, p, y, x, hpv, hy, hx, hyb, hxa, eq_force_symm_l hZF hx hy he⟩
  have forth v a b (hab : Rel_d M K v a b) : Match_d M false B R z K v a b := by
    obtain ⟨_, haW, hbW, p, x, y, hpv, hx, hy, hxa, hyb, he⟩ := (hk v a b).mp hab
    intro c d hcd r hr hrd
    obtain ⟨x', d₀, hx'd, hx'c, hd₀d⟩ := (nmap_entry_l M hZF.1 hI hP hxa c d).mp hcd
    obtain ⟨r₀, hr₀r⟩ := h.onto r hr.1
    obtain ⟨r₁, y', e₀, hr₁, hy'e, hr₁e, hx'y'⟩ :=
      ((eq_force_unfold_l M hZF hx hy).mp he).2.1 x' d₀ hx'd r₀
        ((aut_below_l h hpv hr₀r).mpr hr) ((h.order r₀ d₀ r d hr₀r hd₀d).mpr hrd)
    obtain ⟨r₂, hr₁r₂⟩ := h.total r₁ hr₁.1
    obtain ⟨b', hy'b'⟩ := nmap_exists_l M hZF F y'
    obtain ⟨e, he₀e⟩ := h.total e₀ (name_entry_l M hy hy'e).2
    have hb'e := (nmap_entry_l M hZF.1 hI hP hyb b' e).mpr ⟨y', e₀, hy'e, hy'b', he₀e⟩
    exact ⟨r₂, b', e, (aut_below_l h hr₀r hr₁r₂).mp hr₁, hb'e,
      (h.order r₁ e₀ r₂ e hr₁r₂ he₀e).mp hr₁e,
      (hk r₂ c b').mpr ⟨(h.domain r₁ r₂ hr₁r₂).2, (supp_entry_l M hW haW hcd).1,
        (supp_entry_l M hW hbW hb'e).1, r₁, x', y', hr₁r₂,
        (name_entry_l M hx hx'd).1, (name_entry_l M hy hy'e).1, hx'c, hy'b', hx'y'⟩⟩
  refine ⟨(h.domain p q hpq).2, K, ?_, (hk q s t).mpr
    ⟨(h.domain p q hpq).2, hsW, htW, p, x, y, hpq, hx, hy, hs, ht, he⟩⟩
  intro v a b hab
  refine ⟨forth v a b hab, ?_⟩
  intro c d hcd r hr hrd
  obtain ⟨w, e, f, hw, hef, hwf, hce⟩ := forth v b a (symm hab) c d hcd r hr hrd
  exact ⟨w, e, f, hw, hef, hwf, symm hce⟩

theorem aut_eq_force_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Eq_force_d M B R z p x y ↔ Eq_force_d M B R z q s t := by
  refine ⟨aut_eq_push_l hZF h hx hy hs ht hpq, fun he => ?_⟩
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  exact aut_eq_push_l hZF k (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) hs)
    (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) ht)
    (aut_nmap_inverse_l hZF h hg hx hs) (aut_nmap_inverse_l hZF h hg hy ht) ((hg q p).mpr hpq) he

theorem aut_mem_push_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F)
    (hm : Mem_force_d M B R z p x y) : Mem_force_d M B R z q s t := by
  refine ⟨(h.domain p q hpq).2, fun r hr => ?_⟩
  obtain ⟨r₀, hr₀r⟩ := h.onto r hr.1
  obtain ⟨v, a, b, hv, hab, hvb, he⟩ := hm.2 r₀ ((aut_below_l h hpq hr₀r).mpr hr)
  obtain ⟨v', hvv'⟩ := h.total v hv.1
  obtain ⟨a', haa'⟩ := nmap_exists_l M hZF F a
  obtain ⟨b', hbb'⟩ := h.total b (name_entry_l M hy hab).2
  exact ⟨v', a', b', (aut_below_l h hr₀r hvv').mp hv,
    (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht a' b').mpr
      ⟨a, b, hab, haa', hbb'⟩, (h.order v b v' b' hvv' hbb').mp hvb,
    aut_eq_push_l hZF h hx (name_entry_l M hy hab).1 hs haa' hvv' he⟩

theorem aut_mem_force_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y s t p q} (hx : Name_d M B x) (hy : Name_d M B y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Mem_force_d M B R z p x y ↔ Mem_force_d M B R z q s t := by
  refine ⟨aut_mem_push_l hZF h hx hy hs ht hpq, fun he => ?_⟩
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  exact aut_mem_push_l hZF k (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) hs)
    (nmap_name_l M hZF (fun a b hab => (h.domain a b hab).2) ht)
    (aut_nmap_inverse_l hZF h hg hx hs) (aut_nmap_inverse_l hZF h hg hy ht) ((hg q p).mpr hpq) he

end YesMetaZFC.Model.Forcing.Internal

/-! ## 检查子集名字库的自同构不变性

检查基条件固定时，各直接子名字逐个固定，系数沿原条件自同构双射。
正反向都在同一个实际幂集库内完成，不假设所需名字已被枚举覆盖。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {B R z F b D W : M.Domain}
  (aut : Aut_d M B R z F) (fixed : Entry_d M b b F) (pool : Ck_pool_d B b D W)
include hZF aut fixed pool

theorem Ck_pool_d.aut_image_l {s t : M.Domain} (hs : M.mem s W) (image : Nmap_d M F s t) : M.mem t W := by
  apply (pool t).mpr
  intro v hv
  obtain ⟨a,p,c,q,⟨u,ua,hu⟩,ac,pq,pair⟩ := (nmap_mem_l M hZF.1 (check_ind_l M hZF) image v).mp hv
  obtain ⟨a',p',d,ua',_,hd,check⟩ := (pool s).mp hs u hu
  obtain ⟨ea,ep⟩ := kpair_injective_l M ua ua'
  subst a' p'
  have eq := nmap_unique_l M hZF.1 (check_ind_l M hZF) F a c a ac (aut_check_fixed_l hZF aut fixed check)
  exact ⟨c,q,d,pair,(aut.domain p q pq).2,hd,eq.symm ▸ check⟩

theorem Ck_pool_d.aut_onto_l {t : M.Domain} (ht : M.mem t W) : ∃ s, M.mem s W ∧ Nmap_d M F s t := by
  obtain ⟨G,inverse,entries⟩ := aut_inverse_l hZF aut
  obtain ⟨s,st⟩ := nmap_exists_l M hZF G t
  have fixed' := (entries b b).mpr fixed
  exact ⟨s,pool.aut_image_l hZF inverse fixed' ht st,
    aut_nmap_inverse_l hZF inverse (fun p q => (entries q p).symm)
      (pool.name_l hZF (aut.domain b b fixed).1 ht) st⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部原公式的自同构不变性

否定通过条件双射搬运，量词通过名称的严格逆作用搬运。正文是原 Project 公式，
参数作用仍由实际内部 Nmap 图见证；不假定外部名称域良基或存在全局代表选择。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z F : M.Domain}

private theorem aut_neg_l (h : Aut_d M B R z F) {P Q : M.Domain → Prop}
    (he : ∀ p q, Entry_d M p q F → (P p ↔ Q q)) {p q} (hpq : Entry_d M p q F) :
    Neg_d M B R z P p ↔ Neg_d M B R z Q q := by
  constructor
  · intro hn s hs hQ
    obtain ⟨r, hrs⟩ := h.onto s hs.1
    exact hn r ((aut_below_l h hpq hrs).mpr hs) ((he r s hrs).mpr hQ)
  · intro hn r hr hP
    obtain ⟨s, hrs⟩ := h.total r hr.1
    exact hn s ((aut_below_l h hpq hrs).mp hr) ((he r s hrs).mp hP)

private theorem aut_all_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {P Q : M.Domain → Prop}
    (he : ∀ x y, Name_d M B x → Nmap_d M F x y → (P x ↔ Q y)) :
    (∀ x, Name_d M B x → P x) ↔ ∀ y, Name_d M B y → Q y := by
  constructor
  · intro hP y hy
    obtain ⟨x, hx, hxy⟩ := aut_nmap_onto_l hZF h hy
    exact (he x y hx hxy).mp (hP x hx)
  · intro hQ x hx
    obtain ⟨y, hxy⟩ := nmap_exists_l M hZF F x
    exact (he x y hx hxy).mpr (hQ y (nmap_name_l M hZF (fun p q hpq => (h.domain p q hpq).2) hxy))

/-- 同时作用于条件和全部名称参数，保持任意原公式的力迫关系。 -/
theorem aut_forces_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (ρ η : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
    (hρη : ∀ t : Term n, Nmap_d M F (t.eval ρ) (t.eval η))
    {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η q := by
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
      {x} (hx : Name_d M B x) : ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push x)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hx (fun i => hρ (.bound i)) i
  have pair {n} {ρ η : Env M n} (hρη : ∀ t : Term n, Nmap_d M F (t.eval ρ) (t.eval η))
      {x y} (hxy : Nmap_d M F x y) :
      ∀ t : Term (n+1), Nmap_d M F (t.eval (ρ.push x)) (t.eval (η.push y)) := by
    intro t
    cases t with
    | free i => exact hρη (.free i)
    | bound i => exact Fin.cases hxy (fun i => hρη (.bound i)) i
  have hn := @aut_neg_l M B R z F h
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ p q, Entry_d M p q F → (P p ↔ Q q))
      (k : ∀ p q, Entry_d M p q F → (V p ↔ W q)) :=
    fun p q hpq => and_congr (h p q hpq) (k p q hpq)
  induction φ generalizing p q with
  | falsum => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact aut_mem_force_l hZF h (hρ s) (hρ t) (hρη s) (hρη t) hpq
  | atom r _ ts =>
    cases r
    · simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact aut_eq_force_l hZF h (hρ (ts 0)) (hρ (ts 1)) (hρη (ts 0)) (hρη (ts 1)) hpq
    · simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      apply aut_all_l hZF h
      intro x y hx hxy
      have hm (t : Term _) (p q) (hpq : Entry_d M p q F) :=
        aut_mem_force_l hZF h hx (hρ t) hxy (hρη t) hpq
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (fun _ _ h => hn (hm (ts 1)) h)) hpq
  | neg φ ih =>
    simpa only [forces_neg_l hZF.1] using hn (fun _ _ h => ih ρ η hρ hρη h) hpq
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using and_congr (ih ρ η hρ hρη hpq) (jh ρ η hρ hρη hpq)
  | disj φ ψ ih jh =>
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (fun _ _ h => hn (fun _ _ h => ih ρ η hρ hρη h) h)
        (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq
  | imp φ ψ ih jh =>
    simpa only [forces_imp_l hZF.1] using
      hn (hc (fun _ _ h => ih ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq
  | iff φ ψ ih jh =>
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1] using
      and_congr
        (hn (hc (fun _ _ h => ih ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => jh ρ η hρ hρη h) h)) hpq)
        (hn (hc (fun _ _ h => jh ρ η hρ hρη h) (fun _ _ h => hn (fun _ _ h => ih ρ η hρ hρη h) h)) hpq)
  | forallE φ ih =>
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    exact aut_all_l hZF h (fun x y hx hxy => ih (ρ.push x) (η.push y) (push hρ hx) (pair hρη hxy) hpq)
  | existsE φ ih =>
    simp only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d]
    simpa only [Neg_d] using hn (fun _ _ hpq => aut_all_l hZF h (fun x y hx hxy => hn
      (fun _ _ hpq => ih (ρ.push x) (η.push y) (push hρ hx) (pair hρη hxy) hpq) hpq)) hpq

/-- 自由闭合正文只需有限 bound 参数的名称及作用证书。 -/
theorem aut_forces_closed_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (hφ : φ.FreeClosed) (ρ η : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i))
    (hρη : ∀ i, Nmap_d M F (ρ.bound i) (η.bound i)) {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η q := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hn := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  obtain ⟨v, hv⟩ := nmap_exists_l M hZF F e
  let ρ' : Env M n := ⟨ρ.bound, fun _ => e⟩
  let η' : Env M n := ⟨η.bound, fun _ => v⟩
  have hρ' (t : Term n) : Name_d M B (t.eval ρ') := by
    cases t with
    | free _ => exact hn
    | bound i => exact hρ i
  have hρη' (t : Term n) : Nmap_d M F (t.eval ρ') (t.eval η') := by
    cases t with
    | free _ => exact hv
    | bound i => exact hρη i
  exact (forces_env_l hZF.1 φ hφ ρ ρ' (fun _ => rfl) p).trans
    ((aut_forces_l hZF h φ ρ' η' hρ' hρη' hpq).trans
      (forces_env_l hZF.1 φ hφ η' η (fun _ => rfl) q))

/-- 固定基条件后，带任意有限地参数的力迫真值沿条件自同构保持。 -/
theorem aut_check_forces_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {a n}
    (φ : Formula a n) (hφ : φ.FreeClosed) (ρ : Env M n) {b}
    (hb : Entry_d M b b F) (hρ : ∀ i, ∃ x, Check_d M b x (ρ.bound i))
    {p q} (hpq : Entry_d M p q F) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ ρ q :=
  aut_forces_closed_l hZF h φ hφ ρ ρ
    (fun i => (hρ i).elim fun _ hx => check_name_l M (check_range_l M hZF) (h.domain b b hb).1 hx)
    (fun i => (hρ i).elim fun _ hx => aut_check_fixed_l hZF h hb hx) hpq

end YesMetaZFC.Model.Forcing.Internal

/-! ## 条件自同构保留实际泛型扩张及名字值

全部条件均为正的集合偏序使用载体本身作为排除值。
自同构的名称满射把原有阶段嵌入提升为满同构；原地参数和每个运输名字的值均保持。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} {B R F : M.Domain}

theorem Aut_d.regular_l (h : Aut_d M B R B F) (O : Cond_order_d M B R B) (hZF : M.Models ZF) :
    Reg_embed_d M B R B B R B F := by
  have nz {p} (hp : M.mem p B) : p ≠ B :=
    fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  refine ⟨h.graph,fun p hp _ => h.total p hp,
    fun p q pq => ⟨(h.domain p q pq).1,nz (h.domain p q pq).1,
      (h.domain p q pq).2,nz (h.domain p q pq).2⟩,
    h.functional,h.injective,fun p q s t ps qt => (h.order p q s t ps qt).symm,?_,?_⟩
  · intro p q s t ps qt
    constructor
    · rintro ⟨u,us,ut⟩
      obtain ⟨r,ru⟩ := h.onto u us.1
      exact ⟨r,(aut_below_l h ps ru).mpr us,(h.order r q u t ru qt).mpr ut⟩
    · rintro ⟨r,rp,rq⟩
      obtain ⟨u,ru⟩ := h.total r rp.1
      exact ⟨u,(aut_below_l h ps ru).mp rp,(h.order r q u t ru qt).mp rq⟩
  · intro q hq _
    obtain ⟨p,pq⟩ := h.onto q hq
    refine ⟨p,(h.domain p q pq).1,nz (h.domain p q pq).1,?_⟩
    intro r s rs rp
    exact ⟨s,(aut_below_l h pq rs).mp ⟨(h.domain r s rs).1,nz (h.domain r s rs).1,rp⟩,
      O.refl s (h.domain r s rs).2⟩

/-- 原自同构的回拉泛型、满同构和逐名字取值一次取得。 -/
theorem aut_extension_l (O : Cond_order_d M B R B) (hZF : M.Models ZF)
    (h : Aut_d M B R B F) {G : M.Domain → Prop} (generic : Generic_d M B R B G) :
    let H := Pull_generic_d M F G
    let E := extension_l M hZF B R B H
    let N := extension_l M hZF B R B G
    Generic_d M B R B H ∧ ∃ e : E.Domain → N.Domain,
      (∀ a b, E.mem a b ↔ N.mem (e a) (e b)) ∧ Function.Injective e ∧ Function.Surjective e ∧
      (∀ x a, Gval_d M B R B H x a ↔ Gval_d M B R B G x (e a)) ∧
      ∀ a s t, Qval_d M B R B H s a → Nmap_d M F s t → Qval_d M B R B G t (e a) := by
  let H := Pull_generic_d M F G
  have reg := h.regular_l O hZF
  have inh := reg.pull_inhabited_l O hZF generic
  have gen := reg_generic_l O O hZF reg generic inh
  obtain ⟨e,values,full,inj⟩ := stage_extension_l O O hZF reg generic inh
  have onto : Function.Surjective e := by
    intro b
    obtain ⟨t,nt,tb⟩ := value_name_l b
    obtain ⟨s,ns,st⟩ := aut_nmap_onto_l hZF h nt
    obtain ⟨a,sa⟩ := name_value_l (R := R) (z := B) (U := H) ns
    exact ⟨a,qval_unique_l (values a s t sa st) tb⟩
  have ground x a (ha : Gval_d M B R B H x a) : Gval_d M B R B G x (e a) := by
    obtain ⟨p,s,⟨q,pq,hq⟩,check,sa⟩ := ha
    obtain ⟨t,check',_,_⟩ := zf_check_l M hZF (generic.proper q hq).1 x
    exact ⟨q,t,hq,check',values a s t sa (aut_check_l hZF h pq check check')⟩
  refine ⟨gen,e,?_,inj,onto,?_,values⟩
  · intro a b
    exact ((full b (e a)).trans
      ⟨fun ⟨c,cb,eq⟩ => inj eq ▸ cb,fun ab => ⟨a,ab,rfl⟩⟩).symm
  · intro x a
    refine ⟨ground x a,fun ha => ?_⟩
    obtain ⟨b,hb⟩ := gval_exists_l hZF gen x
    exact inj ((ground x b hb).unique_l O hZF generic ha) ▸ hb

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范实数名字的实际自同构固定性

系数与候选名字同时搬运。规范库的双向闭合和原函数公式的力迫不变性
逐条识别同一个名字；其结论强于在泛型扩张中被迫等值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Rn_data_d.aut_fixed_l {B R b ω D t W r F : M.Domain}
    (h : Rn_data_d I B R b ω D t W r) (aut : Aut_d M B R B F) (fixed : Entry_d M b b F) :
    Nmap_d M F r r := by
  have hb := (aut.domain b b fixed).1
  have nt := check_name_l M (check_range_l M hZF) hb h.check
  have tt := aut_check_fixed_l hZF aut fixed h.check
  have transfer {s u p q : M.Domain} (hs : M.mem s W) (su : Nmap_d M F s u) (pq : Entry_d M p q F) :
      Fn_name_d M B R B p t t s ↔ Fn_name_d M B R B q t t u := by
    have ns := h.pool.name_l hZF hb hs
    have nu := h.pool.name_l hZF hb (h.pool.aut_image_l hZF aut fixed hs su)
    have force := aut_forces_closed_l hZF aut fn_body_m fn_body_closed_l (fn_env_l t t s) (fn_env_l t t u)
      (Fin.cases ns (Fin.cases nt (fun _ => nt))) (Fin.cases su (Fin.cases tt (fun _ => tt))) pq
    exact ⟨fun f => ⟨nt,nt,nu,force.mp f.2.2.2⟩,fun f => ⟨nt,nt,ns,force.mpr f.2.2.2⟩⟩
  obtain ⟨r',image⟩ := nmap_exists_l M hZF F r
  have nr' := nmap_name_l M hZF (fun p q pq => (aut.domain p q pq).2) image
  have graph {s : M.Domain} (ns : Name_d M B s) : ∀ v, M.mem v s → ∃ a p, KPair_d M v a p := by
    intro v hv
    obtain ⟨a,p,pair,_⟩ := (name_unfold_l M (name_ops_l M hZF) B s).mp ns v hv
    exact ⟨a,p,pair⟩
  have eq : r' = r := entry_ext_l M hZF.1 (graph nr') (graph h.name) (fun u q => by
    rw [nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) image]
    constructor
    · rintro ⟨s,p,sp,su,pq⟩
      obtain ⟨hs,_,fn⟩ := (h.entries s p).mp sp
      exact (h.entries u q).mpr ⟨h.pool.aut_image_l hZF aut fixed hs su,(aut.domain p q pq).2,(transfer hs su pq).mp fn⟩
    · intro uq
      obtain ⟨hu,hq,fn⟩ := (h.entries u q).mp uq
      obtain ⟨s,hs,su⟩ := h.pool.aut_onto_l hZF aut fixed hu
      obtain ⟨p,pq⟩ := aut.onto q hq
      exact ⟨s,p,(h.entries s p).mpr ⟨hs,(aut.domain p q pq).1,(transfer hs su pq).mpr fn⟩,su,pq⟩)
  exact eq ▸ image

end YesMetaZFC.Model.Forcing.Internal
