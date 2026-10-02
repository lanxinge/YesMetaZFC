import YesMetaZFC.SetTheory.Ord.Code.Transport
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 不依赖方块界的规范序数配对

编码是典范序数对良序中的位置。任一容纳输入的序数方块都算出同一结果；
存在性、唯一性及单射性均由实际集合编码坍塌图给出。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Oc_at_d (a p c : M.Domain) : Prop := M.IsOrdinal a ∧ ∃ X R,
  M.IsCanonicalOrdinalPairOrder I R X a ∧ M.mem p X ∧ M.IsWellOrderCollapseValue I R X p c

def Oc_pair_d (a b c : M.Domain) : Prop := ∃ t p, I.Codes p a b ∧ Oc_at_d I t p c

def oc_order_m {n} (a X R : Term n) : Formula 1 n :=
  .conj (Formula.isCartesianProduct 𝒞 X a a) (.conj (Formula.isRelation 𝒞 R)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken)
        (binary_pred_m (BinarySchema.canonicalOrdinalPairLess 𝒞) Fin.elim0 (.bound 1) .newest)))))))
derive_free_closed oc_order_m

theorem oc_order_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a X R : Term n) :
    Formula.satisfies ρ (oc_order_m (𝒞 := 𝒞) a X R) ↔
      M.IsCanonicalOrdinalPairOrder I (R.eval ρ) (X.eval ρ) (a.eval ρ) := by
  simp only [oc_order_m, Formula.satisfies_conj_iff, Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, binary_pred_sat_l,
    Formula.denote_canonicalOrdinalPairLess_iff I hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  exact ⟨fun h => ⟨h.1, ⟨h.2.1, fun p q hp => ⟨((h.2.2 p q).mp hp).1, ((h.2.2 p q).mp hp).2.1⟩⟩, h.2.2⟩,
    fun h => ⟨h.1, h.2.1.1, h.2.2⟩⟩

def oc_at_m {n} (a p c : Term n) : Formula 1 n := .conj (Formula.isOrdinal a)
  (.existsE (.existsE (.conj (oc_order_m (𝒞 := 𝒞) a.weaken.weaken (.bound 1) .newest)
    (.conj (.mem p.weaken.weaken (.bound 1))
      (Formula.isWellOrderCollapseValue 𝒞 .newest (.bound 1) p.weaken.weaken c.weaken.weaken)))))
derive_free_closed oc_at_m

theorem oc_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a p c : Term n) :
    Formula.satisfies ρ (oc_at_m (𝒞 := 𝒞) a p c) ↔ Oc_at_d I (a.eval ρ) (p.eval ρ) (c.eval ρ) := by
  simp only [oc_at_m, Oc_at_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_exists_iff, oc_order_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_isWellOrderCollapseValue_iff I hE, Definitional.Term.eval_weaken]
  rfl

def oc_pair_m {n} (a b c : Term n) : Formula 1 n := .existsE (.existsE
  (.conj (𝒞.code .newest a.weaken.weaken b.weaken.weaken)
    (oc_at_m (𝒞 := 𝒞) (.bound 1) .newest c.weaken.weaken)))
derive_free_closed oc_pair_m

theorem oc_pair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a b c : Term n) :
    Formula.satisfies ρ (oc_pair_m (𝒞 := 𝒞) a b c) ↔ Oc_pair_d I (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [oc_pair_m, Oc_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, oc_at_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem oc_bound_l (hZF : M.Models ZF) {a b : M.Domain} (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) :
    ∃ t, M.IsOrdinal t ∧ M.mem a t ∧ M.mem b t := by
  have upper {x y : M.Domain} (hy : M.IsOrdinal y) (hxy : x = y ∨ M.mem x y) :
      ∃ t, M.IsOrdinal t ∧ M.mem x t ∧ M.mem y t := by
    obtain ⟨t, ht⟩ := KP.exists_successor (ZF.modelsKP hZF) y
    exact ⟨t, KP.successor_isOrdinal (ZF.modelsKP hZF) hy ht,
      hxy.elim (fun he => he.symm ▸ ht.predecessor_mem) (fun h => (ht x).mpr (Or.inl h)), ht.predecessor_mem⟩
  rcases ha.trichotomy hZF.1 hb (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) a b) with he | hab | hba
  · exact upper hb (Or.inl (hZF.1.eq_of_same_members a b he))
  · exact upper hb (Or.inr hab)
  · obtain ⟨t, ht, hb, ha⟩ := upper ha (Or.inr hba)
    exact ⟨t, ht, ha, hb⟩

theorem oc_at_unique_l (hZF : M.Models ZF) {a b p c d} (h : Oc_at_d I a p c) (g : Oc_at_d I b p d) : c = d := by
  obtain ⟨ha, X, R, hr, hp, hc⟩ := h
  obtain ⟨hb, Y, S, hs, hq, hd⟩ := g
  obtain ⟨t, ht, hat, hbt⟩ := oc_bound_l hZF ha hb
  obtain ⟨W, hw⟩ := ZF.exists_cartesianProduct hZF I t t
  obtain ⟨T, hT, ho⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I ht hw
  have ex := oc_square_end_l I ha hr hT (ht.transitive a hat)
  have ey := oc_square_end_l I hb hs hT (ht.transitive b hbt)
  obtain ⟨_, _, hu⟩ := ZF.wellOrderCollapseValue_existsUnique hZF I ho p (ex.1.1 p hp)
  exact (hu c (hc.end_l I hp ex.1 ex.2)).trans (hu d (hd.end_l I hq ey.1 ey.2)).symm

/-- 任意方块的整张坍塌图都实现同一全局编码。 -/
theorem oc_at_function_l (hZF : M.Models ZF) {a b X R F p c} (ha : M.IsOrdinal a)
    (hr : M.IsCanonicalOrdinalPairOrder I R X a) (hf : M.IsWellOrderCollapseFunction I F R X X)
    (hp : M.mem p X) (hc : Oc_at_d I b p c) : M.PairMember I p c F := by
  obtain ⟨d, hd⟩ := (hf.2.1 p).mp hp
  have eq := oc_at_unique_l I hZF hc ⟨ha, X, R, hr, hp,
    hf.collapseValue_of_pairMember hZF I (hr.isSetCodedWellOrder hZF ha) hp hd⟩
  exact eq.symm ▸ hd

theorem oc_at_value_l (hZF : M.Models ZF) {a b X R p c} (ha : M.IsOrdinal a)
    (hr : M.IsCanonicalOrdinalPairOrder I R X a) (hp : M.mem p X) (hc : Oc_at_d I b p c) :
    M.IsWellOrderCollapseValue I R X p c := by
  obtain ⟨d, hd, _⟩ := ZF.wellOrderCollapseValue_existsUnique hZF I (hr.isSetCodedWellOrder hZF ha) p hp
  exact (oc_at_unique_l I hZF hc ⟨ha, X, R, hr, hp, hd⟩).symm ▸ hd

theorem oc_at_ordinal_l (hZF : M.Models ZF) {a p c} (h : Oc_at_d I a p c) : M.IsOrdinal c := by
  obtain ⟨ha, X, R, hr, hp, hc⟩ := h
  have ho := hr.isSetCodedWellOrder hZF ha
  obtain ⟨t, ht, _⟩ := ZF.wellOrderType_existsUnique hZF I ho
  obtain ⟨F, hf, hF⟩ := ht
  have hh := oc_at_function_l I hZF ha hr hf hp ⟨ha, X, R, hr, hp, hc⟩
  exact (show M.IsWellOrderType I R X t from ⟨F, hf, hF⟩).isOrdinal hZF I ho |>.mem ((hF c).mpr ⟨p, hh⟩)

theorem oc_pair_types_l (hZF : M.Models ZF) {a b c} (h : Oc_pair_d I a b c) :
    M.IsOrdinal a ∧ M.IsOrdinal b ∧ M.IsOrdinal c := by
  obtain ⟨t, p, hp, ht⟩ := h
  have hc := oc_at_ordinal_l I hZF ht
  obtain ⟨hot, X, R, hr, hx, _⟩ := ht
  obtain ⟨a', ha, b', hb, hp'⟩ := (hr.1 p).mp hx
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  exact ⟨hot.mem ha, hot.mem hb, hc⟩

theorem oc_pair_exists_l (hZF : M.Models ZF) {a b} (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) :
    ∃ c, Oc_pair_d I a b c := by
  obtain ⟨t, ht, ha, hb⟩ := oc_bound_l hZF ha hb
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I t t
  obtain ⟨R, hr, ho⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I ht hX
  obtain ⟨p, hp⟩ := I.total a b
  have hx := (hX p).mpr ⟨a, ha, b, hb, hp⟩
  obtain ⟨c, hc, _⟩ := ZF.wellOrderCollapseValue_existsUnique hZF I ho p hx
  exact ⟨c, t, p, hp, ht, X, R, hr, hx, hc⟩

theorem oc_pair_unique_l (hZF : M.Models ZF) {a b c d} (h : Oc_pair_d I a b c) (g : Oc_pair_d I a b d) : c = d := by
  obtain ⟨t, p, hp, hc⟩ := h
  obtain ⟨s, q, hq, hd⟩ := g
  have eq := I.unique hp hq; subst q
  exact oc_at_unique_l I hZF hc hd

theorem oc_pair_injective_l (hZF : M.Models ZF) {a b x y c}
    (h : Oc_pair_d I a b c) (g : Oc_pair_d I x y c) : a = x ∧ b = y := by
  obtain ⟨t, p, hp, ht, X, R, hr, hpx, hc⟩ := h
  obtain ⟨s, q, hq, hs, Y, S, hS, hqy, hd⟩ := g
  obtain ⟨u, hu, htu, hsu⟩ := oc_bound_l hZF ht hs
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I u u
  obtain ⟨T, hT, ho⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I hu hW
  obtain ⟨_, ⟨F, hf, _⟩, _⟩ := ZF.wellOrderType_existsUnique hZF I ho
  have px := (oc_square_end_l I ht hr hT (hu.transitive t htu)).1.1 p hpx
  have qy := (oc_square_end_l I hs hS hT (hu.transitive s hsu)).1.1 q hqy
  have hpc := oc_at_function_l I hZF hu hT hf px ⟨ht, X, R, hr, hpx, hc⟩
  have hqc := oc_at_function_l I hZF hu hT hf qy ⟨hs, Y, S, hS, hqy, hd⟩
  have eq := hf.isSetInjective hZF I ho p q c hpc hqc; subst q
  exact I.injective hp hq

/-- 〈0,0〉是典范序的首项，其代码恰为 0。 -/
theorem oc_pair_zero_l (hZF : M.Models ZF) {e} (he : ∀ z, ¬ M.mem z e) : Oc_pair_d I e e e := by
  obtain ⟨c, hc⟩ := oc_pair_exists_l I hZF (Structure.IsOrdinal.of_no_members he) (Structure.IsOrdinal.of_no_members he)
  have empty : ∀ z, ¬ M.mem z c := by
    obtain ⟨t, p, hp, _, X, R, hr, _, P, F, hP, hf, hF⟩ := hc
    intro z hz
    obtain ⟨q, hq⟩ := (hF z).mp hz
    have hqp := ((hP q).mp ((hf.2.1 q).mpr ⟨z, hq⟩)).2
    obtain ⟨_, _, u, v, a, b, m, n, _, hp', _, hn, lt⟩ := (hr.2.2 q p).mp hqp
    obtain ⟨rfl, rfl⟩ := I.injective hp hp'
    have eq : n = e := hn.elim (fun h => h.1) (fun h => h.1)
    subst n
    rcases lt with h | ⟨_, h | ⟨_, h⟩⟩ <;> exact he _ h
  exact hZF.1.eq_of_same_members c e (fun z => iff_of_false (empty z) (he z)) ▸ hc

end YesMetaZFC.SetTheory
