import YesMetaZFC.SetTheory.Descriptive.Borel.Universe
import YesMetaZFC.SetTheory.Card.CountablePair
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail

/-! # 内部自然数配对

先由已有内部单射及 Cantor–Bernstein 构造 ω×ω 到 ω 的实际双射。
逐坐标提升该双射即可配对 Baire 实数，且保持相同内部长度的前缀。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Npair_d (ω J : M.Domain) : Prop := ∃ W,
  M.IsCartesianProduct I W ω ω ∧ M.IsSetBijectionFromTo I J W ω
def npair_m {d} (ω J : Term d) : Formula 1 d := .existsE (.conj
  (Formula.isCartesianProduct 𝒞 .newest ω.weaken ω.weaken)
  (Formula.isBijectionFromTo 𝒞 J.weaken .newest ω.weaken))
derive_free_closed npair_m

theorem npair_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J : Term d) :
    Formula.satisfies ρ (npair_m (𝒞 := 𝒞) ω J) ↔ Npair_d I (ω.eval ρ) (J.eval ρ) := by
  simp only [npair_m, Npair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isCartesianProduct_iff I, Formula.satisfies_isBijectionFromTo_iff I hE,
    Definitional.Term.eval_weaken]; rfl

theorem npair_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ J, Npair_d I ω J := by
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨E, hE⟩ := ZF.exists_identityBijection hZF I ω
  have hc := ZF.countable_product_l I hZF hω ⟨E, hE.1⟩ ⟨E, hE.1⟩ hW
  obtain ⟨z, _, hz⟩ := hω.1.1
  let ρ : Env M 1 := ⟨fun _ => z, fun _ => z⟩
  let φ : BinarySchema 1 := { body := 𝒞.code .newest (.bound 1) (.bound 2) }
  have hp i p : φ.denote ρ i p ↔ I.Codes p i z := I.satisfies_code_iff _ _ _ _
  obtain ⟨F, hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ (source := ω) (target := W)
    (fun i _ => (I.total i z).imp fun p h => (hp i p).mpr h)
    (fun i _ p q h k => I.unique ((hp i p).mp h) ((hp i q).mp k))
    (fun i p hi h => (hW p).mpr ⟨i, hi, z, hz, (hp i p).mp h⟩)
    (fun i j p _ _ h k => (I.injective ((hp i p).mp h) ((hp j p).mp k)).1)
  obtain ⟨J, hJ⟩ := ZF.equinumerous_of_cardinalLessOrEqual hZF I hc ⟨F, hF⟩
  exact ⟨J, W, hW, hJ⟩

def Np_d (J a b v : M.Domain) : Prop := ∃ p, I.Codes p a b ∧ M.PairMember I p v J
def np_m {d} (J a b v : Term d) : Formula 1 d := .existsE (.conj
  (𝒞.code .newest a.weaken b.weaken) (Formula.orderedPairMem 𝒞 .newest v.weaken J.weaken))
derive_free_closed np_m
theorem np_sat_l {d} (ρ : Env M d) (J a b v : Term d) :
    Formula.satisfies ρ (np_m (𝒞 := 𝒞) J a b v) ↔ Np_d I (J.eval ρ) (a.eval ρ) (b.eval ρ) (v.eval ρ) := by
  simp only [np_m, Np_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem np_total_l {ω J a b} (hJ : Npair_d I ω J) (ha : M.mem a ω) (hb : M.mem b ω) :
    ∃ v, M.mem v ω ∧ Np_d I J a b v := by
  obtain ⟨W, hW, hJ⟩ := hJ
  obtain ⟨p, hp⟩ := I.total a b
  obtain ⟨v, hv, hpv⟩ := hJ.1.1.2.2 p ((hW p).mpr ⟨a, ha, b, hb, hp⟩)
  exact ⟨v, hv, p, hp, hpv⟩

theorem np_unique_l {ω J a b v w} (hJ : Npair_d I ω J)
    (h : Np_d I J a b v) (k : Np_d I J a b w) : v = w := by
  obtain ⟨_, _, hJ⟩ := hJ
  obtain ⟨p, hp, hv⟩ := h
  obtain ⟨q, hq, hw⟩ := k
  exact hJ.1.1.1.2 p v w hv (I.unique hq hp ▸ hw)

theorem np_injective_l {ω J a b c d v} (hJ : Npair_d I ω J)
    (h : Np_d I J a b v) (k : Np_d I J c d v) : a = c ∧ b = d := by
  obtain ⟨_, _, hJ⟩ := hJ
  obtain ⟨p, hp, hv⟩ := h
  obtain ⟨q, hq, hw⟩ := k
  exact I.injective hp (hJ.1.2 q p v hw hv ▸ hq)

theorem np_type_l {ω J a b v} (hJ : Npair_d I ω J) (h : Np_d I J a b v) :
    M.mem a ω ∧ M.mem b ω ∧ M.mem v ω := by
  obtain ⟨W, hW, hJ⟩ := hJ
  obtain ⟨p, hp, hv⟩ := h
  obtain ⟨c, hc, d, hd, hcd⟩ := (hW p).mp (hJ.1.1.input_mem_of_pairMember hv)
  obtain ⟨rfl, rfl⟩ := I.injective hp hcd
  exact ⟨hc, hd, hJ.1.1.output_mem_of_pairMember hv⟩

theorem np_surj_l {ω J v} (hJ : Npair_d I ω J) (hv : M.mem v ω) :
    ∃ a b, M.mem a ω ∧ M.mem b ω ∧ Np_d I J a b v := by
  obtain ⟨W, hW, hJ⟩ := hJ
  obtain ⟨p, hpW, hpv⟩ := hJ.2 v hv
  obtain ⟨a, ha, b, hb, hp⟩ := (hW p).mp hpW
  exact ⟨a, b, ha, hb, p, hp, hpv⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限列和实数的逐坐标配对

同一个定义覆盖任意内部定义域。存在性与解码均构造实际函数图；有限长度和 ω
只是该一般构造的两个实例。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rp_d (J x y t : M.Domain) : Prop := M.IsSetRelation I t ∧ ∀ i v,
  M.PairMember I i v t ↔ ∃ a b, M.PairMember I i a x ∧ M.PairMember I i b y ∧ Np_d I J a b v
def rp_m {d} (J x y t : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 t)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest t.weaken.weaken)
    (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) x.weaken.weaken.weaken.weaken)
      (.conj (Formula.orderedPairMem 𝒞 (.bound 3) .newest y.weaken.weaken.weaken.weaken)
        (np_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken (.bound 1) .newest (.bound 2)))))))))
derive_free_closed rp_m

theorem rp_sat_l {d} (ρ : Env M d) (J x y t : Term d) :
    Formula.satisfies ρ (rp_m (𝒞 := 𝒞) J x y t) ↔ Rp_d I (J.eval ρ) (x.eval ρ) (y.eval ρ) (t.eval ρ) := by
  simp only [rp_m, Rp_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, np_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rp_unique_l (hE : Extensional M) {J x y t u} (h : Rp_d I J x y t) (k : Rp_d I J x y u) : t = u :=
  h.1.eq_of_pairMember_iff hE k.1 (fun i v => (h.2 i v).trans (k.2 i v).symm)

theorem rp_exists_l (hZF : M.Models ZF) {ω J D x y} (hJ : Npair_d I ω J)
    (hx : M.IsSetFunctionFromTo I x D ω) (hy : M.IsSetFunctionFromTo I y D ω) :
    ∃ t, M.IsSetFunctionFromTo I t D ω ∧ Rp_d I J x y t := by
  let ρ : Env M 3 := ((⟨fun _ => J, fun _ => J⟩ : Env M 1).push x).push y
  let φ : BinarySchema 3 := {
    body := .existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 5))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4))
        (np_m (𝒞 := 𝒞) (.bound 6) (.bound 1) .newest (.bound 2))))) }
  have hp i v : φ.denote ρ i v ↔ ∃ a b, M.PairMember I i a x ∧ M.PairMember I i b y ∧ Np_d I J a b v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, np_sat_l I]; rfl
  obtain ⟨t, ht, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := ω)
    (by
      intro i hi
      obtain ⟨a, ha, hia⟩ := hx.2.2 i hi
      obtain ⟨b, hb, hib⟩ := hy.2.2 i hi
      obtain ⟨v, _, hv⟩ := np_total_l I hJ ha hb
      exact ⟨v, (hp i v).mpr ⟨a, b, hia, hib, hv⟩⟩)
    (by
      intro i _ v w hv hw
      obtain ⟨a, b, hia, hib, hv⟩ := (hp i v).mp hv
      obtain ⟨c, d, hic, hid, hw⟩ := (hp i w).mp hw
      exact np_unique_l I hJ hv (hx.1.2 i c a hic hia ▸ hy.1.2 i d b hid hib ▸ hw))
    (fun i v _ hv => ((hp i v).mp hv).elim fun _ h => h.elim fun _ h => (np_type_l I hJ h.2.2).2.2)
  refine ⟨t, ht, ht.1.1, fun i v => ((he i v).trans (and_congr_right fun _ => hp i v)).trans ?_⟩
  exact ⟨And.right, fun h => ⟨h.elim fun _ h => h.elim fun _ h => hx.input_mem_of_pairMember h.1, h⟩⟩

/-- 逆双射逐坐标给出两个实际序列，不在宿主层选择坐标值。 -/
theorem rp_decode_l (hZF : M.Models ZF) {ω J D t} (hJ : Npair_d I ω J)
    (ht : M.IsSetFunctionFromTo I t D ω) :
    ∃ x y, M.IsSetFunctionFromTo I x D ω ∧ M.IsSetFunctionFromTo I y D ω ∧ Rp_d I J x y t := by
  let ρ : Env M 2 := (⟨fun _ => J, fun _ => J⟩ : Env M 1).push t
  let φ (b : Bool) : BinarySchema 2 := {
    body := .existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 4))
      (np_m (𝒞 := 𝒞) (.bound 5) (if b then .newest else .bound 2)
        (if b then .bound 2 else .newest) (.bound 1))))
    freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have hp b i a : (φ b).denote ρ i a ↔ ∃ v c, M.PairMember I i v t ∧
      Np_d I J (if b then c else a) (if b then a else c) v := by
    cases b <;> simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, np_sat_l I,
      Bool.false_eq_true, ↓reduceIte] <;> rfl
  have build (b : Bool) : ∃ x, M.IsSetFunctionFromTo I x D ω ∧ ∀ i a,
      M.PairMember I i a x ↔ M.mem i D ∧ ∃ v c, M.PairMember I i v t ∧
        Np_d I J (if b then c else a) (if b then a else c) v := by
    obtain ⟨x, hx, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I (φ b) ρ (source := D) (target := ω)
      (by
        intro i hi
        obtain ⟨v, hv, hiv⟩ := ht.2.2 i hi
        obtain ⟨a, c, _, _, hac⟩ := np_surj_l I hJ hv
        cases b
        · exact ⟨a, (hp false i a).mpr ⟨v, c, hiv, hac⟩⟩
        · exact ⟨c, (hp true i c).mpr ⟨v, a, hiv, hac⟩⟩)
      (by
        intro i _ a c ha hc
        obtain ⟨v, a', hiv, ha⟩ := (hp b i a).mp ha
        obtain ⟨w, c', hiw, hc⟩ := (hp b i c).mp hc
        have e := ht.1.2 i w v hiw hiv
        have eqn := np_injective_l I hJ ha (e ▸ hc)
        cases b
        · exact eqn.1
        · exact eqn.2)
      (by
        intro i a _ ha
        obtain ⟨v, c, _, ha⟩ := (hp b i a).mp ha
        have hb := np_type_l I hJ ha
        cases b
        · exact hb.1
        · exact hb.2.1)
    exact ⟨x, hx, fun i a => (he i a).trans (and_congr_right fun _ => hp b i a)⟩
  obtain ⟨x, hx, ex⟩ := build false
  obtain ⟨y, hy, ey⟩ := build true
  refine ⟨x, y, hx, hy, ht.1.1, fun i v => ⟨?_, ?_⟩⟩
  · intro hv
    obtain ⟨a, b, _, _, hab⟩ := np_surj_l I hJ (ht.output_mem_of_pairMember hv)
    exact ⟨a, b, (ex i a).mpr ⟨ht.input_mem_of_pairMember hv, v, b, hv, hab⟩,
      (ey i b).mpr ⟨ht.input_mem_of_pairMember hv, v, a, hv, hab⟩, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨_, v', b', hv, ha⟩ := (ex i a).mp ha
    obtain ⟨_, w, a', hw, hb⟩ := (ey i b).mp hb
    have eqn := np_injective_l I hJ ha (ht.1.2 i w v' hw hv ▸ hb)
    have eb : b' = b := eqn.2
    have hnp : Np_d I J a b v' := eb ▸ (show Np_d I J a b' v' from ha)
    exact np_unique_l I hJ hnp hab ▸ hv

theorem rp_subset_l {ω J D s t r x y u} (hJ : Npair_d I ω J)
    (hs : M.IsSetFunctionFromTo I s D ω) (ht : M.IsSetFunctionFromTo I t D ω)
    (hr : Rp_d I J s t r) (hu : Rp_d I J x y u) :
    M.MemberSubset r u ↔ M.MemberSubset s x ∧ M.MemberSubset t y := by
  have lift {P Q i a} (h : M.MemberSubset P Q) (ha : M.PairMember I i a P) : M.PairMember I i a Q :=
    ha.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
  constructor
  · intro h
    have pair {i a b} (ha : M.PairMember I i a s) (hb : M.PairMember I i b t) :
        M.PairMember I i a x ∧ M.PairMember I i b y := by
      obtain ⟨v, _, hv⟩ := np_total_l I hJ (hs.output_mem_of_pairMember ha) (ht.output_mem_of_pairMember hb)
      obtain ⟨c, d, hc, hd, hcd⟩ := (hu.2 i v).mp (lift h ((hr.2 i v).mpr ⟨a, b, ha, hb, hv⟩))
      obtain ⟨e, f⟩ := np_injective_l I hJ hv hcd
      exact ⟨e.symm ▸ hc, f.symm ▸ hd⟩
    constructor
    · intro p hp
      obtain ⟨i, a, hc⟩ := hs.1.1 p hp
      obtain ⟨b, _, hb⟩ := ht.2.2 i (hs.input_mem_of_pairMember ⟨p, hc, hp⟩)
      obtain ⟨q, hq, hqx⟩ := (pair ⟨p, hc, hp⟩ hb).1
      exact (I.unique hc hq).symm ▸ hqx
    · intro p hp
      obtain ⟨i, b, hc⟩ := ht.1.1 p hp
      obtain ⟨a, _, ha⟩ := hs.2.2 i (ht.input_mem_of_pairMember ⟨p, hc, hp⟩)
      obtain ⟨q, hq, hqy⟩ := (pair ha ⟨p, hc, hp⟩).2
      exact (I.unique hc hq).symm ▸ hqy
  · rintro ⟨hx, hy⟩ p hp
    obtain ⟨i, v, hc⟩ := hr.1 p hp
    obtain ⟨a, b, ha, hb, hv⟩ := (hr.2 i v).mp ⟨p, hc, hp⟩
    obtain ⟨q, hq, hqu⟩ := (hu.2 i v).mpr ⟨a, b, lift hx ha, lift hy hb, hv⟩
    exact (I.unique hc hq).symm ▸ hqu

theorem rp_injective_l (hE : Extensional M) {ω J D x y u v t} (hJ : Npair_d I ω J)
    (hx : M.IsSetFunctionFromTo I x D ω) (hy : M.IsSetFunctionFromTo I y D ω)
    (hu : M.IsSetFunctionFromTo I u D ω) (hv : M.IsSetFunctionFromTo I v D ω)
    (h : Rp_d I J x y t) (k : Rp_d I J u v t) : x = u ∧ y = v := by
  have a := (rp_subset_l I hJ hx hy h k).mp (fun _ => id)
  have b := (rp_subset_l I hJ hu hv k h).mp (fun _ => id)
  exact ⟨hE.eq_of_same_members x u (fun p => ⟨a.1 p, b.1 p⟩),
    hE.eq_of_same_members y v (fun p => ⟨a.2 p, b.2 p⟩)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Baire 空间的内部配对同胚

实际双射图配合等长度矩形基，识别 Baire×Baire 与 Baire。这里的前缀长度
仍遍历模型自身的 ω。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_type_l (hZF : M.Models ZF) {ω J D x y t} (hJ : Npair_d I ω J)
    (hx : M.IsSetFunctionFromTo I x D ω) (hy : M.IsSetFunctionFromTo I y D ω) (h : Rp_d I J x y t) :
    M.IsSetFunctionFromTo I t D ω := by
  obtain ⟨u, hu, hp⟩ := rp_exists_l I hZF hJ hx hy
  exact rp_unique_l I hZF.1 hp h ▸ hu

theorem rp_graph_l (hZF : M.Models ZF) {ω B J} (hB : Baire_d I ω B) (hJ : Npair_d I ω J) :
    ∃ P F, M.IsCartesianProduct I P B B ∧ M.IsSetBijectionFromTo I F P B ∧
      ∀ p t, M.PairMember I p t F ↔ ∃ x y, M.mem x B ∧ M.mem y B ∧ I.Codes p x y ∧ Rp_d I J x y t := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B B
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
      (rp_m (𝒞 := 𝒞) (.bound 4) (.bound 1) .newest (.bound 2)))) }
  have hp p t : φ.denote ρ p t ↔ ∃ x y, I.Codes p x y ∧ Rp_d I J x y t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, rp_sat_l I]; rfl
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := B)
    (by
      intro p hpP
      obtain ⟨x, hx, y, hy, hc⟩ := (hP p).mp hpP
      obtain ⟨t, _, ht⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy)
      exact ⟨t, (hp p t).mpr ⟨x, y, hc, ht⟩⟩)
    (by
      intro p _ t u ht hu
      obtain ⟨x, y, hc, ht⟩ := (hp p t).mp ht
      obtain ⟨x', y', hc', hu⟩ := (hp p u).mp hu
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact rp_unique_l I hZF.1 ht hu)
    (by
      intro p t hpP ht
      obtain ⟨x, hx, y, hy, hc⟩ := (hP p).mp hpP
      obtain ⟨x', y', hc', ht⟩ := (hp p t).mp ht
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact (hB.2 t).mpr (rp_type_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy) ht))
  have eqn p t : M.PairMember I p t F ↔ ∃ x y, M.mem x B ∧ M.mem y B ∧ I.Codes p x y ∧ Rp_d I J x y t := by
    rw [he, hp]
    constructor
    · rintro ⟨hpP, x, y, hc, ht⟩
      obtain ⟨x', hx, y', hy, hc'⟩ := (hP p).mp hpP
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact ⟨x, y, hx, hy, hc, ht⟩
    · rintro ⟨x, y, hx, hy, hc, ht⟩
      exact ⟨(hP p).mpr ⟨x, hx, y, hy, hc⟩, x, y, hc, ht⟩
  refine ⟨P, F, hP, ⟨⟨hF, ?_⟩, ?_⟩, eqn⟩
  · intro p q t ht hu
    obtain ⟨x, y, hx, hy, hc, ht⟩ := (eqn p t).mp ht
    obtain ⟨u, v, hu, hv, hd, hk⟩ := (eqn q t).mp hu
    obtain ⟨rfl, rfl⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy)
      ((hB.2 u).mp hu) ((hB.2 v).mp hv) ht hk
    exact I.unique hc hd
  · intro t ht
    obtain ⟨x, y, hx, hy, hr⟩ := rp_decode_l I hZF hJ ((hB.2 t).mp ht)
    obtain ⟨p, hp⟩ := I.total x y
    exact ⟨p, (hP p).mpr ⟨x, (hB.2 x).mpr hx, y, (hB.2 y).mpr hy, hp⟩,
      (eqn p t).mpr ⟨x, y, (hB.2 x).mpr hx, (hB.2 y).mpr hy, hp, hr⟩⟩

/-- 配对坐标下的开集判据恰为乘积的等长度矩形基判据。 -/
theorem rp_open_l (hZF : M.Models ZF) {ω B A J U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : Open_d A B U ↔ M.MemberSubset U B ∧
      ∀ x y z, M.mem x B → M.mem y B → Rp_d I J x y z → M.mem z U →
        ∃ n s t, M.mem n ω ∧ M.IsSetFunctionFromTo I s n ω ∧ M.IsSetFunctionFromTo I t n ω ∧
          M.MemberSubset s x ∧ M.MemberSubset t y ∧ ∀ u v w,
            M.mem u B → M.mem v B → Rp_d I J u v w → M.MemberSubset s u → M.MemberSubset t v → M.mem w U := by
  constructor
  · intro ho
    refine ⟨ho.1, fun x y z _ _ hr hz => ?_⟩
    obtain ⟨r, hrA, hrz, hru⟩ := ho.2 z hz
    obtain ⟨n, hn, hrf⟩ := (hA r).mp hrA
    obtain ⟨s, t, hs, ht, hst⟩ := rp_decode_l I hZF hJ hrf
    obtain ⟨hsx, hty⟩ := (rp_subset_l I hJ hs ht hst hr).mp hrz
    refine ⟨n, s, t, hn, hs, ht, hsx, hty, fun u v w hu hv hw hsu htv => ?_⟩
    exact hru w ((hB.2 w).mpr (rp_type_l I hZF hJ ((hB.2 u).mp hu) ((hB.2 v).mp hv) hw))
      ((rp_subset_l I hJ hs ht hst hw).mpr ⟨hsu, htv⟩)
  · rintro ⟨hUB, ho⟩
    refine ⟨hUB, fun z hz => ?_⟩
    obtain ⟨x, y, hx, hy, hr⟩ := rp_decode_l I hZF hJ ((hB.2 z).mp (hUB z hz))
    obtain ⟨n, s, t, hn, hs, ht, hsx, hty, hu⟩ := ho x y z ((hB.2 x).mpr hx) ((hB.2 y).mpr hy) hr hz
    obtain ⟨r, hrf, hst⟩ := rp_exists_l I hZF hJ hs ht
    refine ⟨r, (hA r).mpr ⟨n, hn, hrf⟩, (rp_subset_l I hJ hs ht hst hr).mpr ⟨hsx, hty⟩, fun w hw hrw => ?_⟩
    obtain ⟨u, v, huf, hvf, hp⟩ := rp_decode_l I hZF hJ ((hB.2 w).mp hw)
    obtain ⟨hsu, htv⟩ := (rp_subset_l I hJ hs ht hst hp).mp hrw
    exact hu u v w ((hB.2 u).mpr huf) ((hB.2 v).mpr hvf) hp hsu htv

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限列的配对解码及子边

长度由图本身唯一决定；定义中的长度量词遍历内部 ω。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fp_d (ω J r s t : M.Domain) : Prop := ∃ n, M.mem n ω ∧
  M.IsSetFunctionFromTo I s n ω ∧ M.IsSetFunctionFromTo I t n ω ∧ Rp_d I J s t r
def fp_m {d} (ω J r s t : Term d) : Formula 1 d := Formula.existsMem ω (.conj
  (Formula.isFunctionFromTo 𝒞 s.weaken .newest ω.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 t.weaken .newest ω.weaken) (rp_m (𝒞 := 𝒞) J.weaken s.weaken t.weaken r.weaken)))
derive_free_closed fp_m
theorem fp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J r s t : Term d) :
    Formula.satisfies ρ (fp_m (𝒞 := 𝒞) ω J r s t) ↔
      Fp_d I (ω.eval ρ) (J.eval ρ) (r.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [fp_m, Fp_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem fp_unique_l (hE : Extensional M) {ω J r s t u v} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J r u v) : s = u ∧ t = v := by
  obtain ⟨_, _, hs, ht, hp⟩ := h
  obtain ⟨_, _, hu, hv, hq⟩ := k
  have a := (rp_subset_l I hJ hs ht hp hq).mp (fun _ => id)
  have b := (rp_subset_l I hJ hu hv hq hp).mp (fun _ => id)
  exact ⟨hE.eq_of_same_members s u (fun p => ⟨a.1 p, b.1 p⟩),
    hE.eq_of_same_members t v (fun p => ⟨a.2 p, b.2 p⟩)⟩

theorem fp_type_l (hZF : M.Models ZF) {ω A J r s t} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (h : Fp_d I ω J r s t) : M.mem r A ∧ M.mem s A ∧ M.mem t A := by
  obtain ⟨n, hn, hs, ht, hp⟩ := h
  exact ⟨(hA r).mpr ⟨n, hn, rp_type_l I hZF hJ hs ht hp⟩, (hA s).mpr ⟨n, hn, hs⟩, (hA t).mpr ⟨n, hn, ht⟩⟩

theorem fp_decode_l (hZF : M.Models ZF) {ω A J r} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hr : M.mem r A) : ∃ s t, Fp_d I ω J r s t := by
  obtain ⟨n, hn, hr⟩ := (hA r).mp hr
  obtain ⟨s, t, hs, ht, hp⟩ := rp_decode_l I hZF hJ hr
  exact ⟨s, t, n, hn, hs, ht, hp⟩

theorem fp_at_l (hZF : M.Models ZF) {ω J r s t D} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (hr : M.IsSetFunctionFromTo I r D ω) :
    M.IsSetFunctionFromTo I s D ω ∧ M.IsSetFunctionFromTo I t D ω ∧ Rp_d I J s t r := by
  obtain ⟨n, _, hs, ht, hp⟩ := h
  have e := hZF.1.eq_of_same_members n D (fun i => ((rp_type_l I hZF hJ hs ht hp).2.1 i).trans (hr.2.1 i).symm)
  exact ⟨e ▸ hs, e ▸ ht, hp⟩

theorem fp_sub_l {ω J r s t q u v} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J q u v) :
    M.MemberSubset r q ↔ M.MemberSubset s u ∧ M.MemberSubset t v := by
  obtain ⟨_, _, hs, ht, hp⟩ := h
  obtain ⟨_, _, _, _, hq⟩ := k
  exact rp_subset_l I hJ hs ht hp hq

theorem fp_step_l (hZF : M.Models ZF) {ω J r s t q u v} (hω : M.IsOmega ω) (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J q u v) :
    Step_d I ω r q ↔ Step_d I ω s u ∧ Step_d I ω t v := by
  obtain ⟨n, hn, hs, ht, hp⟩ := h
  obtain ⟨m, hm, hu, hv, hq⟩ := k
  rw [tree_step_iff_l I hZF hω hn hm (rp_type_l I hZF hJ hs ht hp) (rp_type_l I hZF hJ hu hv hq),
    tree_step_iff_l I hZF hω hn hm hs hu, tree_step_iff_l I hZF hω hn hm ht hv, rp_subset_l I hJ hs ht hp hq]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2.2⟩⟩

/-- 同步延伸两个分量所得的配对仍是一个子节点。 -/
theorem fp_child_l (hZF : M.Models ZF) {ω A J r s t u v} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (h : Fp_d I ω J r s t)
    (hu : M.mem u A) (hv : M.mem v A) (hsu : Step_d I ω s u) (htv : Step_d I ω t v) :
    ∃ q, Fp_d I ω J q u v ∧ Step_d I ω r q := by
  obtain ⟨n, hn, hs, ht, _⟩ := h
  obtain ⟨m, hm, hu⟩ := (hA u).mp hu
  obtain ⟨l, hl, hv⟩ := (hA v).mp hv
  have sm := ((tree_step_iff_l I hZF hω hn hm hs hu).mp hsu).1
  have sl := ((tree_step_iff_l I hZF hω hn hl ht hv).mp htv).1
  have e := hZF.1.eq_of_same_members l m (fun x => (sl x).trans (sm x).symm)
  subst l
  obtain ⟨q, _, hq⟩ := rp_exists_l I hZF hJ hu hv
  have hp : Fp_d I ω J q u v := ⟨m, hm, hu, hv, hq⟩
  exact ⟨q, hp, (fp_step_l I hZF hω hJ ⟨n, hn, hs, ht, ‹Rp_d I J s t r›⟩ hp).mpr ⟨hsu, htv⟩⟩

end YesMetaZFC.SetTheory.Descriptive
