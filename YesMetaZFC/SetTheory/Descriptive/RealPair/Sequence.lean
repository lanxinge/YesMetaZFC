import YesMetaZFC.SetTheory.Descriptive.RealPair.Natural

/-! # 有限列和实数的逐坐标配对

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
@[prove_auto_norm semantic]
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
