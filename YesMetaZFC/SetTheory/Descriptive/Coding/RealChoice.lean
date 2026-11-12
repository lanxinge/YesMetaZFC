import YesMetaZFC.SetTheory.Descriptive.Topology.Continuous

/-! # 任意内部坐标重编号诱导连续实数映射 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem omega_fn_bound_l (hZF : M.Models ZF) {ω E} (hω : M.IsOmega ω)
    (he : M.IsSetFunctionFromTo I E ω ω) : ∀ n, M.mem n ω →
      ∃ m, M.mem m ω ∧ ∀ i k, M.mem i n → M.PairMember I i k E → M.mem k m := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push E
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (.forallE (.forallE
    (.imp (.mem (.bound 1) (.bound 3)) (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem .newest (.bound 2)))))) }
  have hp n : φ.denote ρ n ↔ ∃ m, M.mem m ω ∧ ∀ i k, M.mem i n → M.PairMember I i k E → M.mem k m := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  apply hω.induction
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz
    obtain ⟨m, _, hm⟩ := hω.1.1
    exact ⟨m, hm, fun i _ hi _ => (hz i hi).elim⟩
  · rintro n hn ⟨m, hm, bound⟩ l hl
    obtain ⟨a, ha, hna⟩ := he.2.2 n hn
    have upper : ∃ u, M.mem u ω ∧ M.MemberSubset m u ∧ M.mem a u := by
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare a ha m hm with e | e | e
      · obtain ⟨u, hu, huω⟩ := hω.1.2 m hm
        exact ⟨u, huω, fun i hi => (hu i).mpr (Or.inl hi), (hZF.1.eq_of_same_members a m e).symm ▸ hu.predecessor_mem⟩
      · exact ⟨m, hm, fun _ => id, e⟩
      · obtain ⟨u, hu, huω⟩ := hω.1.2 a ha
        exact ⟨u, huω, fun i hi => (hu i).mpr (Or.inl (((hω.isOrdinal (ZF.modelsKP hZF)).mem ha).transitive m e i hi)), hu.predecessor_mem⟩
    obtain ⟨u, hu, hmu, hau⟩ := upper
    exact ⟨u, hu, fun i k hi hik => ((hl i).mp hi).elim (fun hi => hmu k (bound i k hi hik))
      (fun e => (he.1.2 n a k hna (hZF.1.eq_of_same_members i n e ▸ hik)) ▸ hau)⟩

def Re_d (E x y : M.Domain) : Prop := M.IsSetRelation I y ∧ ∀ i v,
  M.PairMember I i v y ↔ ∃ j, M.PairMember I i j E ∧ M.PairMember I j v x
def re_m {d} (E x y : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 y) (.forallE (.forallE
  (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest y.weaken.weaken) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest E.weaken.weaken.weaken)
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) x.weaken.weaken.weaken))))))
derive_free_closed re_m
theorem re_sat_l {d} (ρ : Env M d) (E x y : Term d) :
    Formula.satisfies ρ (re_m (𝒞 := 𝒞) E x y) ↔ Re_d I (E.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [re_m, Re_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, Definitional.Term.eval_weaken]; rfl

theorem re_unique_l (hE : Extensional M) {E x y z} (h : Re_d I E x y) (k : Re_d I E x z) : y = z :=
  h.1.eq_of_pairMember_iff hE k.1 (fun i v => (h.2 i v).trans (k.2 i v).symm)

theorem re_exists_l (hZF : M.Models ZF) {ω E x} (he : M.IsSetFunctionFromTo I E ω ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) : ∃ y, M.IsSetFunctionFromTo I y ω ω ∧ Re_d I E x y := by
  obtain ⟨y, hy, ey⟩ := ZF.exists_compositionFunction hZF I he hx
  exact ⟨y, hy, hy.1.1, fun i v => (ey i v).trans
    ⟨And.right, fun ⟨j, hij, hjv⟩ => ⟨he.input_mem_of_pairMember hij, j, hij, hjv⟩⟩⟩

def Rg_d (B E f : M.Domain) : Prop := M.IsSetFunctionFromTo I f B B ∧ ∀ x y,
  M.PairMember I x y f ↔ M.mem x B ∧ Re_d I E x y
def rg_m {d} (B E f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f B B)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (.conj (.mem (.bound 1) B.weaken.weaken) (re_m (𝒞 := 𝒞) E.weaken.weaken (.bound 1) .newest)))))
derive_free_closed rg_m
theorem rg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B E f : Term d) :
    Formula.satisfies ρ (rg_m (𝒞 := 𝒞) B E f) ↔ Rg_d I (B.eval ρ) (E.eval ρ) (f.eval ρ) := by
  simp only [rg_m, Rg_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, re_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rg_unique_l (hE : Extensional M) {B E f g} (h : Rg_d I B E f) (k : Rg_d I B E g) : f = g :=
  h.1.1.1.eq_of_pairMember_iff hE k.1.1.1 (fun x y => (h.2 x y).trans (k.2 x y).symm)

theorem rg_exists_l (hZF : M.Models ZF) {ω B E} (hB : Baire_d I ω B)
    (he : M.IsSetFunctionFromTo I E ω ω) : ∃ f, Rg_d I B E f := by
  let ρ : Env M 1 := ⟨fun _ => E, fun _ => E⟩
  let φ : BinarySchema 1 := { body := re_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  have hp x y : φ.denote ρ x y ↔ Re_d I E x y := re_sat_l I _ _ _ _
  obtain ⟨f, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (fun x hx => (re_exists_l I hZF he ((hB.2 x).mp hx)).imp fun y h => (hp x y).mpr h.2)
    (fun _ _ _ _ h k => re_unique_l I hZF.1 ((hp _ _).mp h) ((hp _ _).mp k))
    (by
      intro x y hx hy
      obtain ⟨z, hz, hz'⟩ := re_exists_l I hZF he ((hB.2 x).mp hx)
      exact re_unique_l I hZF.1 hz' ((hp x y).mp hy) ▸ (hB.2 z).mpr hz)
  exact ⟨f, hf, fun x y => (ef x y).trans (and_congr_right fun _ => hp x y)⟩

theorem rg_cont_l (hZF : M.Models ZF) {ω A B E f} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetFunctionFromTo I E ω ω) (hf : Rg_d I B E f) : Cont_d I A B f := by
  refine ⟨hf.1, fun x y s hxy hs hsy => ?_⟩
  have hx := (hB.2 x).mp (hf.1.input_mem_of_pairMember hxy)
  obtain ⟨n, hn, hsf⟩ := (hA s).mp hs
  obtain ⟨m, hm, bound⟩ := omega_fn_bound_l I hZF hB.1 he n hn
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 hx hm
  refine ⟨t, (hA t).mpr ⟨m, hm, ht⟩, (ds_restrict_iff_l I ht hx.1).mp hr, fun x' y' hxy' htx' p hp => ?_⟩
  obtain ⟨i, v, hi⟩ := hsf.1.1 p hp
  obtain ⟨j, hij, hjv⟩ := (((hf.2 x y).mp hxy).2.2 i v).mp ⟨p, hi, hsy p hp⟩
  have hj := bound i j (hsf.input_mem_of_pairMember ⟨p, hi, hp⟩) hij
  obtain ⟨q, hq, hqt⟩ := (hr.2 j v).mpr ⟨hj, hjv⟩
  obtain ⟨r, hr', hry⟩ := (((hf.2 x' y').mp hxy').2.2 i v).mpr ⟨j, hij, q, hq, htx' q hqt⟩
  exact (I.unique hi hr').symm ▸ hry

end YesMetaZFC.SetTheory.Descriptive

/-! ## 一个内部实数编码可数列实数

第 i 行的第 j 项读取自然数配对 J(i,j) 处的值。逐坐标实数配对与取行交换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Row_d (J i w x : M.Domain) : Prop := M.IsSetRelation I x ∧ ∀ j v,
  M.PairMember I j v x ↔ ∃ k, Np_d I J i j k ∧ M.PairMember I k v w
def row_m {d} (J i w x : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 x) (.forallE (.forallE
  (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest x.weaken.weaken) (.existsE (.conj
    (np_m (𝒞 := 𝒞) J.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 2) .newest)
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) w.weaken.weaken.weaken))))))
derive_free_closed row_m
theorem row_sat_l {d} (ρ : Env M d) (J i w x : Term d) :
    Formula.satisfies ρ (row_m (𝒞 := 𝒞) J i w x) ↔ Row_d I (J.eval ρ) (i.eval ρ) (w.eval ρ) (x.eval ρ) := by
  simp only [row_m, Row_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, np_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem row_unique_l (hE : Extensional M) {J i w x y} (h : Row_d I J i w x) (k : Row_d I J i w y) : x = y :=
  h.1.eq_of_pairMember_iff hE k.1 (fun j v => (h.2 j v).trans (k.2 j v).symm)

theorem row_index_l (hZF : M.Models ZF) {ω J i} (hJ : Npair_d I ω J) (hi : M.mem i ω) :
    ∃ E, M.IsSetFunctionFromTo I E ω ω ∧ ∀ j k, M.PairMember I j k E ↔ Np_d I J i j k := by
  let ρ : Env M 2 := (⟨fun _ => J, fun _ => J⟩ : Env M 1).push i
  let φ : BinarySchema 2 := { body := np_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp j k : φ.denote ρ j k ↔ Np_d I J i j k := np_sat_l I _ _ _ _ _
  obtain ⟨E, he, eqn⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun j hj => (np_total_l I hJ hi hj).imp fun k h => (hp j k).mpr h.2)
    (fun _ _ _ _ h k => np_unique_l I hJ ((hp _ _).mp h) ((hp _ _).mp k))
    (fun _ _ _ h => (np_type_l I hJ ((hp _ _).mp h)).2.2)
  exact ⟨E, he, fun j k => ((eqn j k).trans (and_congr_right fun _ => hp j k)).trans
    ⟨And.right, fun h => ⟨(np_type_l I hJ h).2.1, h⟩⟩⟩

theorem row_exists_l (hZF : M.Models ZF) {ω J i w} (hJ : Npair_d I ω J) (hi : M.mem i ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) : ∃ x, M.IsSetFunctionFromTo I x ω ω ∧ Row_d I J i w x := by
  obtain ⟨E, he, eqn⟩ := row_index_l I hZF hJ hi
  obtain ⟨x, hx, hr⟩ := re_exists_l I hZF he hw
  exact ⟨x, hx, hr.1, fun j v => (hr.2 j v).trans (exists_congr fun k => and_congr_left fun _ => eqn j k)⟩

def Rmap_d (B J i f : M.Domain) : Prop := M.IsSetFunctionFromTo I f B B ∧ ∀ w x,
  M.PairMember I w x f ↔ M.mem w B ∧ Row_d I J i w x
def rmap_m {d} (B J i f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f B B)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (.conj (.mem (.bound 1) B.weaken.weaken) (row_m (𝒞 := 𝒞) J.weaken.weaken i.weaken.weaken (.bound 1) .newest)))))
derive_free_closed rmap_m
theorem rmap_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J i f : Term d) :
    Formula.satisfies ρ (rmap_m (𝒞 := 𝒞) B J i f) ↔ Rmap_d I (B.eval ρ) (J.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [rmap_m, Rmap_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, row_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rmap_unique_l (hE : Extensional M) {B J i f g} (h : Rmap_d I B J i f) (k : Rmap_d I B J i g) : f = g :=
  h.1.1.1.eq_of_pairMember_iff hE k.1.1.1 (fun x y => (h.2 x y).trans (k.2 x y).symm)

theorem rmap_exists_l (hZF : M.Models ZF) {ω A B J i} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hi : M.mem i ω) :
    ∃ f, Rmap_d I B J i f ∧ Cont_d I A B f := by
  obtain ⟨E, he, eqn⟩ := row_index_l I hZF hJ hi
  obtain ⟨f, hf⟩ := rg_exists_l I hZF hB he
  have eqv w x : Re_d I E w x ↔ Row_d I J i w x := and_congr_right fun _ =>
    forall_congr' fun j => forall_congr' fun v => iff_congr Iff.rfl (exists_congr fun k => and_congr_left fun _ => eqn j k)
  exact ⟨f, ⟨hf.1, fun w x => (hf.2 w x).trans (and_congr_right fun _ => eqv w x)⟩, rg_cont_l I hZF hB hA he hf⟩

/-- 取行与逐坐标配对交换，量词运算因此不需要额外的实数重括号。 -/
theorem row_pair_l {ω J i w v p x y z} (hJ : Npair_d I ω J)
    (hx : Row_d I J i w x) (hy : Row_d I J i v y) (hp : Rp_d I J w v p)
    (hz : Rp_d I J x y z) : Row_d I J i p z := by
  refine ⟨hz.1, fun j a => ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨b, c, hb, hc, hbc⟩ := (hz.2 j a).mp h
    obtain ⟨k, hk, hkb⟩ := (hx.2 j b).mp hb
    obtain ⟨l, hl, hlc⟩ := (hy.2 j c).mp hc
    exact ⟨k, hk, (hp.2 k a).mpr ⟨b, c, hkb, np_unique_l I hJ hl hk ▸ hlc, hbc⟩⟩
  · rintro ⟨k, hk, hka⟩
    obtain ⟨b, c, hb, hc, hbc⟩ := (hp.2 k a).mp hka
    exact (hz.2 j a).mpr ⟨b, c, (hx.2 j b).mpr ⟨k, hk, hb⟩, (hy.2 j c).mpr ⟨k, hk, hc⟩, hbc⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 实数行列的内部编码与常行对角映射 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem array_encode_l (hZF : M.Models ZF) {ω B J D H} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hD : M.MemberSubset D ω) (hH : M.IsSetFunctionFromTo I H D B) :
    ∃ w, M.mem w B ∧ ∀ i x, M.PairMember I i x H → Row_d I J i w x := by
  classical
  obtain ⟨z, _, hz⟩ := hB.1.1.1
  let ρ : Env M 4 := (((⟨fun _ => J, fun _ => J⟩ : Env M 1).push D).push H).push z
  let φ : BinarySchema 4 := { body := .existsE (.existsE (.conj
    (np_m (𝒞 := 𝒞) (.bound 7) (.bound 1) .newest (.bound 3)) (.disj
    (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 6))
      (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) .newest)))
    (.conj (.neg (.mem (.bound 1) (.bound 6))) (Formula.extensionalEq (.bound 2) (.bound 4)))))) }
  have hp k v : φ.denote ρ k v ↔ ∃ i j, Np_d I J i j k ∧
      ((∃ x, M.PairMember I i x H ∧ M.PairMember I j v x) ∨ (¬ M.mem i D ∧ v = z)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, np_sat_l I, Formula.satisfies_disj_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨w, hw, ew⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (by
      intro k hk
      obtain ⟨i, j, _, hj, hij⟩ := np_surj_l I hJ hk
      by_cases hi : M.mem i D
      · obtain ⟨x, hx, hix⟩ := hH.2.2 i hi
        obtain ⟨v, _, hjv⟩ := ((hB.2 x).mp hx).2.2 j hj
        exact ⟨v, (hp k v).mpr ⟨i, j, hij, Or.inl ⟨x, hix, hjv⟩⟩⟩
      · exact ⟨z, (hp k z).mpr ⟨i, j, hij, Or.inr ⟨hi, rfl⟩⟩⟩)
    (by
      intro k _ v u hv hu
      obtain ⟨i, j, hij, hv⟩ := (hp k v).mp hv
      obtain ⟨i', j', hij', hu⟩ := (hp k u).mp hu
      obtain ⟨ei, ej⟩ := np_injective_l I hJ hij' hij
      subst i' j'
      rcases hv with ⟨x, hx, hjv⟩ | ⟨hi, rfl⟩ <;> rcases hu with ⟨y, hy, hju⟩ | ⟨hi', rfl⟩
      · exact ((hB.2 x).mp (hH.output_mem_of_pairMember hx)).1.2 j v u hjv (hH.1.2 i y x hy hx ▸ hju)
      · exact (hi' (hH.input_mem_of_pairMember hx)).elim
      · exact (hi (hH.input_mem_of_pairMember hy)).elim
      · rfl)
    (by
      intro k v _ hv
      obtain ⟨i, j, _, hv⟩ := (hp k v).mp hv
      exact hv.elim (fun ⟨x, hx, hjv⟩ => ((hB.2 x).mp (hH.output_mem_of_pairMember hx)).output_mem_of_pairMember hjv)
        (fun h => h.2.symm ▸ hz))
  refine ⟨w, (hB.2 w).mpr hw, fun i x hix => ⟨((hB.2 x).mp (hH.output_mem_of_pairMember hix)).1.1, fun j v => ⟨?_, ?_⟩⟩⟩
  · intro hjv
    obtain ⟨k, hk, hik⟩ := np_total_l I hJ (hD i (hH.input_mem_of_pairMember hix))
      (((hB.2 x).mp (hH.output_mem_of_pairMember hix)).input_mem_of_pairMember hjv)
    exact ⟨k, hik, (ew k v).mpr ⟨hk, (hp k v).mpr ⟨i, j, hik, Or.inl ⟨x, hix, hjv⟩⟩⟩⟩
  · rintro ⟨k, hik, hkv⟩
    obtain ⟨i', j', hij', hv⟩ := (hp k v).mp ((ew k v).mp hkv).2
    obtain ⟨ei, ej⟩ := np_injective_l I hJ hij' hik
    subst i' j'
    exact hv.elim (fun ⟨y, hiy, hjv⟩ => hH.1.2 i y x hiy hix ▸ hjv)
      (fun h => (h.1 (hH.input_mem_of_pairMember hix)).elim)

/-- 常行对角 x↦(x,x,…) 是实际连续函数，无需选择公理。 -/
theorem array_diag_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ x w, M.PairMember I x w f → ∀ i, M.mem i ω → Row_d I J i w x := by
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := { body := .existsE (np_m (𝒞 := 𝒞) (.bound 3) .newest (.bound 1) (.bound 2)) }
  have hp k j : φ.denote ρ k j ↔ ∃ i, Np_d I J i j k := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, np_sat_l I]; rfl
  obtain ⟨E, he, ee⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun k hk => (np_surj_l I hJ hk).elim fun i h => h.elim fun j h => ⟨j, (hp k j).mpr ⟨i, h.2.2⟩⟩)
    (fun _ _ _ _ h k => ((hp _ _).mp h).elim fun _ h => ((hp _ _).mp k).elim fun _ k => (np_injective_l I hJ h k).2)
    (fun _ _ _ h => ((hp _ _).mp h).elim fun _ h => (np_type_l I hJ h).2.1)
  obtain ⟨f, hf⟩ := rg_exists_l I hZF hB he
  refine ⟨f, rg_cont_l I hZF hB hA he hf, fun x w hxw i hi => ?_⟩
  have hx := (hB.2 x).mp (hf.1.input_mem_of_pairMember hxw)
  have hr := ((hf.2 x w).mp hxw).2
  refine ⟨hx.1.1, fun j v => ⟨?_, ?_⟩⟩
  · intro hjv
    obtain ⟨k, hk, hik⟩ := np_total_l I hJ hi (hx.input_mem_of_pairMember hjv)
    exact ⟨k, hik, (hr.2 k v).mpr ⟨j, (ee k j).mpr ⟨hk, (hp k j).mpr ⟨i, hik⟩⟩, hjv⟩⟩
  · rintro ⟨k, hik, hkv⟩
    obtain ⟨j', hkj, hjv⟩ := (hr.2 k v).mp hkv
    obtain ⟨i', hij'⟩ := (hp k j').mp ((ee k j').mp hkj).2
    exact (np_injective_l I hJ hij' hik).2 ▸ hjv

theorem row_mem_l (hZF : M.Models ZF) {ω B J i w x} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hi : M.mem i ω) (hw : M.mem w B) (h : Row_d I J i w x) : M.mem x B := by
  obtain ⟨y, hy, hr⟩ := row_exists_l I hZF hJ hi ((hB.2 w).mp hw)
  exact row_unique_l I hZF.1 hr h ▸ (hB.2 y).mpr hy

theorem row_surj_l (hZF : M.Models ZF) {ω B J x} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hx : M.mem x B) : ∃ w, M.mem w B ∧ ∀ i, M.mem i ω → Row_d I J i w x := by
  obtain ⟨H, hH, eh⟩ := ZF.exists_constantFunction hZF I (source := ω) hx
  obtain ⟨w, hw, hr⟩ := array_encode_l I hZF hB hJ (fun _ => id) hH
  exact ⟨w, hw, fun i hi => hr i x ((eh i x).mpr ⟨hi, rfl⟩)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 仅对内部实数使用的可数选择

可数交的见证交换只需要 AC_ω(B)，并不要求模型满足整个选择公理。
下方从已有 ZFC 集合关系单值化给出实际实例，所有输出仍是模型内函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 仅在当前指标集上选择实数；有限指标实例由 ZF 直接构造。 -/
def Cc_d (D B : M.Domain) : Prop := ∀ R,
  (∀ i, M.mem i D → ∃ x, M.mem x B ∧ M.PairMember I i x R) →
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → M.PairMember I i x R
def Fcc_d (B H : M.Domain) : Prop := ∀ D, M.IsDomainOf I D H → Cc_d I D B

def cc_m {d} (D B : Term d) : Formula 1 d := .forallE (.imp
  (Formula.forallMem D.weaken (Formula.existsMem B.weaken.weaken
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))))
  (.existsE (.conj (Formula.isFunctionFromTo 𝒞 .newest D.weaken.weaken B.weaken.weaken)
    (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))))
derive_free_closed cc_m
theorem cc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D B : Term d) :
    Formula.satisfies ρ (cc_m (𝒞 := 𝒞) D B) ↔ Cc_d I (D.eval ρ) (B.eval ρ) := by
  simp only [cc_m, Cc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Definitional.Term.eval_weaken]; rfl
def fcc_m {d} (B H : Term d) : Formula 1 d := .forallE (.imp (Formula.isDomain 𝒞 .newest H.weaken)
  (cc_m (𝒞 := 𝒞) .newest B.weaken))
derive_free_closed fcc_m
theorem fcc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B H : Term d) :
    Formula.satisfies ρ (fcc_m (𝒞 := 𝒞) B H) ↔ Fcc_d I (B.eval ρ) (H.eval ρ) := by
  simp only [fcc_m, Fcc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isDomain_iff I, cc_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Rcc_d (ω B : M.Domain) : Prop := ∀ D R, M.MemberSubset D ω →
  (∀ i, M.mem i D → ∃ x, M.mem x B ∧ M.PairMember I i x R) →
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → M.PairMember I i x R
def rcc_m {d} (ω B : Term d) : Formula 1 d := .forallE (.forallE
  (.imp (Formula.subset (.bound 1) ω.weaken.weaken) (.imp
    (Formula.forallMem (.bound 1) (Formula.existsMem B.weaken.weaken.weaken (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))))
    (.existsE (.conj (Formula.isFunctionFromTo 𝒞 .newest (.bound 2) B.weaken.weaken.weaken)
      (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))))))
derive_free_closed rcc_m
theorem rcc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B : Term d) :
    Formula.satisfies ρ (rcc_m (𝒞 := 𝒞) ω B) ↔ Rcc_d I (ω.eval ρ) (B.eval ρ) := by
  simp only [rcc_m, Rcc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Definitional.Term.eval_weaken]; rfl

theorem rcc_zfc_l (hZFC : M.Models ZFC) (ω B : M.Domain) : Rcc_d I ω B :=
  fun _ _ _ ht => ZFC.uniformize_l I hZFC ht

theorem cc_schema_l (hZF : M.Models ZF) {B D} (h : Cc_d I D B)
    {d} (φ : BinarySchema d) (ρ : Env M d)
    (ht : ∀ i, M.mem i D → ∃ x, M.mem x B ∧ φ.denote ρ i x) :
    ∃ F, M.IsSetFunctionFromTo I F D B ∧ ∀ i x, M.PairMember I i x F → φ.denote ρ i x := by
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D B
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  obtain ⟨F, hf, he⟩ := h R (fun i hi => (ht i hi).elim fun x hx =>
    ⟨x, hx.1, (hr i x).mpr ⟨(hW i).mpr (Or.inl hi), (hW x).mpr (Or.inr hx.1), hx.2⟩⟩)
  exact ⟨F, hf, fun i x hx => ((hr i x).mp (he i x hx)).2.2⟩

theorem fcc_real_l {ω B H} (h : Rcc_d I ω B) (hH : ∀ i p, M.PairMember I i p H → M.mem i ω) : Fcc_d I B H :=
  fun D hd R ht => h D R (fun i hi => ((hd i).mp hi).elim fun p hp => hH i p hp) ht

end YesMetaZFC.SetTheory.Descriptive
