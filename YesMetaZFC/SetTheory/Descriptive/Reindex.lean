import YesMetaZFC.SetTheory.Descriptive.Continuous

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
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare a ha m hm with e | e | e
      · obtain ⟨u, hu, huω⟩ := hω.1.2 m hm
        exact ⟨u, huω, fun i hi => (hu i).mpr (Or.inl hi), (hZF.1.eq_of_same_members a m e).symm ▸ hu.predecessor_mem⟩
      · exact ⟨m, hm, fun _ => id, e⟩
      · obtain ⟨u, hu, huω⟩ := hω.1.2 a ha
        exact ⟨u, huω, fun i hi => (hu i).mpr (Or.inl (((hω.isOrdinal hZF).mem ha).transitive m e i hi)), hu.predecessor_mem⟩
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
