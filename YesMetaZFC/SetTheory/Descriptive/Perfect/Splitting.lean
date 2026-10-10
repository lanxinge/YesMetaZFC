import YesMetaZFC.SetTheory.Descriptive.Perfect.Thin
import YesMetaZFC.SetTheory.Descriptive.MapIteration

/-! # 稳定核上的规范二分函数

在候选子节点对的内部自然数编号中取最小者，形成两个实际函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pin_not_sub_l {ω J a b} (hJ : Npair_d I ω J) (h : Pin_d I ω J a b) :
    ¬ M.MemberSubset a b ∧ ¬ M.MemberSubset b a := by
  obtain ⟨s, t, u, v, pa, pb, i, x, y, hx, hy, ne⟩ := h
  have inc {f g} (h : M.MemberSubset f g) {x} (hx : M.PairMember I i x f) : M.PairMember I i x g :=
    hx.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
  refine ⟨fun sub => ?_, fun sub => ?_⟩
  · have hu : M.IsSetFunction I u := pb.elim fun _ h => h.2.1.1
    exact ne (hu.2 i x y (inc ((fp_sub_l I hJ pa pb).mp sub).1 hx) hy)
  · have hs : M.IsSetFunction I s := pa.elim fun _ h => h.2.1.1
    exact ne (hs.2 i x y hx (inc ((fp_sub_l I hJ pb pa).mp sub).1 hy))

def Split_d (ω A J U L R : M.Domain) : Prop := M.MemberSubset U A ∧
  M.IsSetFunctionFromTo I L U U ∧ M.IsSetFunctionFromTo I R U U ∧
  ∀ a b c, M.PairMember I a b L → M.PairMember I a c R →
    M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c

theorem splitting_l (hZF : M.Models ZF) {ω A J U} (hω : M.IsOmega ω)
    (hc : M.CardinalLessOrEqual I A ω) (sub : M.MemberSubset U A)
    (split : ∀ a, M.mem a U → Sp_d I ω J U a) : ∃ L R, Split_d I ω A J U L R := by
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF I U U
  obtain ⟨A', hA'⟩ := ZF.exists_cartesianProduct hZF I A A
  obtain ⟨E', he'⟩ := ZF.countable_product_l I hZF hω hc hc hA'
  have psub : M.MemberSubset P A' := fun p h => ((hp p).mp h).elim fun b h => h.2.elim fun c h' =>
    (hA' p).mpr ⟨b, sub b h.1, c, sub c h'.1, h'.2⟩
  obtain ⟨E, he⟩ := ZF.exists_restriction hZF I E' P
  have hei : M.IsSetInjectionFromTo I E P ω := ⟨he.isSetFunctionFromTo he'.1 psub,
    fun a b i ha hb => he'.2 a b i ((he.2 a i).mp ha).2 ((he.2 b i).mp hb).2⟩
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) P U
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest) (.conj
    (.mem (.bound 1) (.bound 4)) (.conj (.mem .newest (.bound 4)) (.conj
    (Formula.subset (.bound 2) (.bound 1)) (.conj (Formula.subset (.bound 2) .newest)
    (pin_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 1) .newest))))))) }
  have hφ p a : φ.denote ρ p a ↔ ∃ b c, I.Codes p b c ∧ M.mem b U ∧ M.mem c U ∧
      M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, pin_sat_l I hZF.1]; rfl
  obtain ⟨Q, _, eqn⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ W
  let η : Env M 3 := ((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push E).push P
  let ψ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
    (nj_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have hs a p : ψ.denote η a p ↔ M.mem p P ∧ ∃ i, M.PairMember I p i E ∧ Nj_d I Q E P a i := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, nj_sat_l I hZF.1]; rfl
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := U) (target := P) (by
    intro a ha
    obtain ⟨_, b, c, hb, hc, hab, hac, pin⟩ := split a ha
    obtain ⟨p, pair⟩ := I.total b c
    have hpP := (hp p).mpr ⟨b, hb, c, hc, pair⟩
    obtain ⟨i, hi⟩ := nj_exists_l I hZF hei.1 ⟨p, hpP,
      (eqn p a).mpr ⟨(hw p).mpr (Or.inl hpP), (hw a).mpr (Or.inr ha), (hφ p a).mpr ⟨b, c, pair, hb, hc, hab, hac, pin⟩⟩, hpP⟩
    obtain ⟨q, hq, _, hqi⟩ := hi.1
    exact ⟨q, (hs a q).mpr ⟨hq, i, hqi, hi⟩⟩) (by
      intro a _ p q ha hb
      obtain ⟨_, i, hpi, hi⟩ := (hs a p).mp ha
      obtain ⟨_, j, hqj, hj⟩ := (hs a q).mp hb
      exact hei.2 p q i hpi (nj_unique_l I hZF.1 (hω.isOrdinal hZF) hei.1 hj hi ▸ hqj))
    (fun a p _ h => ((hs a p).mp h).1)
  have selected {a p} (h : M.PairMember I a p F) : ∃ b c, I.Codes p b c ∧ M.mem b U ∧ M.mem c U ∧
      M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c := by
    obtain ⟨_, i, hpi, hi⟩ := (hs a p).mp ((ef a p).mp h).2
    obtain ⟨q, _, hqa, hqi⟩ := hi.1
    have e := hei.2 q p i hqi hpi
    exact (hφ p a).mp ((eqn p a).mp (e ▸ hqa)).2.2
  let δ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let χ (b : Bool) : BinarySchema 1 := {
    body := .existsE (.existsE (.conj
      (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 4))
      (𝒞.code (.bound 1) (if b then .newest else .bound 2) (if b then .bound 2 else .newest))))
    freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have hχ b a x : (χ b).denote δ a x ↔ ∃ p y, M.PairMember I a p F ∧ I.Codes p (if b then y else x) (if b then x else y) := by
    cases b <;> simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff] <;> rfl
  have build (b : Bool) : ∃ L, M.IsSetFunctionFromTo I L U U ∧ ∀ a x,
      M.PairMember I a x L ↔ M.mem a U ∧ ∃ p y, M.PairMember I a p F ∧ I.Codes p (if b then y else x) (if b then x else y) := by
    obtain ⟨L, hl, el⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I (χ b) δ (source := U) (target := U) (by
      intro a ha
      obtain ⟨p, hpP, hap⟩ := hf.2.2 a ha
      obtain ⟨x, hx, y, hy, pair⟩ := (hp p).mp hpP
      cases b
      · exact ⟨x, (hχ false a x).mpr ⟨p, y, hap, pair⟩⟩
      · exact ⟨y, (hχ true a y).mpr ⟨p, x, hap, pair⟩⟩) (by
      intro a _ x y hx hy
      obtain ⟨p, u, hap, px⟩ := (hχ b a x).mp hx
      obtain ⟨q, v, haq, py⟩ := (hχ b a y).mp hy
      have e := I.injective px (hf.1.2 a q p haq hap ▸ py)
      cases b
      · exact e.1
      · exact e.2) (by
      intro a x _ hx
      obtain ⟨p, y, hap, pair⟩ := (hχ b a x).mp hx
      obtain ⟨u, hu, v, hv, pair'⟩ := (hp p).mp (hf.output_mem_of_pairMember hap)
      have e := I.injective pair pair'
      cases b
      · have ex : x = u := by simpa only [Bool.false_eq_true, ↓reduceIte] using e.1
        exact ex.symm ▸ hu
      · have ex : x = v := by simpa only [↓reduceIte] using e.2
        exact ex.symm ▸ hv)
    exact ⟨L, hl, fun a x => (el a x).trans (and_congr_right fun _ => hχ b a x)⟩
  obtain ⟨L, hl, el⟩ := build false
  obtain ⟨R, hr, er⟩ := build true
  refine ⟨L, R, sub, hl, hr, fun a b c hab hac => ?_⟩
  obtain ⟨_, p, v, hap, pair⟩ := (el a b).mp hab
  obtain ⟨_, q, u, haq, pair'⟩ := (er a c).mp hac
  obtain ⟨eu, ev⟩ := I.injective pair (hf.1.2 a q p haq hap ▸ pair')
  simp only [Bool.false_eq_true, ↓reduceIte] at eu ev
  subst u v
  obtain ⟨x, y, pxy, _, _, incb, incc, pin⟩ := selected hap
  obtain ⟨rfl, rfl⟩ := I.injective pxy pair
  exact ⟨incb, incc, pin⟩

end YesMetaZFC.SetTheory.Descriptive
