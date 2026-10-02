import YesMetaZFC.SetTheory.Descriptive.Convergence
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

/-! # 前缀距离的规范有理数码

距离值是实际有序对 (0,1) 或 (1,2ⁿ)，指数及幂均由模型解释。只对这组规范
非负分数比较大小：零最小，正单位分数按分母反序。ω 用作零距离的指数标记。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Dyad_d (ω D z o n q : M.Domain) : Prop :=
  (n = ω ∧ I.Codes q z o) ∨ (M.mem n ω ∧ ∃ p, M.mem p ω ∧
    M.IsOrdinalExponentiation I p D n ∧ I.Codes q o p)
def Qle_d (z o q r : M.Domain) : Prop := (∃ p, I.Codes q z p) ∨
  ∃ p t, I.Codes q o p ∧ I.Codes r o t ∧ M.MemberSubset t p

def dyad_m {d} (ω D z o n q : Term d) : Formula 1 d := .disj
  (.conj (Formula.extensionalEq n ω) (𝒞.code q z o)) (.conj (.mem n ω) (.existsE
    (.conj (.mem .newest ω.weaken) (.conj (Formula.isOrdinalExponentiation 𝒞 .newest D.weaken n.weaken)
      (𝒞.code q.weaken o.weaken .newest)))))
derive_free_closed dyad_m
def qle_m {d} (z o q r : Term d) : Formula 1 d := .disj
  (.existsE (𝒞.code q.weaken z.weaken .newest)) (.existsE (.existsE (.conj
    (𝒞.code q.weaken.weaken o.weaken.weaken (.bound 1)) (.conj
      (𝒞.code r.weaken.weaken o.weaken.weaken .newest) (Formula.subset .newest (.bound 1))))))
derive_free_closed qle_m
theorem dyad_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o n q : Term d) :
    Formula.satisfies ρ (dyad_m (𝒞 := 𝒞) ω D z o n q) ↔
      Dyad_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (n.eval ρ) (q.eval ρ) := by
  simp only [dyad_m, Dyad_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, I.satisfies_code_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isOrdinalExponentiation_iff I hE,
    Definitional.Term.eval_weaken]; rfl
theorem qle_sat_l {d} (ρ : Env M d) (z o q r : Term d) :
    Formula.satisfies ρ (qle_m (𝒞 := 𝒞) z o q r) ↔
      Qle_d I (z.eval ρ) (o.eval ρ) (q.eval ρ) (r.eval ρ) := by
  simp only [qle_m, Qle_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, I.satisfies_code_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]; rfl

theorem dyad_exists_l (hZF : M.Models ZF) {ω D z o n} (hω : M.IsOmega ω)
    (hD : M.mem D ω) (hn : n = ω ∨ M.mem n ω) : ∃ q, Dyad_d I ω D z o n q := by
  rcases hn with rfl | hn
  · obtain ⟨q, hq⟩ := I.total z o
    exact ⟨q, Or.inl ⟨rfl, hq⟩⟩
  · obtain ⟨p, hp, _⟩ := ZF.ordinalExponentiation_existsUnique hZF I
      ((hω.isOrdinal hZF).mem hD) ((hω.isOrdinal hZF).mem hn)
    obtain ⟨q, hq⟩ := I.total o p
    exact ⟨q, Or.inr ⟨hn, p, ZF.ordinalExponentiation_mem_omega hZF I hω hD hn hp, hp, hq⟩⟩

theorem dyad_unique_l (hZF : M.Models ZF) {ω D z o n q r} (hω : M.IsOmega ω)
    (hD : M.IsOrdinal D) (hq : Dyad_d I ω D z o n q) (hr : Dyad_d I ω D z o n r) : q = r := by
  rcases hq with ⟨en, hq⟩ | ⟨hn, p, _, hp, hq⟩ <;>
    rcases hr with ⟨e, hr⟩ | ⟨hn', t, _, ht, hr⟩
  · exact I.unique hq hr
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (en ▸ hn')).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (e ▸ hn)).elim
  · obtain ⟨v, _, hv⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD ((hω.isOrdinal hZF).mem hn)
    have e := (hv p hp).trans (hv t ht).symm
    subst t
    exact I.unique hq hr

omit I in
theorem ds_nat_le_l (hE : Extensional M) {ω i j : M.Domain} (hω : M.IsOrdinal ω)
    (hi : M.mem i ω) (hj : M.mem j ω) : M.MemberSubset i j ↔ i = j ∨ M.mem i j := by
  refine ⟨fun h => ?_, fun h => h.elim (fun e => e ▸ (fun _ h => h)) ((hω.mem hj).transitive i)⟩
  rcases hω.wellOrder.linear.compare i hi j hj with he | hij | hji
  · exact Or.inl (hE.eq_of_same_members i j he)
  · exact Or.inr hij
  · exact (hω.wellOrder.linear.irrefl j hj (h j hji)).elim

/-- 单位分数的数值次序恰是指数的反序；零距离作为最大指数。 -/
theorem dyad_le_l (hZF : M.Models ZF) {ω D z o n m q r} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hq : Dyad_d I ω D z o n q) (hr : Dyad_d I ω D z o m r) :
    Qle_d I z o q r ↔ n = ω ∨ m = n ∨ M.mem m n := by
  have hD := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  have hzo : o ≠ z := fun e => ho.elim fun a ha => hz a (e ▸ ha.2.predecessor_mem)
  rcases hq with ⟨en, hq⟩ | ⟨hn, p, hpω, hp, hq⟩
  · exact iff_of_true (Or.inl ⟨o, hq⟩) (Or.inl en)
  · have hne : n ≠ ω := fun e => KP.mem_irrefl_d (ZF.modelsKP hZF) ω (e ▸ hn)
    rcases hr with ⟨em, hr⟩ | ⟨hm, t, htω, ht, hr⟩
    · refine iff_of_false ?_ ?_
      · rintro (⟨p', h⟩ | ⟨p', t', h, k, _⟩)
        · exact hzo (I.injective hq h).1
        · exact hzo (I.injective k hr).1
      · rintro (e | e | h)
        · exact hne e
        · exact hne (e.symm.trans em)
        · exact KP.mem_irrefl_d (ZF.modelsKP hZF) ω (hω.transitive hZF n hn ω (em ▸ h))
    · have order : M.MemberSubset t p ↔ m = n ∨ M.mem m n := by
        rw [ds_nat_le_l hZF.1 (hω.isOrdinal hZF) htω hpω]
        apply or_congr
        · refine ⟨fun e => ZF.ordinalExponentiation_exponent_injective hZF I hD ho hd.predecessor_mem
            ((hω.isOrdinal hZF).mem hm) ((hω.isOrdinal hZF).mem hn) (e ▸ ht) hp, fun e => ?_⟩
          subst m
          obtain ⟨v, _, hv⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD ((hω.isOrdinal hZF).mem hn)
          exact (hv t ht).trans (hv p hp).symm
        · exact ZF.ordinalExponentiation_values_mem_iff hZF I hD ho hd.predecessor_mem
            ((hω.isOrdinal hZF).mem hm) ((hω.isOrdinal hZF).mem hn) ht hp
      refine ⟨fun h => Or.inr (order.mp ?_), fun h => ?_⟩
      · rcases h with ⟨v, hv⟩ | ⟨v, w, hv, hw, h⟩
        · exact (hzo (I.injective hq hv).1).elim
        · have ev := (I.injective hv hq).2
          have ew := (I.injective hw hr).2
          exact ev ▸ ew ▸ h
      · exact Or.inr ⟨p, t, hq, hr, order.mpr (h.resolve_left hne)⟩

omit I in
/-- 内部归纳集直接提供 0、1、2 的实际实例。 -/
theorem ds_digits_l {ω : M.Domain} (hω : M.IsOmega ω) : ∃ z o D,
    (∀ x, ¬ M.mem x z) ∧ M.mem z ω ∧ M.IsOrdinalOne o ∧ M.mem o ω ∧
    M.SuccessorOf D o ∧ M.mem D ω := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  obtain ⟨D, hd, hdω⟩ := hω.1.2 o hoω
  exact ⟨z, o, D, hz, hzω, ⟨z, hz, ho⟩, hoω, hd, hdω⟩

/-- 正距离的分母非零，因此实际有理数码不含零分母。 -/
theorem dyad_denominator_pos_l (hZF : M.Models ZF) {ω D o n p} (hω : M.IsOmega ω)
    (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o) (hn : M.mem n ω)
    (hp : M.IsOrdinalExponentiation I p D n) : ∃ a, M.mem a p :=
  ZF.ordinalExponentiation_isNonemptyOnOrdinals hZF I
    (Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩) ⟨o, hd.predecessor_mem⟩
    n ((hω.isOrdinal hZF).mem hn) p hp

/-- 2 的幂在内部自然数中无界；这些单位分数构成趋向零的共尾尺度。 -/
theorem dyad_cofinal_l (hZF : M.Models ZF) {ω D o m} (hω : M.IsOmega ω)
    (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o) (hm : M.mem m ω) :
    ∃ n p, M.mem n ω ∧ M.mem p ω ∧ M.IsOrdinalExponentiation I p D n ∧ M.mem m p := by
  have hD : M.IsOrdinal D := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  obtain ⟨n, hn, hnω⟩ := hω.1.2 m hm
  have hno := (hω.isOrdinal hZF).mem hnω
  obtain ⟨p, hp, _⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD hno
  have hpω := ZF.ordinalExponentiation_mem_omega hZF I hω
    (ds_two_mem_l hZF.1 hω ⟨o, ho, hd⟩) hnω hp
  refine ⟨n, p, hnω, hpω, hp, ?_⟩
  exact (ZF.ordinalExponentiation_exponent_eq_or_mem hZF I hD ho hd.predecessor_mem hno hp).elim
    (fun e => e ▸ hn.predecessor_mem)
    (fun h => ((hω.isOrdinal hZF).mem hpω).transitive n h m hn.predecessor_mem)

end YesMetaZFC.SetTheory.Descriptive
