import YesMetaZFC.SetTheory.PartialFunction

/-! # 任意坐标集上有限部分函数的可数链条件

对内部有限图的大小界归纳。固定族中一个非空图 p，每个其他条件必在 p 的某个
坐标上取值；这些坐标与可数值集给出可数覆盖。每个覆盖片共享一个条目，删去它
以后大小界严格降低。全过程只使用模型内公式归纳，坐标集可为任意大小。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fn_antichain_d (A : M.Domain) : Prop :=
  ∀ p q, M.mem p A → M.mem q A → Agree_d I p q → p = q

def fn_antichain_m (𝒞 : OrderedPairConvention) {n} (A : Term n) : Formula 1 n :=
  Formula.forallMem A (Formula.forallMem A.weaken
    (.imp (agree_m 𝒞 (.bound 1) .newest) (Formula.extensionalEq (.bound 1) .newest)))
derive_free_closed fn_antichain_m

def Fn_bounded_d (X Y n A : M.Domain) : Prop :=
  (∀ p, M.mem p A → Pfn_d I X Y p ∧ M.CardinalLessOrEqual I p n) ∧ Fn_antichain_d I A

def fn_bounded_m (𝒞 : OrderedPairConvention) {n} (X Y k A : Term n) : Formula 1 n :=
  .conj (Formula.forallMem A (.conj (pfn_m 𝒞 X.weaken Y.weaken .newest)
    (Formula.cardinalLessOrEqual 𝒞 .newest k.weaken))) (fn_antichain_m 𝒞 A)
derive_free_closed fn_bounded_m

theorem fn_antichain_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A : Term n) :
    Formula.satisfies ρ (fn_antichain_m 𝒞 A) ↔ Fn_antichain_d I (A.eval ρ) := by
  simp only [fn_antichain_m, Fn_antichain_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, agree_sat_l I hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push]
  exact ⟨fun h p q hp hq => h p hp q hq, fun h p hp q hq => h p q hp hq⟩

theorem fn_bounded_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X Y k A : Term n) :
    Formula.satisfies ρ (fn_bounded_m 𝒞 X Y k A) ↔ Fn_bounded_d I (X.eval ρ) (Y.eval ρ) (k.eval ρ) (A.eval ρ) := by
  simp only [fn_bounded_m, Fn_bounded_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    pfn_sat_l I hE, Formula.satisfies_cardinalLessOrEqual_iff I hE, fn_antichain_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

namespace ZFC
variable (hZFC : M.Models ZFC) {ω X Y : M.Domain} (hω : M.IsOmega ω)
include hZFC hω

private theorem subsingleton_countable_l {A} (hA : ∀ p q, M.mem p A → M.mem q A → p = q) :
    M.CardinalLessOrEqual I A ω := by
  let hZF := models_zf_l hZFC
  obtain ⟨e, _, he⟩ := hω.1.1
  let ρ : Env M 1 := ⟨fun _ => e, fun _ => e⟩
  apply ZF.exists_setInjectionFromTo_of_denote hZF I BinarySchema.constantValue ρ
  · exact fun _ _ => ⟨e, (Formula.denote_constantValue_iff hZF.1 ρ _ _).mpr rfl⟩
  · exact fun x _ y z hy hz => ((Formula.denote_constantValue_iff hZF.1 ρ x y).mp hy).trans
      ((Formula.denote_constantValue_iff hZF.1 ρ x z).mp hz).symm
  · exact fun x y _ hy => (Formula.denote_constantValue_iff hZF.1 ρ x y).mp hy ▸ he
  · exact fun p q _ hp hq _ _ => hA p q hp hq

/-- 固定内部有限大小界的部分函数反链可数。 -/
theorem fn_bounded_countable_l (hY : M.CardinalLessOrEqual I Y ω) :
    ∀ n, M.mem n ω → ∀ A, Fn_bounded_d I X Y n A → M.CardinalLessOrEqual I A ω := by
  let hZF := models_zf_l hZFC
  let ρ : Env M 3 := ((⟨fun _ => X, fun _ => X⟩ : Env M 1).push Y).push ω
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (fn_bounded_m 𝒞 (.bound 4) (.bound 3) (.bound 1) .newest)
      (Formula.cardinalLessOrEqual 𝒞 .newest (.bound 2))) }
  have hφ n : φ.denote ρ n ↔ ∀ A, Fn_bounded_d I X Y n A → M.CardinalLessOrEqual I A ω := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fn_bounded_sat_l I hZF.1, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  apply hω.induction (fun n => ∀ A, Fn_bounded_d I X Y n A → M.CardinalLessOrEqual I A ω)
  · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro n hn A hA
    have he p (hp : M.mem p A) : ∀ x, ¬ M.mem x p := by
      obtain ⟨f, hf⟩ := (hA.1 p hp).2
      intro x hx
      obtain ⟨y, hy, _⟩ := hf.1.2.2 x hx
      exact hn y hy
    exact subsingleton_countable_l I hZFC hω (fun p q hp hq =>
      hZF.1.eq_of_same_members p q (fun x => iff_of_false (he p hp x) (he q hq x)))
  · intro n hn ih s hs A ⟨hA, hanti⟩
    classical
    by_cases hA0 : ∃ p, M.mem p A
    · obtain ⟨p, hp⟩ := hA0
      by_cases hp0 : ∃ c, M.mem c p
      · obtain ⟨s', hs', hsω⟩ := hω.1.2 n hn
        have hsω : M.mem s ω := (Structure.SuccessorOf.eq hZF.1 hs hs').symm ▸ hsω
        have hpω := ZF.finite_countable_l I hZF hω ⟨s, hsω, (hA p hp).2⟩
        obtain ⟨J, hJ⟩ := ZF.exists_cartesianProduct hZF I p Y
        have hj := ZF.countable_product_l I hZF hω hpω hY hJ
        let ψ : BinarySchema 0 := {
          body := .existsE (.existsE (.existsE (.existsE (.conj
            (𝒞.code (.bound 5) (.bound 3) (.bound 2)) (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
              (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 2) (.bound 4))))))) }
        let δ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
        have hψ j q : ψ.denote δ j q ↔ ∃ c v x w, I.Codes j c v ∧ I.Codes c x w ∧ M.PairMember I x v q := by
          simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
            I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]
          rfl
        apply countable_cover_l I hZFC hω ψ δ hj
        · intro j hj D hD
          obtain ⟨c, hcp, v, _, hj⟩ := (hJ j).mp hj
          obtain ⟨x, w, hc⟩ := (hA p hp).1.1.1 c hcp
          have hd q : M.mem q D ↔ M.mem q A ∧ M.PairMember I x v q := by
            rw [hD q]
            apply and_congr_right
            intro _
            rw [hψ j q]
            constructor
            · rintro ⟨c', v', x', w', hj', hc', hq⟩
              obtain ⟨rfl, rfl⟩ := I.injective hj hj'
              obtain ⟨rfl, rfl⟩ := I.injective hc hc'
              exact hq
            · exact fun h => ⟨c, v, x, w, hj, hc, h⟩
          obtain ⟨a, ha⟩ := I.total x v
          have had q (hq : M.mem q D) : M.mem a q := by
            obtain ⟨b, hb, hbq⟩ := ((hd q).mp hq).2
            exact I.unique hb ha ▸ hbq
          obtain ⟨E, hE, g, hg⟩ := ZF.erase_family_l I hZF had
          have heq {q r t} (hr : ∀ i, M.mem i r ↔ M.mem i q ∧ i ≠ a)
              (ht : ∀ i, M.mem i t ↔ M.mem i q ∧ i ≠ a) : r = t :=
            hZF.1.eq_of_same_members r t (fun i => (hr i).trans (ht i).symm)
          have hEb : Fn_bounded_d I X Y n E := by
            constructor
            · intro r hr
              obtain ⟨q, hq, hqr⟩ := (hE r).mp hr
              have hqA := hA q ((hd q).mp hq).1
              exact ⟨pfn_subset_l I hqA.1 (fun i hi => ((hqr i).mp hi).1),
                ZF.delete_bound_l I hZF hs hqA.2 (had q hq) hqr⟩
            · intro r t hr ht hrt
              obtain ⟨q, hq, hqr⟩ := (hE r).mp hr
              obtain ⟨q', hq', hqt⟩ := (hE t).mp ht
              have hqq := hanti q q' ((hd q).mp hq).1 ((hd q').mp hq').1
                (agree_restore_l I ha (hA q ((hd q).mp hq).1).1.1 (hA q' ((hd q').mp hq').1).1.1
                  (had q hq) (had q' hq') hqr hqt hrt)
              subst q'
              exact heq hqr hqt
          obtain ⟨f, hf⟩ := ih E hEb
          exact ZF.exists_compositionInjection hZF I hg hf
        · intro q hq
          have hit : ∃ c v x w, M.mem c p ∧ M.mem v Y ∧ I.Codes c x w ∧ M.PairMember I x v q := by
            by_cases hqp : q = p
            · subst q
              obtain ⟨c, hc⟩ := hp0
              obtain ⟨x, v, hcv⟩ := (hA p hp).1.1.1 c hc
              exact ⟨c, v, x, v, hc, ((hA p hp).1.2 x v ⟨c, hcv, hc⟩).2, hcv, c, hcv, hc⟩
            · apply Classical.byContradiction
              intro hnone
              apply hqp
              apply Eq.symm
              apply hanti p q hp hq
              intro x y v hpx hqv
              obtain ⟨c, hc, hcp⟩ := hpx
              exact False.elim (hnone ⟨c, v, x, y, hcp, ((hA q hq).1.2 x v hqv).2, hc, hqv⟩)
          obtain ⟨c, v, x, w, hc, hv, hcx, hxv⟩ := hit
          obtain ⟨j, hj⟩ := I.total c v
          exact ⟨j, (hJ j).mpr ⟨c, hc, v, hv, hj⟩, (hψ j q).mpr ⟨c, v, x, w, hj, hcx, hxv⟩⟩
      · have he q (hq : M.mem q A) : p = q := hanti p q hp hq
          (fun _ _ _ h => False.elim (h.elim fun c hc => hp0 ⟨c, hc.2⟩))
        exact subsingleton_countable_l I hZFC hω (fun q r hq hr => (he q hq).symm.trans (he r hr))
    · exact subsingleton_countable_l I hZFC hω (fun p _ hp _ => False.elim (hA0 ⟨p, hp⟩))

/-- 任意坐标集、可数值集的有限部分函数满足模型内部可数链条件。 -/
theorem fn_ccc_l (hY : M.CardinalLessOrEqual I Y ω) {A}
    (hA : ∀ p, M.mem p A → Fn_d I ω X Y p) (ha : Fn_antichain_d I A) : M.CardinalLessOrEqual I A ω := by
  let hZF := models_zf_l hZFC
  let φ : BinarySchema 0 := { body := Formula.cardinalLessOrEqual 𝒞 .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
  have hφ n p : φ.denote ρ n p ↔ M.CardinalLessOrEqual I p n :=
    Formula.satisfies_cardinalLessOrEqual_iff I hZF.1 ((ρ.push n).push p) .newest (.bound 1)
  obtain ⟨f, hf⟩ := ZF.exists_identityBijection hZF I ω
  apply countable_cover_l I hZFC hω φ ρ ⟨f, hf.1⟩
  · intro n hn D hD
    apply fn_bounded_countable_l I hZFC hω hY n hn D
    refine ⟨fun p hp => ⟨(hA p ((hD p).mp hp).1).1, (hφ n p).mp ((hD p).mp hp).2⟩,
      fun p q hp hq => ha p q ((hD p).mp hp).1 ((hD q).mp hq).1⟩
  · intro p hp
    obtain ⟨n, hn, hpn⟩ := (hA p hp).2
    exact ⟨n, hn, (hφ n p).mpr hpn⟩

end ZFC
end YesMetaZFC.SetTheory
