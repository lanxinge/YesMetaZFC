import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Card.CountablePair

/-! # 可数良基关系的双层秩界

把每个节点 a 分为 a₀ < a₁，原边 b < a 改为 b₁ < a₀。
因此得到实际序数标号 ℓ(a) < h(a)，且 h(b) < ℓ(a)；两步间隙用于交替运算。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem wr_gap_l (hZF : M.Models ZF) {ω T R} (hω : M.IsOmega ω)
    (hw : Wf_rel_d T R) (hc : M.CardinalLessOrEqual I T ω) :
    ∃ κ L H, M.IsOrdinal κ ∧ M.CardinalLessOrEqual I κ ω ∧
      M.IsSetFunctionFromTo I L T κ ∧ M.IsSetFunctionFromTo I H T κ ∧
      ∀ a α β, M.PairMember I a α L → M.PairMember I a β H →
        M.mem α β ∧ ∀ b γ, M.mem b T → Rd_entry_d b a R → M.PairMember I b γ H → M.mem γ α := by
  classical
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  have ne : z ≠ o := fun e => hz z (e ▸ ho.predecessor_mem)
  obtain ⟨D, hd⟩ := KP.exists_pair (ZF.modelsKP hZF) z o
  have tags i : M.mem i D ↔ i = z ∨ i = o := hd i
  obtain ⟨E, he⟩ := ZF.exists_inclusionInjection hZF I (fun i hi => ((tags i).mp hi).elim (fun e => e ▸ hzω) (fun e => e ▸ hoω))
  obtain ⟨X, hx⟩ := ZF.exists_cartesianProduct hZF I T D
  have count := ZF.countable_product_l I hZF hω hc ⟨E, he⟩ hx
  let ρ : Env M 3 := ((⟨fun _ => R, fun _ => R⟩ : Env M 1).push z).push o
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.existsE (.existsE (.conj
    (𝒞.code (.bound 5) (.bound 3) (.bound 1)) (.conj (𝒞.code (.bound 4) (.bound 2) .newest)
    (.disj (.conj (Formula.extensionalEq (.bound 1) (.bound 6)) (.conj
      (Formula.extensionalEq .newest (.bound 7)) (rd_entry_m (.bound 3) (.bound 2) (.bound 8))))
    (.conj (Formula.extensionalEq (.bound 3) (.bound 2)) (.conj
      (Formula.extensionalEq (.bound 1) (.bound 7)) (Formula.extensionalEq .newest (.bound 6)))))))))) }
  have hp p q : φ.denote ρ p q ↔ ∃ a b i j, I.Codes p a i ∧ I.Codes q b j ∧
      ((i = o ∧ j = z ∧ Rd_entry_d a b R) ∨ (a = b ∧ i = z ∧ j = o)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨Q, _, eqn⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ X
  have edge {p q a b i j} (pp : I.Codes p a i) (qq : I.Codes q b j) :
      Rd_entry_d p q Q ↔ M.mem p X ∧ M.mem q X ∧
        ((i = o ∧ j = z ∧ Rd_entry_d a b R) ∨ (a = b ∧ i = z ∧ j = o)) := by
    refine (eqn p q).trans (and_congr_right fun _ => and_congr_right fun _ => (hp p q).trans ⟨?_, ?_⟩)
    · rintro ⟨a', b', i', j', pp', qq', h⟩
      obtain ⟨rfl, rfl⟩ := I.injective pp' pp
      obtain ⟨rfl, rfl⟩ := I.injective qq' qq
      exact h
    · exact fun h => ⟨a, b, i, j, pp, qq, h⟩
  have node {a i p} (ha : M.mem a T) (hi : M.mem i D) (pp : I.Codes p a i) : M.mem p X :=
    (hx p).mpr ⟨a, ha, i, hi, pp⟩
  have wf : Wf_rel_d X Q := by
    intro Y sub hn
    let ψ : UnarySchema 1 := { body := .existsE (.existsE (.conj
      (𝒞.code .newest (.bound 2) (.bound 1)) (.mem .newest (.bound 3)))) }
    let η : Env M 1 := ⟨fun _ => Y, fun _ => Y⟩
    obtain ⟨C, hc'⟩ := ZF.separation_exists_d hZF ψ η T
    have ec a : M.mem a C ↔ M.mem a T ∧ ∃ i p, I.Codes p a i ∧ M.mem p Y := by
      simpa only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff,
        Formula.satisfies_conj_iff, I.satisfies_code_iff, Formula.satisfies_mem_iff] using! hc' a
    obtain ⟨p, hpY⟩ := hn
    obtain ⟨a, ha, i, _, pp⟩ := (hx p).mp (sub p hpY)
    obtain ⟨a, haC, least⟩ := hw C (fun a h => ((ec a).mp h).1) ⟨a, (ec a).mpr ⟨ha, i, p, pp, hpY⟩⟩
    obtain ⟨ha, i, p, pp, hpY⟩ := (ec a).mp haC
    obtain ⟨p₀, pz⟩ := I.total a z
    by_cases h₀ : M.mem p₀ Y
    · refine ⟨p₀, h₀, fun q hq e => ?_⟩
      obtain ⟨b, hb, j, _, qq⟩ := (hx q).mp (sub q hq)
      rcases ((edge qq pz).mp e).2.2 with ⟨_, _, hba⟩ | ⟨_, _, hzo⟩
      · exact least b ((ec b).mpr ⟨hb, j, q, qq, hq⟩) hba
      · exact ne hzo
    · refine ⟨p, hpY, fun q hq e => ?_⟩
      obtain ⟨b, hb, j, _, qq⟩ := (hx q).mp (sub q hq)
      rcases ((edge qq pp).mp e).2.2 with ⟨_, hi, _⟩ | ⟨hba, hj, _⟩
      · exact h₀ (I.unique (hi ▸ pp) pz ▸ hpY)
      · exact h₀ (I.unique (hba ▸ hj ▸ qq) pz ▸ hq)
  obtain ⟨κ, F, hk, hkω, hf, hr⟩ := wr_countable_l I hZF hω wf count
  have below {p q α β} (hp : M.mem p X) (he : Rd_entry_d p q Q)
      (hpa : M.PairMember I p α F) (hqb : M.PairMember I q β F) : M.mem α β :=
    ((hr.2.2 q β hqb).2 α).mpr ⟨p, α, hp, he, hpa, Or.inl rfl⟩
  have select i (hi : M.mem i D) : ∃ H, M.IsSetFunctionFromTo I H T κ ∧
      ∀ a α, M.PairMember I a α H ↔ M.mem a T ∧ ∃ p, I.Codes p a i ∧ M.PairMember I p α F := by
    let η : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push i
    let ψ : BinarySchema 2 := { body := .existsE (.conj (𝒞.code .newest (.bound 2) (.bound 3))
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4))) }
    have ep a α : ψ.denote η a α ↔ ∃ p, I.Codes p a i ∧ M.PairMember I p α F := by
      simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
    obtain ⟨H, hh, eh⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := T) (target := κ) (by
      intro a ha
      obtain ⟨p, pp⟩ := I.total a i
      obtain ⟨α, _, hpa⟩ := hf.2.2 p (node ha hi pp)
      exact ⟨α, (ep a α).mpr ⟨p, pp, hpa⟩⟩) (by
      intro a _ α β ha hb
      obtain ⟨p, pp, hpa⟩ := (ep a α).mp ha
      obtain ⟨q, qq, hqb⟩ := (ep a β).mp hb
      exact hf.1.2 p α β hpa (I.unique qq pp ▸ hqb))
      (fun a α _ h => (ep a α).mp h |>.elim fun _ h => hf.output_mem_of_pairMember h.2)
    exact ⟨H, hh, fun a α => (eh a α).trans (and_congr_right fun _ => ep a α)⟩
  obtain ⟨L, hl, el⟩ := select z ((tags z).mpr (Or.inl rfl))
  obtain ⟨H, hh, eh⟩ := select o ((tags o).mpr (Or.inr rfl))
  refine ⟨κ, L, H, hk, hkω, hl, hh, fun a α β ha hb => ?_⟩
  obtain ⟨_, p, pp, hpa⟩ := (el a α).mp ha
  obtain ⟨_, q, qq, hqb⟩ := (eh a β).mp hb
  have px := hf.input_mem_of_pairMember hpa
  have qx := hf.input_mem_of_pairMember hqb
  refine ⟨below px ((edge pp qq).mpr ⟨px, qx, Or.inr ⟨rfl, rfl, rfl⟩⟩) hpa hqb, ?_⟩
  intro b γ _ hba hc
  obtain ⟨_, r, rr, hrg⟩ := (eh b γ).mp hc
  have rx := hf.input_mem_of_pairMember hrg
  exact below rx ((edge rr pp).mpr ⟨rx, px, Or.inl ⟨rfl, rfl, hba⟩⟩) hrg hpa

end YesMetaZFC.SetTheory
