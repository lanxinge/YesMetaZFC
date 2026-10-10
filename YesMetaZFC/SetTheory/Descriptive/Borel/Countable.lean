import YesMetaZFC.SetTheory.Descriptive.Borel.Operations

/-! # 可逐项调用的唯一补码与内部部分指标域 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bneg_d (ω c d : M.Domain) : Prop := ∃ z E H p,
  (∀ x, ¬ M.mem x z) ∧ (∀ x, M.mem x E ↔ x = z) ∧ I.Codes p z c ∧
  (∀ x, M.mem x H ↔ x = p) ∧ Bjoin_d I ω z H E d
def bneg_m {d} (ω c e : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (Formula.isEmpty (.bound 3)) (.conj (Formula.isSingleton (.bound 2) (.bound 3)) (.conj
    (𝒞.code .newest (.bound 3) c.weaken.weaken.weaken.weaken) (.conj
    (Formula.isSingleton (.bound 1) .newest)
    (bjoin_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 2) e.weaken.weaken.weaken.weaken))))))))
derive_free_closed bneg_m
theorem bneg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c e : Term d) :
    Formula.satisfies ρ (bneg_m (𝒞 := 𝒞) ω c e) ↔ Bneg_d I (ω.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [bneg_m, Bneg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSingleton_iff hE, I.satisfies_code_iff,
    bjoin_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bneg_unique_l (hE : Extensional M) {ω c d e} (h : Bneg_d I ω c d) (k : Bneg_d I ω c e) : d = e := by
  obtain ⟨z, E, H, p, hz, he, hp, hh, hd⟩ := h
  obtain ⟨z', E', H', p', hz', he', hp', hh', hk⟩ := k
  have e := hE.eq_of_same_members z' z (fun x => iff_of_false (hz' x) (hz x))
  subst z'
  have e := I.unique hp' hp
  subst p'
  have e := hE.eq_of_same_members E' E (fun x => (he' x).trans (he x).symm)
  subst E'
  have e := hE.eq_of_same_members H' H (fun x => (hh' x).trans (hh x).symm)
  subst H'
  exact bjoin_unique_l I hE hd hk

theorem bneg_exists_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) :
    ∃ d, Bneg_d I ω c d ∧ Bcode_d I ω A S d ∧ ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨E, he⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨p, hp⟩ := I.total z c
  obtain ⟨H, hh⟩ := KP.exists_singleton (ZF.modelsKP hZF) p
  have pair i d : M.PairMember I i d H ↔ i = z ∧ d = c :=
    ⟨fun ⟨q, hq, hqH⟩ => I.injective ((hh q).mp hqH ▸ hq) hp,
      fun ⟨rfl, rfl⟩ => ⟨p, hp, (hh p).mpr rfl⟩⟩
  have fam : Bfam_d I ω A S H := ⟨⟨fun q hq => ⟨z, c, ((hh q).mp hq).symm ▸ hp⟩,
    fun i d e hd he => ((pair i d).mp hd).2.trans ((pair i e).mp he).2.symm⟩,
    fun i d hd => ⟨((pair i d).mp hd).1.symm ▸ hzω, ((pair i d).mp hd).2.symm ▸ hc⟩⟩
  obtain ⟨d, hd, hc', hv⟩ := bjoin_exists_l I hZF hω hA hz hzω fam
    (E := E) (fun _ => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, fun j d h => ((pair j d).mp h).1⟩)
  refine ⟨d, ⟨z, E, H, p, hz, he, hp, hh, hd⟩, hc', fun x => ?_⟩
  have ex : (∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) ↔ Bsat_d I ω A S c x :=
    ⟨fun ⟨i, d, hd, hv⟩ => ((pair i d).mp hd).2 ▸ hv, fun h => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, h⟩⟩
  simpa only [ex, (he z).mpr rfl, true_and, not_true, false_and, or_false] using hv x

theorem family_domain_l (hZF : M.Models ZF) {ω H} (hH : ∀ i c, M.PairMember I i c H → M.mem i ω) :
    ∃ D, M.MemberSubset D ω ∧ M.IsDomainOf I D H := by
  let ρ : Env M 1 := ⟨fun _ => H, fun _ => H⟩
  let φ : UnarySchema 1 := { body := .existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
  have hp i : φ.denote ρ i ↔ ∃ c, M.PairMember I i c H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  exact ⟨D, fun i hi => ((hD i).mp hi).1, fun i => ((hD i).trans (and_congr_right fun _ => hp i)).trans
    ⟨And.right, fun ⟨c, hc⟩ => ⟨hH i c hc, c, hc⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive
