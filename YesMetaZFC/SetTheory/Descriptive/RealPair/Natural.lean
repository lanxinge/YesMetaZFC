import YesMetaZFC.SetTheory.Descriptive.Borel
import YesMetaZFC.SetTheory.Card.CountablePair

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
