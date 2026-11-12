import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Card.Aleph.Recursion
import YesMetaZFC.SetTheory.Card.Properties.SuccessorRegularity
import YesMetaZFC.SetTheory.Notation

/-! # 良基关系的正则基数值下降秩

从超过给定高度与 ω 的基数 ζ 开始，按原秩取 ζ 起始的 Aleph 值，再取 Hartogs 后继。
所得实际图处处为正则基数，并严格保持原秩的不等式；全套条件都有一阶编码。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Rr_d (A R η F : M.Domain) : Prop where
  function : M.IsSetFunction I F
  domain : M.IsDomainOf I A F
  regular : ∀ a κ, Rd_entry_d a κ F → M.IsRegularCardinal I κ ∧ M.mem η κ
  decrease : ∀ a b κ ζ, Rd_entry_d a b R → Rd_entry_d a κ F → Rd_entry_d b ζ F → M.mem κ ζ

def rr_m {d} (A R η F : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜F⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜A⌝ₛ, ⌜F⌝ₛ) ∧
    (∀ a κ, ⌜rd_entry0_m⌝ₚ(a, κ, ⌜F⌝ₛ) → ⌜Formula.isRegularCardinal kpair_convention_l⌝ₚ(κ) ∧ ⌜η⌝ₛ ∈ κ) ∧
    (∀ a b κ ζ, ⌜rd_entry0_m⌝ₚ(a, b, ⌜R⌝ₛ) → ⌜rd_entry0_m⌝ₚ(a, κ, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(b, ζ, ⌜F⌝ₛ) → κ ∈ ζ)⟫
derive_free_closed rr_m

theorem rr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A R η F : Term d) :
    Formula.satisfies ρ (rr_m A R η F) ↔ Rr_d I (A.eval ρ) (R.eval ρ) (η.eval ρ) (F.eval ρ) := by
  simp only [rr_m, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_isRegularCardinal_iff I hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.function, h.domain, h.regular, h.decrease⟩⟩

private def rr_hartogs_m {d} (κ X : Term d) : Formula 1 d := set[d] ⟪
  Ord(⌜κ⌝ₛ) ∧ (∀ α, Ord(α) → (α ∈ ⌜κ⌝ₛ ↔ ∃ f, ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(f, α, ⌜X⌝ₛ)))⟫
derive_free_closed rr_hartogs_m

private theorem rr_hartogs_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X : Term d) :
    Formula.satisfies ρ (rr_hartogs_m κ X) ↔ M.IsHartogsNumber I (κ.eval ρ) (X.eval ρ) := by
  simp only [rr_hartogs_m, Structure.IsHartogsNumber, Structure.CardinalLessOrEqual, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinal_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isInjectionFromTo_iff I hE, Definitional.Term.eval_weaken]; rfl

theorem wr_regular_l (hZFC : M.Models ZFC) {ω A R η F : M.Domain} (hω : M.IsOmega ω)
    (ho : M.IsOrdinal η) (rank : Wr_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A R F) :
    ∃ H, Rr_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A R η H := by
  have hZF := ZFC.models_zf_l hZFC
  have hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have hwo := hω.isOrdinal (ZF.modelsKP hZF)
  obtain ⟨ζ, card, above, uncountable⟩ : ∃ ζ, M.IsCardinal I ζ ∧ M.mem η ζ ∧ M.mem ω ζ := by
    rcases ho.trichotomy hZF.1 hwo (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP η ω) with eq | hηω | hωη
    · obtain ⟨ζ, hc, hwζ⟩ := ZF.exists_cardinalAbove hZF I hwo
      exact ⟨ζ, hc, (hZF.1.eq_of_same_members η ω eq).symm ▸ hwζ, hwζ⟩
    · obtain ⟨ζ, hc, hwζ⟩ := ZF.exists_cardinalAbove hZF I hwo
      exact ⟨ζ, hc, hc.1.transitive ω hwζ η hηω, hwζ⟩
    · obtain ⟨ζ, hc, hηζ⟩ := ZF.exists_cardinalAbove hZF I ho
      exact ⟨ζ, hc, hηζ, hc.1.transitive η hηζ ω hωη⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ β ν,
    ⌜rd_entry0_m⌝ₚ(⌜(Term.bound 1 : Term 4)⌝ₛ, β, ⌜(Term.bound 2 : Term 4)⌝ₛ) ∧
    ⌜(Formula.isAlephNumber kpair_convention_l)⌝ₚ(⌜(Term.bound 3 : Term 4)⌝ₛ, β, ν) ∧
    ⌜rr_hartogs_m⌝ₚ(⌜(Term.newest : Term 4)⌝ₛ, ν)⟫ }
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => ζ), fun _ => ζ⟩
  have sat a κ : φ.denote ρ a κ ↔ ∃ β ν, Rd_entry_d a β F ∧ M.IsAlephNumber I ζ β ν ∧ M.IsHartogsNumber I κ ν := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_isAlephNumber_iff I hZF.1, rr_hartogs_sat_l I hZF.1,
      Definitional.Term.eval_weaken]; rfl
  have total a (ha : M.mem a A) : ∃ κ, φ.denote ρ a κ := by
    obtain ⟨β, hβ⟩ := (rank.2.1 a).mp ha
    obtain ⟨ν, hν, _⟩ := ZF.aleph_existsUnique hZF I ζ (rank.2.2 a β hβ).1
    obtain ⟨κ, hκ⟩ := ZF.exists_hartogsNumber hZF I ν
    exact ⟨κ, (sat a κ).mpr ⟨β, ν, hβ, hν, hκ⟩⟩
  have unique a κ μ (hk : φ.denote ρ a κ) (hm : φ.denote ρ a μ) : κ = μ := by
    obtain ⟨β, ν, hβ, hν, hk⟩ := (sat a κ).mp hk
    obtain ⟨γ, ξ, hγ, hξ, hm⟩ := (sat a μ).mp hm
    have eq := rank.1.2 a γ β hγ hβ
    subst γ
    obtain ⟨_, _, least⟩ := ZF.aleph_existsUnique hZF I ζ (rank.2.2 a β hβ).1
    have eq := (least ξ hξ).trans (least ν hν).symm
    subst ξ
    apply hZF.1.eq_of_same_members κ μ
    intro x
    exact ⟨fun hx => (hm.2 x (hk.1.mem hx)).mpr ((hk.2 x (hk.1.mem hx)).mp hx),
      fun hx => (hk.2 x (hm.1.mem hx)).mpr ((hm.2 x (hm.1.mem hx)).mp hx)⟩
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ A total unique
  obtain ⟨H, hf, hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun a _ => unique a)
    (fun a κ ha hκ => (hd κ).mpr ⟨a, ha, hκ⟩)
  have read a κ (hκ : Rd_entry_d a κ H) := (sat a κ).mp ((hs a κ).mp hκ).2
  have inf β ν (hβ : M.IsOrdinal β) (hν : M.IsAlephNumber I ζ β ν) : M.IsInfiniteCardinal I ω ν := by
    have hn := ZF.aleph_isInfiniteCardinal hZF I card hβ hν
    obtain ⟨e, he⟩ := ZF.exists_inclusionInjection hZF I (card.1.transitive.memberSubset uncountable)
    obtain ⟨f, hf⟩ := hn.2
    exact ⟨hn.1, ZF.exists_compositionInjection hZF I he hf⟩
  have below ν κ (hn : M.IsOrdinal ν) (hk : M.IsHartogsNumber I κ ν) : M.mem ν κ :=
    (hk.2 ν hn).mpr (ZF.exists_inclusionInjection hZF I (source := ν) (fun _ hx => hx))
  refine ⟨H, hf.1, hf.2.1, fun a κ hκ => ?_, fun a b κ μ hab ha hb => ?_⟩
  · obtain ⟨β, ν, hβ, hν, hk⟩ := read a κ hκ
    have hn := inf β ν (rank.2.2 a β hβ).1 hν
    have bζν := (ZF.aleph_isInfiniteCardinal hZF I card (rank.2.2 a β hβ).1 hν).2
    have νκ := below ν κ hn.1.1 hk
    have ζκ : M.mem ζ κ := by
      rcases card.eq_or_mem_of_cardinalLessOrEqual hZF I hn.1 bζν with eq | hζν
      · exact eq.symm ▸ νκ
      · exact hk.1.transitive ν νκ ζ hζν
    exact ⟨ZFC.hartogs_regular_l I hZFC hω hn hk, hk.1.transitive ζ ζκ η above⟩
  · obtain ⟨α, ν, hα, hν, hk⟩ := read a κ ha
    obtain ⟨β, ξ, hβ, hξ, hm⟩ := read b μ hb
    have αβ := ((rank.2.2 b β hβ).2 α).mpr ⟨a, α, (rank.2.1 a).mpr ⟨α, hα⟩, hab, hα, Or.inl rfl⟩
    have νξ := ZF.aleph_isIncreasingOnOrdinals hZF I card α β (rank.2.2 a α hα).1 (rank.2.2 b β hβ).1 αβ ν ξ hν hξ
    have cn := (inf α ν (rank.2.2 a α hα).1 hν).1
    have cx := (inf β ξ (rank.2.2 b β hβ).1 hξ).1
    have ξμ := below ξ μ cx.1 hm
    rcases hk.1.trichotomy hZF.1 cx.1 (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP κ ξ) with eq | hkξ | hξk
    · exact (hZF.1.eq_of_same_members κ ξ eq).symm ▸ ξμ
    · exact hm.1.transitive ξ ξμ κ hkξ
    · rcases cx.eq_or_mem_of_cardinalLessOrEqual hZF I cn ((hk.2 ξ cx.1).mp hξk) with eq | hξν
      · exact (KP.mem_irrefl_d hKP ξ (eq.symm ▸ νξ)).elim
      · exact (KP.mem_irrefl_d hKP ν (cn.1.transitive ξ hξν ν νξ)).elim

end YesMetaZFC.SetTheory
