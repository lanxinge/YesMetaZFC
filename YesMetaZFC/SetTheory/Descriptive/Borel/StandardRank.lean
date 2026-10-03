import YesMetaZFC.SetTheory.Descriptive.Borel.LevelBound
import YesMetaZFC.SetTheory.Descriptive.Borel.Rank

/-! # 集合的标准 Borel 秩

Bsr(K,α) 表示 α 是 K 所属 Σ⁰α 或 Π⁰α 的最小阶数，从一开始计数。
它只依赖集合 K；与具体码的根树秩 Bcr 分开。有码集合在 ZF 中有唯一可数秩。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Blev_d (ω S B α K : M.Domain) : Prop := Bsig_d I ω S B α K ∨ Bpi_d I ω S B α K
def blev_m {d} (ω S B α K : Term d) : Formula 1 d := .disj
  (bsig_m (𝒞 := 𝒞) ω S B α K) (bpi_m (𝒞 := 𝒞) ω S B α K)
derive_free_closed blev_m
theorem blev_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω S B α K : Term d) :
    Formula.satisfies ρ (blev_m (𝒞 := 𝒞) ω S B α K) ↔ Blev_d I (ω.eval ρ) (S.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [blev_m, Blev_d, Formula.satisfies_disj_iff, bsig_sat_l I hE, bpi_sat_l I hE]
theorem blev_ordinal_l {ω S B α K} (h : Blev_d I ω S B α K) : M.IsOrdinal α :=
  h.elim (bsig_ordinal_l I) (fun ⟨_, h, _⟩ => bsig_ordinal_l I h)
theorem blev_nonempty_l {ω S B α K} (h : Blev_d I ω S B α K) : ∃ β, M.mem β α :=
  h.elim (bsig_nonempty_l I) (fun ⟨_, h, _⟩ => bsig_nonempty_l I h)
theorem blev_subset_l {ω S B α K} (h : Blev_d I ω S B α K) : M.MemberSubset K B :=
  h.elim (bsig_subset_l I) (bpi_subset_l I)

def Bsr_d (ω S B K α : M.Domain) : Prop := Blev_d I ω S B α K ∧
  ∀ β, Blev_d I ω S B β K → M.MemberSubset α β
def bsr_m {d} (ω S B K α : Term d) : Formula 1 d := .conj (blev_m (𝒞 := 𝒞) ω S B α K)
  (.forallE (.imp (blev_m (𝒞 := 𝒞) ω.weaken S.weaken B.weaken .newest K.weaken) (Formula.subset α.weaken .newest)))
derive_free_closed bsr_m
theorem bsr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω S B K α : Term d) :
    Formula.satisfies ρ (bsr_m (𝒞 := 𝒞) ω S B K α) ↔ Bsr_d I (ω.eval ρ) (S.eval ρ) (B.eval ρ) (K.eval ρ) (α.eval ρ) := by
  simp only [bsr_m, Bsr_d, Formula.satisfies_conj_iff, blev_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl
theorem bsr_unique_l (hE : Extensional M) {ω S B K α β} (h : Bsr_d I ω S B K α) (k : Bsr_d I ω S B K β) : α = β :=
  hE.eq_of_same_members α β (fun x => ⟨h.2 β k.1 x, k.2 α h.1 x⟩)

/-- 最小化发生在内部序数的实际分离子集上，而非外部良序归纳。 -/
theorem bsr_min_l (hZF : M.Models ZF) {ω S B K β} (hb : Blev_d I ω S B β K) :
    ∃ α, Bsr_d I ω S B K α ∧ M.MemberSubset α β := by
  obtain ⟨δ, hd⟩ := KP.exists_successor (ZF.modelsKP hZF) β
  have hδ := KP.successor_isOrdinal (ZF.modelsKP hZF) (blev_ordinal_l I hb) hd
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push K
  let φ : UnarySchema 4 := { body := blev_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1) }
  obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ ρ δ
  have ec γ : M.mem γ C ↔ M.mem γ δ ∧ Blev_d I ω S B γ K :=
    (hc γ).trans (and_congr_right fun _ => blev_sat_l I hZF.1 _ _ _ _ _ _)
  obtain ⟨α, ha, least⟩ := hδ.wellOrder.least C (fun γ h => ((ec γ).mp h).1)
    ⟨β, (ec β).mpr ⟨hd.predecessor_mem, hb⟩⟩
  obtain ⟨haδ, level⟩ := (ec α).mp ha
  have low γ (hγ : Blev_d I ω S B γ K) : M.MemberSubset α γ := by
    have hα := blev_ordinal_l I level
    have hγo := blev_ordinal_l I hγ
    rcases Structure.IsOrdinal.trichotomy hZF.1 hα hγo (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α γ) with e | e | e
    · exact fun x hx => (e x).mp hx
    · exact hγo.transitive.memberSubset e
    · rcases least γ ((ec γ).mpr ⟨hδ.transitive α haδ γ e, hγ⟩) with he | he
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) γ (hZF.1.eq_of_same_members α γ he ▸ e)).elim
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) α (hα.transitive γ e α he)).elim
  exact ⟨α, ⟨level, low⟩, low β hb⟩

theorem bsr_exists_l (hZF : M.Models ZF) {ω X A S B K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I A ω) (hK : Borel_d I ω A S B K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω S B K α ∧
      ∀ β, Bsr_d I ω S B K β → β = α := by
  obtain ⟨c, ht, hd⟩ := hK
  obtain ⟨β, _, ⟨E, he⟩, hb, _⟩ := bcode_level_l I hZF hω hB hS hc ht hd
  obtain ⟨α, ha, sub⟩ := bsr_min_l I hZF (Or.inl hb)
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I sub
  exact ⟨α, blev_ordinal_l I ha.1, ZF.exists_compositionInjection hZF I hd he, ha, fun β h => bsr_unique_l I hZF.1 h ha⟩

theorem blev_compl_l (hE : Extensional M) {ω S B α K L} (sub : M.MemberSubset K B) (hc : Cm_d B K L) :
    Blev_d I ω S B α L ↔ Blev_d I ω S B α K :=
  (or_congr (bsig_compl_l I hE sub hc) (bpi_compl_l I hE sub hc)).trans or_comm
theorem bsr_compl_l (hE : Extensional M) {ω S B α K L} (sub : M.MemberSubset K B) (hc : Cm_d B K L) :
    Bsr_d I ω S B L α ↔ Bsr_d I ω S B K α := by
  exact and_congr (blev_compl_l I hE sub hc) (forall_congr' fun β => imp_congr_left (blev_compl_l I hE sub hc))

/-- 秩一表示开或闭；并不要求既开又闭。 -/
theorem bsr_one_l (hZF : M.Models ZF) {ω S B o K} (ho : M.IsOrdinalOne o) :
    Bsr_d I ω S B K o ↔ Open_d S B K ∨ Cl_d S B K := by
  constructor
  · exact fun h => (or_congr (bsig_one_l I hZF ho) (bpi_one_l I hZF ho)).mp h.1
  · intro h
    refine ⟨(or_congr (bsig_one_l I hZF ho) (bpi_one_l I hZF ho)).mpr h, fun β hb x hx => ?_⟩
    obtain ⟨z, hz, hs⟩ := ho
    rcases (hs x).mp hx with hx | hx
    · exact (hz x hx).elim
    · exact hZF.1.eq_of_same_members z x (fun y => (hx y).symm) ▸
        (blev_ordinal_l I hb).empty_mem_of_nonempty (ZF.modelsKP hZF) (blev_nonempty_l I hb) hz

end YesMetaZFC.SetTheory.Descriptive
