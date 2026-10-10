import YesMetaZFC.Model.SetTheory.Internal.TruthSyntax

/-! # 内部真值递归的存在、唯一性与原公式

一步算子在赋值空间上作实际分离，原序数递归给出整张真值表。递归先对任意
内部序数长度成立，有限公式码只需取长度属于 ω；没有外部良基性或真值表假设。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem seval_step_exists_l (hZF : M.Models ZF) (X R E F H : M.Domain) :
    ∃ Y, Seval_step_d I X R E F H Y := by
  let ρ := (seval_env_l X R E F).push H
  let φ : UnarySchema 5 := {
    body := seval_at_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 2) (.bound 1) .newest }
  obtain ⟨Y, hY⟩ := ZF.separation_exists_d hZF φ ρ E
  exact ⟨Y, fun f => (hY f).trans (and_congr_right fun _ => seval_at_sat_l I hZF.1 (ρ.push f) _ _ _ _ _)⟩

theorem seval_step_unique_l (hE : Extensional M) {X R E F H Y Z}
    (h : Seval_step_d I X R E F H Y) (k : Seval_step_d I X R E F H Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun f => (h f).trans (k f).symm)

theorem seval_class_l (hZF : M.Models ZF) (X R E F : M.Domain) :
    M.IsClassFunctionOnTransfiniteSequences I (Seval_step_d I X R E F) := by
  intro H _
  obtain ⟨Y, hY⟩ := seval_step_exists_l I hZF X R E F H
  exact ⟨Y, hY, fun Z hZ => seval_step_unique_l I hZF.1 hZ hY⟩

/-- 每个内部序数长度的真值表实际存在；算子的全定义性已由分离证明。 -/
theorem seval_exists_l (hZF : M.Models ZF) (X R E F : M.Domain) {n} (hn : M.IsOrdinal n) :
    ∃ H, Seval_d I X R E F n H := by
  have ho : (seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F) = Seval_step_d I X R E F :=
    seval_op_l I hZF.1 (seval_env_l X R E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences I
      ((seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F)) := by
    rw [ho]
    exact seval_class_l I hZF X R E F
  obtain ⟨H, hH⟩ := ZF.recursiveSequence_exists hZF I (seval_env_l X R E F) (seval_s (𝒞 := 𝒞)) hc hn
  exact ⟨H, by simpa only [ho, Seval_d] using hH⟩

theorem seval_unique_l (hZF : M.Models ZF) {X R E F n H J}
    (hH : Seval_d I X R E F n H) (hJ : Seval_d I X R E F n J) : H = J := by
  have ho : (seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F) = Seval_step_d I X R E F :=
    seval_op_l I hZF.1 (seval_env_l X R E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences I
      ((seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F)) := by
    rw [ho]
    exact seval_class_l I hZF X R E F
  exact ZF.recursiveSequence_unique hZF I (seval_env_l X R E F) (seval_s (𝒞 := 𝒞)) hc
    (by simpa only [ho, Seval_d] using hH) (by simpa only [ho, Seval_d] using hJ)

def Ssat_d (X R E F n k f : M.Domain) : Prop :=
  ∃ H Y, Seval_d I X R E F n H ∧ M.PairMember I k Y H ∧ M.mem f Y

def ssat_m {n} (X R E F l k f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (seval_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken E.weaken.weaken
    F.weaken.weaken l.weaken.weaken (.bound 1))
    (.conj (Formula.orderedPairMem 𝒞 k.weaken.weaken .newest (.bound 1)) (.mem f.weaken.weaken .newest))))
derive_free_closed ssat_m

theorem ssat_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F l k f : Term n) :
    Formula.satisfies ρ (ssat_m (𝒞 := 𝒞) X R E F l k f) ↔
      Ssat_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (l.eval ρ) (k.eval ρ) (f.eval ρ) := by
  simp only [ssat_m, Ssat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    seval_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 存在量化的满足关系精确等于唯一真值表中的实际成员性。 -/
theorem ssat_value_l (hZF : M.Models ZF) {X R E F n H k Y}
    (hH : Seval_d I X R E F n H) (hY : M.PairMember I k Y H) (f : M.Domain) :
    Ssat_d I X R E F n k f ↔ M.mem f Y := by
  constructor
  · rintro ⟨J, Z, hJ, hZ, hf⟩
    have he := seval_unique_l I hZF hJ hH
    subst J
    exact (hH.1.2.1.2 k Z Y hZ hY) ▸ hf
  · exact fun hf => ⟨H, Y, hH, hY, hf⟩

/-- 直接解码任意一行，所得递归语义使用精确的先前真值表。 -/
theorem seval_unfold_l (hE : Extensional M) {X R E F n H k c Y}
    (hF : M.IsSetFunction I F) (hH : Seval_d I X R E F n H)
    (hc : M.PairMember I k c F) (hY : M.PairMember I k Y H) : ∃ P,
    M.IsRestrictionOf I P H k ∧ M.IsDomainOf I k P ∧
      ∀ f, M.mem f Y ↔ M.mem f E ∧ Snode_d I X R P c f := by
  have hk := (hH.1.2.2 k).mpr ⟨Y, hY⟩
  obtain ⟨P, hP, hStep⟩ := hH.2 k hk Y hY
  have hd := (hH.restriction hk hP).1.2.2
  refine ⟨P, hP, hd, fun f => (hStep f).trans (and_congr_right fun _ => ?_)⟩
  constructor
  · rintro ⟨l, d, hl, hld, h⟩
    have he := hl.eq hE hd
    subst l
    have he := hF.2 k d c hld hc
    subst d
    exact h
  · exact fun h => ⟨k, c, hd, hc, h⟩

end YesMetaZFC.SetTheory.Internal
