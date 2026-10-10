import YesMetaZFC.SetTheory.Descriptive.Borel.Basic
import YesMetaZFC.SetTheory.Descriptive.Borel.Operations

/-! # 开集与闭树体的 Borel 码

固定一个已有的内部前缀编号，把柱集包含于开集的前缀送到其唯一规范基本码，
形成实际部分可数码族，再调用可数并。整个过程在 ZF 内完成，不需要可数选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bcover_d (B U s : M.Domain) : Prop := ∀ x, M.mem x B → M.MemberSubset s x → M.mem x U
def bcover_m {d} (B U s : Term d) : Formula 1 d := Formula.forallMem B
  (.imp (Formula.subset s.weaken .newest) (.mem .newest U.weaken))
derive_free_closed bcover_m
theorem bcover_sat_l {d} (ρ : Env M d) (B U s : Term d) :
    Formula.satisfies ρ (bcover_m B U s) ↔ Bcover_d (M := M) (B.eval ρ) (U.eval ρ) (s.eval ρ) := by
  simp only [bcover_m, Bcover_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

/-- 有内部可数基的前缀空间，其每个内部开集都有 Borel 码。 -/
theorem bcode_open_l (hZF : M.Models ZF) {ω A S B U} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.CardinalLessOrEqual I S ω) (ho : Open_d S B U) :
    ∃ c, Bcode_d I ω A S c ∧ Bden_d I ω A S B c U := by
  obtain ⟨J, hJ⟩ := hs
  let η : Env M 0 := ⟨Fin.elim0, fun _ => S⟩
  let φ : BinarySchema 0 := { body := bbasic_m (𝒞 := 𝒞) (.bound 1) .newest }
  have hp s c : φ.denote η s c ↔ Bbasic_d I s c := bbasic_sat_l I hZF.1 _ _ _
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ η S
    (fun s _ => (bbasic_exists_l I (ZF.modelsKP hZF) s).imp fun c h => (hp s c).mpr h)
    (fun s _ c d hc hd => bbasic_unique_l I hZF.1 ((hp s c).mp hc) ((hp s d).mp hd))
  let ρ : Env M 4 := (((⟨fun _ => S, fun _ => S⟩ : Env M 1).push J).push B).push U
  let ψ : BinarySchema 4 := {
    body := Formula.existsMem (.bound 5) (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 5))
      (.conj (bcover_m (.bound 4) (.bound 3) .newest) (bbasic_m (𝒞 := 𝒞) .newest (.bound 1)))) }
  have hψ i c : ψ.denote ρ i c ↔ ∃ s, M.mem s S ∧ M.PairMember I s i J ∧ Bcover_d B U s ∧ Bbasic_d I s c := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bcover_sat_l, bbasic_sat_l I hZF.1]; rfl
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω C
  obtain ⟨H, hH, he⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ W
  have pair i c : M.PairMember I i c H ↔ ∃ s, M.mem s S ∧ M.PairMember I s i J ∧ Bcover_d B U s ∧ Bbasic_d I s c := by
    refine ((he i c).trans (and_congr_right fun _ => and_congr_right fun _ => hψ i c)).trans
      ⟨fun h => h.2.2, fun h => ?_⟩
    obtain ⟨s, hs, hi, hu, hc⟩ := h
    exact ⟨(hW i).mpr (Or.inl (hJ.1.output_mem_of_pairMember hi)),
      (hW c).mpr (Or.inr ((hC c).mpr ⟨s, hs, (hp s c).mpr hc⟩)), s, hs, hi, hu, hc⟩
  have family : Bfam_d I ω A S H := by
    refine ⟨⟨hH.1, ?_⟩, ?_⟩
    · intro i c d hc hd
      obtain ⟨s, _, hi, _, hc⟩ := (pair i c).mp hc
      obtain ⟨t, _, hj, _, hd⟩ := (pair i d).mp hd
      have e := hJ.2 s t i hi hj
      exact bbasic_unique_l I hZF.1 hc (e.symm ▸ hd)
    · intro i c hc
      obtain ⟨s, hs, hi, _, hc⟩ := (pair i c).mp hc
      exact ⟨hJ.1.output_mem_of_pairMember hi, (bbasic_correct_l I hZF hω hA hs hc).1⟩
  obtain ⟨c, hc, hv⟩ := bcode_union_l I hZF hω hA family
  refine ⟨c, hc, fun x => ⟨fun hx => ⟨ho.1 x hx, ?_⟩, ?_⟩⟩
  · obtain ⟨s, hs, hsx, hu⟩ := ho.2 x hx
    obtain ⟨d, hd⟩ := bbasic_exists_l I (ZF.modelsKP hZF) s
    obtain ⟨i, _, hi⟩ := hJ.1.2.2 s hs
    exact (hv x).mpr ⟨i, d, (pair i d).mpr ⟨s, hs, hi, hu, hd⟩,
      ((bbasic_correct_l I hZF hω hA hs hd).2 x).mpr hsx⟩
  · rintro ⟨hxB, hx⟩
    obtain ⟨i, d, hi, hx⟩ := (hv x).mp hx
    obtain ⟨s, hs, _, hu, hd⟩ := (pair i d).mp hi
    exact hu x hxB (((bbasic_correct_l I hZF hω hA hs hd).2 x).mp hx)

def Borel_d (ω A S B K : M.Domain) : Prop := ∃ c, Bcode_d I ω A S c ∧ Bden_d I ω A S B c K
def borel_m {d} (ω A S B K : Term d) : Formula 1 d := .existsE (.conj
  (bcode_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken .newest)
  (bden_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken B.weaken .newest K.weaken))
derive_free_closed borel_m

theorem borel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S B K : Term d) :
    Formula.satisfies ρ (borel_m (𝒞 := 𝒞) ω A S B K) ↔
      Borel_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (B.eval ρ) (K.eval ρ) := by
  simp only [borel_m, Borel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bcode_sat_l I hE, bden_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 取补直接作用于码，返回实际相对补集。 -/
theorem borel_compl_l (hZF : M.Models ZF) {ω A S B K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hK : Borel_d I ω A S B K) :
    ∃ L, (∀ x, M.mem x L ↔ M.mem x B ∧ ¬ M.mem x K) ∧ Borel_d I ω A S B L := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨d, hd, hv⟩ := bcode_compl_l I hZF hω hA hc
  obtain ⟨L, hL⟩ := KP.difference_exists_d (ZF.modelsKP hZF) K B
  refine ⟨L, hL, d, hd, fun x => (hL x).trans (and_congr_right fun hx => ?_)⟩
  exact (not_congr ((hK x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).trans (hv x).symm

theorem tree_body_borel_l (hZF : M.Models ZF) {ω A S B T K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.CardinalLessOrEqual I S ω) (hK : Body_d S B T K) :
    Borel_d I ω A S B K := by
  classical
  obtain ⟨U, hU, ho⟩ := tree_body_closed_l (M := M) (ZF.modelsKP hZF) hK
  obtain ⟨c, hc, hv⟩ := bcode_open_l I hZF hω hA hs ho
  obtain ⟨d, hd, he⟩ := bcode_compl_l I hZF hω hA hc
  refine ⟨d, hd, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    refine ⟨((hK x).mp hx).1, (he x).mpr (fun hn => ?_)⟩
    exact ((hU x).mp ((hv x).mpr ⟨((hK x).mp hx).1, hn⟩)).2 hx
  · rintro ⟨hxB, hx⟩
    apply Classical.byContradiction
    intro hn
    exact (he x).mp hx (((hv x).mp ((hU x).mpr ⟨hxB, hn⟩)).2)

end YesMetaZFC.SetTheory.Descriptive
