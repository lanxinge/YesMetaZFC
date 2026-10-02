import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 内部有限参数列的拼接与投影

用内部序数加法移动第二段，故包含非标准有限长度。前段由限制恢复，尾段由
平移图恢复；这为两个有限参数包提供共同参数包。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fs_tail_d (n m F g : M.Domain) : Prop := M.IsSetRelation I g ∧ ∀ j x,
  M.PairMember I j x g ↔ M.mem j m ∧ ∃ i, M.IsOrdinalAddition I i n j ∧ M.PairMember I i x F

def fs_tail_m {d} (n m F g : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 g)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
    (.conj (.mem (.bound 1) m.weaken.weaken) (.existsE (.conj
      (Formula.isOrdinalAddition 𝒞 .newest n.weaken.weaken.weaken (.bound 2))
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) F.weaken.weaken.weaken)))))))
derive_free_closed fs_tail_m

theorem fs_tail_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n m F g : Term d) :
    Formula.satisfies ρ (fs_tail_m (𝒞 := 𝒞) n m F g) ↔
      Fs_tail_d I (n.eval ρ) (m.eval ρ) (F.eval ρ) (g.eval ρ) := by
  simp only [fs_tail_m, Fs_tail_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_isOrdinalAddition_iff I hE,
    Definitional.Term.eval_weaken]
  rfl

theorem fs_tail_unique_l (hE : Extensional M) {n m F g h} (hg : Fs_tail_d I n m F g)
    (hh : Fs_tail_d I n m F h) : g = h :=
  hg.1.eq_of_pairMember_iff hE hh.1 (fun j x => (hg.2 j x).trans (hh.2 j x).symm)

theorem ZF.fseq_join_l (hZF : M.Models ZF) {ω A n m f g} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hf : M.IsSetFunctionFromTo I f n A)
    (hg : M.IsSetFunctionFromTo I g m A) : ∃ k F, M.mem k ω ∧ M.IsSetFunctionFromTo I F k A ∧
      M.IsRestrictionOf I f F n ∧ Fs_tail_d I n m F g := by
  have no := hω.members_areOrdinals hZF n hn
  have mo := hω.members_areOrdinals hZF m hm
  obtain ⟨k, hk, _⟩ := ordinalAddition_existsUnique hZF I n mo
  let ρ : Env M 4 := ⟨Fin.cases n (Fin.cases m (Fin.cases f (fun _ => g))), fun _ => A⟩
  let φ : BinarySchema 4 := {
    body := .disj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.existsE
      (.conj (.mem .newest (.bound 4)) (.conj (Formula.isOrdinalAddition 𝒞 (.bound 2) (.bound 3) .newest)
        (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 6))))) }
  have sat i x : φ.denote ρ i x ↔ M.PairMember I i x f ∨
      ∃ j, M.mem j m ∧ M.IsOrdinalAddition I i n j ∧ M.PairMember I j x g := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_isOrdinalAddition_iff I hZF.1]
    rfl
  have disjoint i j (hi : M.mem i n) (hj : M.mem j m) (h : M.IsOrdinalAddition I i n j) : False :=
    KP.mem_irrefl_d (modelsKP hZF) i (ordinalAddition_left_member_mem_value hZF I no (mo.mem hj) hi h)
  obtain ⟨F, hF, he⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := A) (by
    intro i hi
    rcases (ordinalAddition_mem_iff hZF I mo hk).mp hi with hi | ⟨j, hj, ha⟩
    · obtain ⟨x, _, hx⟩ := hf.2.2 i hi
      exact ⟨x, (sat i x).mpr (Or.inl hx)⟩
    · obtain ⟨x, _, hx⟩ := hg.2.2 j hj
      exact ⟨x, (sat i x).mpr (Or.inr ⟨j, hj, ha, hx⟩)⟩) (by
    intro i _ x y hx hy
    rcases (sat i x).mp hx with hx | ⟨j, hj, ha, hx⟩ <;>
      rcases (sat i y).mp hy with hy | ⟨l, hl, hb, hy⟩
    · exact hf.1.2 i x y hx hy
    · exact (disjoint i l (hf.input_mem_of_pairMember hx) hl hb).elim
    · exact (disjoint i j (hf.input_mem_of_pairMember hy) hj ha).elim
    · have eq := ordinalAddition_right_injective hZF I no (mo.mem hj) (mo.mem hl) ha hb; subst l
      exact hg.1.2 j x y hx hy) (by
    intro i x _ hx
    exact ((sat i x).mp hx).elim hf.output_mem_of_pairMember
      (fun ⟨_, _, _, hx⟩ => hg.output_mem_of_pairMember hx))
  have graph i x : M.PairMember I i x F ↔ M.PairMember I i x f ∨
      ∃ j, M.mem j m ∧ M.IsOrdinalAddition I i n j ∧ M.PairMember I j x g := by
    rw [he i x, sat i x]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    exact (ordinalAddition_mem_iff hZF I mo hk).mpr (h.elim
      (fun h => Or.inl (hf.input_mem_of_pairMember h)) (fun ⟨j, hj, ha, _⟩ => Or.inr ⟨j, hj, ha⟩))
  refine ⟨k, F, ordinalAddition_mem_omega hZF I hω hn hm hk, hF, ⟨hf.1.1, ?_⟩, hg.1.1, ?_⟩
  · intro i x
    exact ⟨fun h => ⟨hf.input_mem_of_pairMember h, (graph i x).mpr (Or.inl h)⟩,
      fun ⟨hi, h⟩ => ((graph i x).mp h).elim id (fun ⟨j, hj, ha, _⟩ => (disjoint i j hi hj ha).elim)⟩
  · intro j x
    constructor
    · intro h
      have hj := hg.input_mem_of_pairMember h
      obtain ⟨i, hi, _⟩ := ordinalAddition_existsUnique hZF I n (mo.mem hj)
      exact ⟨hj, i, hi, (graph i x).mpr (Or.inr ⟨j, hj, hi, h⟩)⟩
    · rintro ⟨hj, i, hi, h⟩
      rcases (graph i x).mp h with h | ⟨l, hl, hh, h⟩
      · exact (disjoint i j (hf.input_mem_of_pairMember h) hj hi).elim
      · have eq := ordinalAddition_right_injective hZF I no (mo.mem hj) (mo.mem hl) hi hh
        exact eq.symm ▸ h

end YesMetaZFC.SetTheory
