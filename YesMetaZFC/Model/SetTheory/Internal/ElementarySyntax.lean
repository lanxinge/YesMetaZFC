import YesMetaZFC.Model.SetTheory.Internal.TarskiVaughtSyntax

/-! # 内部子结构与完整初等性

子结构码保存实际限制关系。初等性量化全部内部公式码以及全部 ω→N 赋值，
比较两张内部满足关系；不是仅对宿主标准公式的外部保持断言。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Ssub_d (c d X R N S : M.Domain) : Prop where
  source : Smdl_d I c X R
  target : Smdl_d I d N S
  subset : M.MemberSubset N X
  relation : ∀ x y, M.PairMember I x y S ↔ M.mem x N ∧ M.mem y N ∧ M.PairMember I x y R

def ssub_m {n} (c d X R N S : Term n) : Formula 1 n :=
  .conj (smdl_m (𝒞 := 𝒞) c X R) (.conj (smdl_m (𝒞 := 𝒞) d N S) (.conj (Formula.subset N X)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest S.weaken.weaken)
      (.conj (.mem (.bound 1) N.weaken.weaken) (.conj (.mem .newest N.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))))))
derive_free_closed ssub_m

theorem ssub_sat_l {n} (ρ : Env M n) (c d X R N S : Term n) :
    Formula.satisfies ρ (ssub_m (𝒞 := 𝒞) c d X R N S) ↔
      Ssub_d I (c.eval ρ) (d.eval ρ) (X.eval ρ) (R.eval ρ) (N.eval ρ) (S.eval ρ) := by
  simp only [ssub_m, Formula.satisfies_conj_iff, smdl_sat_l I, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.source, h.target, h.subset, h.relation⟩⟩

/-- 任意非空内部子集的诱导结构都有实际结构码。 -/
theorem smdl_substructure_l (hZF : M.Models ZF) {c X R N} (hM : Smdl_d I c X R)
    (hN : M.MemberSubset N X) (hne : ∃ x, M.mem x N) : ∃ d S, Ssub_d I c d X R N S := by
  let ρ : Env M 1 := ⟨fun _ => R, fun _ => R⟩
  let φ : BinarySchema 1 := { body := Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2) }
  obtain ⟨d, S, hS, hs⟩ := smdl_exists_l I hZF φ ρ hne
  refine ⟨d, S, hM, hS, hN, fun x y => (hs x y).trans ?_⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl (Formula.satisfies_orderedPairMem_iff I _ _ _ _))

def Selem_d (ω c d : M.Domain) : Prop := ∃ X R N S C,
  Ssub_d I c d X R N S ∧ Scode_d I ω C ∧ ∀ a f, M.mem a C → M.IsSetFunctionFromTo I f ω N →
    (Satisfies_d I ω c a f ↔ Satisfies_d I ω d a f)

def selem_m {n} (ω c d : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ssub_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken.weaken d.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1)) (.conj
    (scode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken .newest)
    (Formula.forallMem .newest (.forallE (.imp
      (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4))
      (.iff (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
        c.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest)
        (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          d.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest)))))))))))
derive_free_closed selem_m

theorem selem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c d : Term n) :
    Formula.satisfies ρ (selem_m (𝒞 := 𝒞) ω c d) ↔ Selem_d I (ω.eval ρ) (c.eval ρ) (d.eval ρ) := by
  simp only [selem_m, Selem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ssub_sat_l I, scode_sat_l I hE, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_iff_iff, satisfies_sat_l I hE, Definitional.Term.eval_weaken]
  exact exists_congr fun X => exists_congr fun R => exists_congr fun N => exists_congr fun S =>
    exists_congr fun C => and_congr Iff.rfl (and_congr Iff.rfl
      ⟨fun h a f ha hf => h a ha f hf, fun h a ha f hf => h a f ha hf⟩)

/-- 初等性不依赖码内存在量化见证的选择，恢复到指定的两份实际结构。 -/
theorem selem_decode_l (hE : Extensional M) {ω c d X R N S C}
    (hS : Ssub_d I c d X R N S) (hC : Scode_d I ω C) :
    Selem_d I ω c d ↔ ∀ a f, M.mem a C → M.IsSetFunctionFromTo I f ω N →
      (Satisfies_d I ω c a f ↔ Satisfies_d I ω d a f) := by
  constructor
  · rintro ⟨Y, Q, B, T, D, hT, hD, h⟩
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I hS.source hT.source
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I hS.target hT.target
    have he := scode_unique_l I hE hC hD
    exact he ▸ h
  · exact fun h => ⟨X, R, N, S, C, hS, hC, h⟩

end YesMetaZFC.SetTheory.Internal
