import YesMetaZFC.SetTheory.Ord.Code.NaturalBound
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 有限常值前缀后仍满射的内部枚举

在前 m 项使用指定元素；尾部按自然数对的第二坐标读取原满枚举，无代码时仍返回指定元素。
代码 (m,i) 不落入 m，故原枚举的每个值都在尾部实际出现。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem ce_prefix_l {ω B e m x : M.Domain} (hw : M.IsOmega ω) (hm : M.mem m ω) (hx : M.mem x B)
    (fn : M.IsSetFunctionFromTo I e ω B) (onto : M.IsSetSurjectiveOnto I e ω B) :
    ∃ f, M.IsSetFunctionFromTo I f ω B ∧
      (∀ i, M.mem i m → M.PairMember I i x f) ∧
      ∀ y, M.mem y B → ∃ i, M.mem i ω ∧ ¬ M.mem i m ∧ M.PairMember I i y f := by
  let codes i := ∃ a, M.mem a ω ∧ ∃ b, M.mem b ω ∧ Oc_pair_d I a b i
  let ρ : Env M 4 := ⟨fun k => [ω,m,e,x].get k,fun _ => x⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    ((⌜(.bound 1 : Term 6)⌝ₛ ∈ ⌜(.bound 3 : Term 6)⌝ₛ ∨
      ¬ (∃ a ∈ ⌜(.bound 2 : Term 6)⌝ₛ, ∃ b ∈ ⌜(.bound 2 : Term 6)⌝ₛ,
        ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(a,b,⌜(.bound 1 : Term 6)⌝ₛ))) →
      ⌜(.newest : Term 6)⌝ₛ = ⌜(.bound 5 : Term 6)⌝ₛ) ∧
    (∀ a ∈ ⌜(.bound 2 : Term 6)⌝ₛ, ∀ b ∈ ⌜(.bound 2 : Term 6)⌝ₛ,
      ⌜(.bound 1 : Term 6)⌝ₛ ∉ ⌜(.bound 3 : Term 6)⌝ₛ →
      ⌜(oc_pair_m (𝒞 := kpair_convention_l))⌝ₚ(a,b,⌜(.bound 1 : Term 6)⌝ₛ) →
      ⌜(Formula.orderedPairMem kpair_convention_l)⌝ₚ(b,⌜(.newest : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ))⟫ }
  have read i y : φ.denote ρ i y ↔ (M.mem i m ∨ ¬ codes i → y = x) ∧
      ∀ a, M.mem a ω → ∀ b, M.mem b ω → ¬ M.mem i m → Oc_pair_d I a b i → M.PairMember I b y e := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_disj_iff,Formula.satisfies_neg_iff,Formula.satisfies_existsMem_iff,
      Formula.satisfies_forallMem_iff,Formula.satisfies_mem_iff,oc_pair_sat_l I hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_orderedPairMem_iff I,Definitional.Term.eval_weaken]
    rfl
  have total i : ∃ y, φ.denote ρ i y := by
    classical
    by_cases hi : M.mem i m
    · exact ⟨x,(read i x).mpr ⟨fun _ => rfl,fun _ _ _ _ no _ => (no hi).elim⟩⟩
    · by_cases code : codes i
      · obtain ⟨a,ha,b,hb,pair⟩ := code
        obtain ⟨y,_,edge⟩ := fn.2.2 b hb
        refine ⟨y,(read i y).mpr ⟨fun h => h.elim (fun h => (hi h).elim)
          (fun h => (h ⟨a,ha,b,hb,pair⟩).elim),?_⟩⟩
        intro a' _ b' _ _ pair'
        exact (oc_pair_injective_l I hZF pair' pair).2.symm ▸ edge
      · exact ⟨x,(read i x).mpr ⟨fun _ => rfl,fun a ha b hb _ pair => (code ⟨a,ha,b,hb,pair⟩).elim⟩⟩
  have unique i y z (hy : φ.denote ρ i y) (hz : φ.denote ρ i z) : y = z := by
    classical
    by_cases fallback : M.mem i m ∨ ¬ codes i
    · exact ((read i y).mp hy).1 fallback |>.trans (((read i z).mp hz).1 fallback).symm
    · have hi : ¬ M.mem i m := fun h => fallback (Or.inl h)
      have code : codes i := Classical.byContradiction (fun h => fallback (Or.inr h))
      obtain ⟨a,ha,b,hb,pair⟩ := code
      exact fn.1.2 b y z (((read i y).mp hy).2 a ha b hb hi pair) (((read i z).mp hz).2 a ha b hb hi pair)
  have bounded i y (hy : φ.denote ρ i y) : M.mem y B := by
    classical
    by_cases fallback : M.mem i m ∨ ¬ codes i
    · exact (((read i y).mp hy).1 fallback).symm ▸ hx
    · have hi : ¬ M.mem i m := fun h => fallback (Or.inl h)
      obtain ⟨a,ha,b,hb,pair⟩ := Classical.byContradiction (fun h : ¬ codes i => fallback (Or.inr h))
      exact fn.output_mem_of_pairMember (((read i y).mp hy).2 a ha b hb hi pair)
  obtain ⟨f,ff,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (fun i _ => total i)
    (fun i _ => unique i) (fun i y _ hy => bounded i y hy)
  refine ⟨f,ff,?_,?_⟩
  · intro i hi
    exact (edges i x).mpr ⟨hw.transitive (ZF.modelsKP hZF) m hm i hi,
      (read i x).mpr ⟨fun _ => rfl,fun _ _ _ _ no _ => (no hi).elim⟩⟩
  · intro y hy
    obtain ⟨b,hb,be⟩ := onto y hy
    obtain ⟨i,pair⟩ := oc_pair_exists_l I hZF (hw.members_areOrdinals (ZF.modelsKP hZF) m hm)
      (hw.members_areOrdinals (ZF.modelsKP hZF) b hb)
    have hi := oc_pair_natural_l I hZF hw hm hb pair
    have outside : ¬ M.mem i m := fun h => KP.mem_irrefl_d (ZF.modelsKP hZF) i
      (oc_pair_left_bound_l I hZF hw hm hb pair i h)
    refine ⟨i,hi,outside,(edges i y).mpr ⟨hi,(read i y).mpr ⟨?_,?_⟩⟩⟩
    · intro fallback
      exact fallback.elim (fun h => (outside h).elim) (fun h => (h ⟨m,hm,b,hb,pair⟩).elim)
    · intro a _ b' _ _ pair'
      exact (oc_pair_injective_l I hZF pair' pair).2.symm ▸ be

end YesMetaZFC.SetTheory
