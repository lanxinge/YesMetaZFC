import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 可良序定义域的函数像基数界

固定定义域到序数 κ 的单射，为每个像点取其原像编号中的最小者，得到像到 κ
的实际单射。只用 ZF；不从任意满射直接调用选择公理。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ord_image_d (G F x n : M.Domain) : Prop := ∃ a, M.PairMember I a n G ∧ M.PairMember I a x F

def ord_image_m {d} (G F x n : Term d) : Formula 1 d :=
  .existsE (.conj (Formula.orderedPairMem 𝒞 .newest n.weaken G.weaken)
    (Formula.orderedPairMem 𝒞 .newest x.weaken F.weaken))
derive_free_closed ord_image_m

theorem ord_image_sat_l {d} (ρ : Env M d) (G F x n : Term d) :
    Formula.satisfies ρ (ord_image_m (𝒞 := 𝒞) G F x n) ↔
      Ord_image_d I (G.eval ρ) (F.eval ρ) (x.eval ρ) (n.eval ρ) := by
  simp only [ord_image_m, Ord_image_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 定义域可单射到序数 κ 时，任意满射的目标也可单射到 κ；不要求目标非空。 -/
theorem ZF.ordinal_image_bound_l (hZF : M.Models ZF) {κ A B F} (hκ : M.IsOrdinal κ)
    (hA : M.CardinalLessOrEqual I A κ) (hF : M.IsSetFunctionFromTo I F A B)
    (hs : M.IsSetSurjectiveOnto I F A B) : M.CardinalLessOrEqual I B κ := by
  obtain ⟨G, hG⟩ := hA
  let ρ : Env M 3 := ((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push G).push F
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 4)) (.conj (ord_image_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest)
      (.forallE (.imp (ord_image_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) .newest) (.neg (.mem .newest (.bound 1)))))) }
  have hφ x n : φ.denote ρ x n ↔ M.mem n κ ∧ Ord_image_d I G F x n ∧
      ∀ m, Ord_image_d I G F x m → ¬ M.mem m n := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      ord_image_sat_l I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff]
    rfl
  apply ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro x hx
    let η : Env M 3 := ((⟨fun _ => G, fun _ => G⟩ : Env M 1).push F).push x
    let ψ : UnarySchema 3 := { body := ord_image_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ η κ
    have hd n : M.mem n D ↔ M.mem n κ ∧ Ord_image_d I G F x n :=
      (hD n).trans (and_congr_right fun _ => ord_image_sat_l I _ _ _ _ _)
    obtain ⟨a, ha, hax⟩ := hs x hx
    obtain ⟨n, hn, han⟩ := hG.1.2.2 a ha
    obtain ⟨m, hm, hmin⟩ := hκ.wellOrder.least D (fun i hi => ((hd i).mp hi).1)
      ⟨n, (hd n).mpr ⟨hn, a, han, hax⟩⟩
    have hmκ := ((hd m).mp hm).1
    refine ⟨m, (hφ x m).mpr ⟨hmκ, ((hd m).mp hm).2, fun j hj hjm => ?_⟩⟩
    have hjκ := hj.elim fun a ha => hG.1.output_mem_of_pairMember ha.1
    rcases hmin j ((hd j).mpr ⟨hjκ, hj⟩) with he | hmj
    · have he := hZF.1.eq_of_same_members m j he
      subst j
      exact hκ.wellOrder.linear.irrefl m hmκ hjm
    · exact hκ.wellOrder.linear.irrefl m hmκ (hκ.wellOrder.linear.trans m hmκ j hjκ m hmκ hmj hjm)
  · intro x _ n m hn hm
    obtain ⟨hnκ, hnx, hn⟩ := (hφ x n).mp hn
    obtain ⟨hmκ, hmx, hm⟩ := (hφ x m).mp hm
    rcases hκ.wellOrder.linear.compare n hnκ m hmκ with he | hnm | hmn
    · exact hZF.1.eq_of_same_members n m he
    · exact (hm n hnx hnm).elim
    · exact (hn m hmx hmn).elim
  · exact fun x n _ hn => ((hφ x n).mp hn).1
  · intro x y n _ _ hx hy
    obtain ⟨a, ha, hax⟩ := ((hφ x n).mp hx).2.1
    obtain ⟨b, hb, hby⟩ := ((hφ y n).mp hy).2.1
    have he := hG.2 a b n ha hb
    subst b
    exact hF.1.2 a x y hax hby

end YesMetaZFC.SetTheory
