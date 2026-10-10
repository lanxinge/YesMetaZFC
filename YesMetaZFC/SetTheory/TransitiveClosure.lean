import YesMetaZFC.SetTheory.CumulativeRank

/-! # 单元素集的内部传递闭包

Tc(x) 是包含 x 的最小传递集合，即通常的 TC({x})。先取实际累积层作为界，
再分离所有传递容器共有的成员；存在性、最小性和唯一性均在原 ZF 内证明。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Tc_d (x T : M.Domain) : Prop := M.TransitiveSet T ∧ M.mem x T ∧
  ∀ A, M.TransitiveSet A → M.mem x A → M.MemberSubset T A

def tc_m {n} (x T : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive T) (.conj (.mem x T) (.forallE
    (.imp (Formula.isTransitive .newest) (.imp (.mem x.weaken .newest) (Formula.subset T.weaken .newest)))))
derive_free_closed tc_m

theorem tc_sat_l {n} (ρ : Env M n) (x T : Term n) :
    Formula.satisfies ρ (tc_m x T) ↔ Tc_d (M := M) (x.eval ρ) (T.eval ρ) := by
  simp only [tc_m, Tc_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem tc_unique_l (hE : Extensional M) {x S T} (h : Tc_d (M := M) x S) (k : Tc_d (M := M) x T) : S = T :=
  hE.eq_of_same_members S T (fun y => ⟨h.2.2 T k.1 k.2.1 y, k.2.2 S h.1 h.2.1 y⟩)

theorem ZF.tc_exists_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) (x : M.Domain) : ∃ T, Tc_d (M := M) x T := by
  obtain ⟨α, V, hV, hxV⟩ := v_cover_l I hZF x
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  let φ : UnarySchema 1 := { body := .forallE (.imp (Formula.isTransitive .newest)
    (.imp (.mem (.bound 2) .newest) (.mem (.bound 1) .newest))) }
  have hφ y : φ.denote ρ y ↔ ∀ A, M.TransitiveSet A → M.mem x A → M.mem y A := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff]
    rfl
  obtain ⟨T, hT'⟩ := separation_exists_d hZF φ ρ V
  have hT y : M.mem y T ↔ M.mem y V ∧ ∀ A, M.TransitiveSet A → M.mem x A → M.mem y A :=
    (hT' y).trans (and_congr_right fun _ => hφ y)
  refine ⟨T, ?_, (hT x).mpr ⟨hxV, fun _ _ h => h⟩, fun A hA hxA y hy => ((hT y).mp hy).2 A hA hxA⟩
  intro y hy z hz
  obtain ⟨hyV, hy⟩ := (hT y).mp hy
  exact (hT z).mpr ⟨v_transitive_l I hZF hV y hyV z hz, fun A hA hxA => hA y (hy A hA hxA) z hz⟩

end YesMetaZFC.SetTheory
