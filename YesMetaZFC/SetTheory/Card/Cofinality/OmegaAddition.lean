import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 不可数共尾性以下的 τ+ω

先对内部自然数证明 τ+n 仍在给定极限序数以下，再实际构造加法值域。
短序列有界性控制其并；这里只需要不可数共尾性，不需要强极限性。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
include hZF

theorem oa_finite_bound_l {ω δ τ n x : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hτ : M.mem τ δ) (hn : M.mem n ω) (hx : M.IsOrdinalAddition I x τ n) : M.mem x δ := by
  let φ : UnarySchema 2 := { body := .forallE (.imp (Formula.isOrdinalAddition 𝒞 .newest (.bound 2) (.bound 1))
    (.mem .newest (.bound 3))) }
  let ρ : Env M 2 := ⟨Fin.cases τ (fun _ => δ), fun _ => τ⟩
  have sat k : φ.denote ρ k ↔ ∀ y, M.IsOrdinalAddition I y τ k → M.mem y δ := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isOrdinalAddition_iff I hZF.1, Formula.satisfies_mem_iff]
    rfl
  have all : ∀ k, M.mem k ω → φ.denote ρ k := by
    apply hω.induction _ (ZF.separation_exists_d hZF φ ρ ω)
    · intro e he
      exact (sat e).mpr (fun y hy => ((ordinalAddition_zero_iff hZF I he).mp hy).symm ▸ hτ)
    · intro k hk ih l hs
      apply (sat l).mpr
      intro y hy
      obtain ⟨a, ha, next⟩ := (ordinalAddition_successor_iff hZF I (hω.members_areOrdinals (ZF.modelsKP hZF) k hk) hs).mp hy
      have haδ := (sat k).mp ih a ha
      obtain ⟨c, hc, hac⟩ := hδ.2.2 a haδ
      apply ordinal_down_l (modelsKP hZF) (KP.successor_isOrdinal (modelsKP hZF) (hδ.1.mem haδ) next) hδ.1
        (b := c) (fun v hv => ?_) hc
      exact ((next v).mp hv).elim ((hδ.1.mem hc).transitive a hac v)
        (fun eq => (hZF.1.eq_of_same_members v a eq).symm ▸ hac)
  exact (sat n).mp (all n hn) x hx

theorem oa_omega_bound_l {ω δ χ τ : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hχ : M.IsCofinality I χ δ) (hwχ : M.mem ω χ) (hτ : M.mem τ δ) :
    ∃ ℓ, M.IsOrdinalAddition I ℓ τ ω ∧ M.IsLimitOrdinal ℓ ∧ M.mem τ ℓ ∧ M.mem ℓ δ ∧
      ∀ η, M.IsLimitOrdinal η → M.mem τ η → M.MemberSubset ℓ η := by
  obtain ⟨ℓ, sum, _⟩ := ordinalAddition_existsUnique hZF I τ (hω.isOrdinal (ZF.modelsKP hZF))
  have limit := (ordinalAddition_isNormalOrdinalFunction hZF I (hδ.1.mem hτ)).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sum
  obtain ⟨e, he, heω⟩ := hω.1.1
  have hτℓ := (ordinalAddition_mem_iff hZF I (hω.isOrdinal (ZF.modelsKP hZF)) sum).mpr
    (Or.inr ⟨e, heω, (ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  let φ : BinarySchema 1 := { body := Formula.isOrdinalAddition 𝒞 .newest (.bound 2) (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => τ, fun _ => τ⟩
  have sat i x : φ.denote ρ i x ↔ M.IsOrdinalAddition I x τ i := Formula.satisfies_isOrdinalAddition_iff I hZF.1 ..
  obtain ⟨f, ff, graph⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := δ)
    (fun i hi => (ordinalAddition_existsUnique hZF I τ (hω.members_areOrdinals (ZF.modelsKP hZF) i hi)).imp fun x hx => (sat i x).mpr hx.1)
    (fun i hi x y hx hy => by
      obtain ⟨a, _, unique⟩ := ordinalAddition_existsUnique hZF I τ (hω.members_areOrdinals (ZF.modelsKP hZF) i hi)
      exact (unique x ((sat i x).mp hx)).trans (unique y ((sat i y).mp hy)).symm)
    (fun i x hi hx => oa_finite_bound_l hZF I hω hδ hτ hi ((sat i x).mp hx))
  obtain ⟨R, range⟩ := exists_range_of_setFunction hZF I ff.1 ff.2.1
  obtain ⟨β, hβ, bound⟩ := (hχ.range_bounded_of_domain_mem hZF I hwχ ff range).exists_bound
  obtain ⟨T, values, union⟩ := (ordinalAddition_limit_iff hZF I (hω.isLimitOrdinal (ZF.modelsKP hZF))).mp sum
  refine ⟨ℓ, sum, limit, hτℓ, ?_, ?_⟩
  · apply ordinal_down_l (modelsKP hZF) limit.1 hδ.1 (b := β) (fun x hx => ?_) hβ
    obtain ⟨v, hv, hxv⟩ := (union x).mp hx
    obtain ⟨i, hi, add⟩ := (values v).mp hv
    have hvR := (range v).mpr ⟨i, (graph i v).mpr ⟨hi, (sat i v).mpr add⟩⟩
    exact (bound v hvR).elim (fun eq => eq ▸ hxv) ((hδ.1.mem hβ).transitive v · x hxv)
  · intro η hη hτη x hx
    rcases (ordinalAddition_mem_iff hZF I (hω.isOrdinal (modelsKP hZF)) sum).mp hx with hx | ⟨i,hi,add⟩
    · exact hη.1.transitive τ hτη x hx
    · exact oa_finite_bound_l hZF I hω hη hτη hi add

end YesMetaZFC.SetTheory.ZF
