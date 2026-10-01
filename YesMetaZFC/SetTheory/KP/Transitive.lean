import YesMetaZFC.Model.SetTheory.KPInduction
import YesMetaZFC.SetTheory.KP.Sigma1

/-! # 完整成员归纳下的内部传递包络

逐成员收集已经存在的传递容器，取并后插入当前对象。证明在 KPi 内完成，
不经由 ZF 的 ω 递归或累积层级。
-/

namespace YesMetaZFC.SetTheory.KPi
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem transitive_cover_l (hM : M.Models KPi) (x : M.Domain) :
    ∃ T, M.TransitiveSet T ∧ M.mem x T := by
  obtain ⟨hKP, hi⟩ := models_iff_l.mp hM
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => x⟩
  let φ : UnarySchema 0 := {
    body := .existsE (.conj (Formula.isTransitive .newest) (.mem (.bound 1) .newest)) }
  have hφ y : φ.denote ρ y ↔ ∃ T, M.TransitiveSet T ∧ M.mem y T := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff]
    rfl
  apply (hφ x).mp (hi φ ρ ?_ x)
  intro y ih
  apply (hφ y).mpr
  let ψ : Delta0BinarySchema 0 := {
    body := .conj (Formula.isTransitive .newest) (.mem (.bound 1) .newest)
    delta0 := .conj (.forallMem _ (.forallMem _ (.mem _ _))) (.mem _ _) }
  have hψ z T : ψ.toBinarySchema.denote ρ z T ↔ M.TransitiveSet T ∧ M.mem z T := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff,
      Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff]
    rfl
  obtain ⟨C, hC⟩ := KP.collection_exists_d hKP ψ ρ y (fun z hz =>
    ((hφ z).mp (ih z hz)).imp (fun T hT => (hψ z T).mpr hT))
  let χ : Delta0UnarySchema 0 := {
    body := Formula.isTransitive .newest
    delta0 := .forallMem _ (.forallMem _ (.mem _ _)) }
  obtain ⟨D, hD'⟩ := KP.separation_exists_d hKP χ ρ C
  have hD T : M.mem T D ↔ M.mem T C ∧ M.TransitiveSet T := by
    simpa only [χ, Formula.satisfies_isTransitive_iff, Definitional.Term.eval_newest] using hD' T
  obtain ⟨U, hU⟩ := KP.exists_union hKP D
  have hu : M.TransitiveSet U := by
    rintro a ha b hb
    obtain ⟨T, hT, ha⟩ := (hU a).mp ha
    exact (hU b).mpr ⟨T, hT, ((hD T).mp hT).2 a ha b hb⟩
  have hy : M.MemberSubset y U := by
    intro z hz
    obtain ⟨T, hT, hzT⟩ := hC z hz
    obtain ⟨ht, hzT⟩ := (hψ z T).mp hzT
    exact (hU z).mpr ⟨T, (hD T).mpr ⟨hT, ht⟩, hzT⟩
  obtain ⟨T, hT⟩ := KP.exists_insert hKP U y
  refine ⟨T, ?_, (hT y).mpr (Or.inr rfl)⟩
  intro a ha b hb
  rcases (hT a).mp ha with ha | rfl
  · exact (hT b).mpr (Or.inl (hu a ha b hb))
  · exact (hT b).mpr (Or.inl (hy b hb))

end YesMetaZFC.SetTheory.KPi
