import YesMetaZFC.Model.SetTheory.Internal.SmallHull
import YesMetaZFC.SetTheory.Collapse.Cardinality
import YesMetaZFC.SetTheory.CumulativeRank

/-! # 传递参数的唯一 Σ₁ 输出保持基数界

将参数的全部成员放入实际小壳。坍塌固定参数，并将 Σ₁ 见证搬入传递值域；
向上绝对性与输出唯一性迫使输出也被固定。J 层的基数估计将直接使用此定理。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem s1_value_bound_l (hZFC : M.Models ZFC) {ω κ A Y : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsInfiniteCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ)
    (hA : M.TransitiveSet A) (ha : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A κ)
    (φ : S1_binary 0) (ρ : Env M 0) (hy : φ.schema.denote ρ A Y)
    (hu : ∀ Z, φ.schema.denote ρ A Z → Y = Z) :
    M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Y κ := by
  let hZF := ZFC.models_zf_l hZFC
  let hKP := ZF.modelsKP hZF
  let hM := ZF.models_kpi_l hZF
  let I := kp_pair_l hKP
  obtain ⟨T, hT⟩ := (φ.sat_l ρ A Y).mp hy
  obtain ⟨S, hS⟩ := KP.exists_insert hKP A A
  obtain ⟨Q, hQ⟩ := KP.exists_insert hKP S Y
  have hq := ZF.infinite_insert_l I hZF hω hκ (ZF.infinite_insert_l I hZF hω hκ ha hS) hQ
  obtain ⟨P, hP⟩ := KP.exists_insert hKP Q T
  obtain ⟨α, U, hU, hpU⟩ := ZF.v_cover_l I hZF P
  have htU := ZF.v_transitive_l I hZF hU
  have hQU : M.MemberSubset Q U := fun x hx => htU P hpU x ((hP x).mpr (Or.inl hx))
  have hAQ : M.mem A Q := (hQ A).mpr (Or.inl ((hS A).mpr (Or.inr rfl)))
  have hYQ : M.mem Y Q := (hQ Y).mpr (Or.inr rfl)
  have hTU : M.mem T U := htU P hpU T ((hP T).mpr (Or.inr rfl))
  obtain ⟨X, hs, hQX, hXκ⟩ := Internal.s1_hull_l I hZFC hω hκ ⟨A, hQU A hAQ⟩ hQU hq
  obtain ⟨B, F, htB, hf, he⟩ := mc_collapse_l hM (hs.extensional_l hKP.1 htU)
  have hAX : M.MemberSubset A X := fun x hx => hQX x ((hQ x).mpr (Or.inl ((hS x).mpr (Or.inl hx))))
  obtain ⟨a, haB, hAa⟩ := hf.function.2.1 A (hQX A hAQ)
  have eq := mc_fixed_subset_l hM hA hAX (fun _ h => h) ((he A a).mp hAa).2
  subst a
  obtain ⟨Z, hZB, hYZ⟩ := hf.function.2.1 Y (hQX Y hYQ)
  have hnB := hf.nonempty_l hs.nonempty
  let ξ : Env (rt_model_l X hs.nonempty) 2 :=
    ⟨Fin.cases ⟨Y, hQX Y hYQ⟩ (fun _ => ⟨A, hQX A hAQ⟩), fun _ => ⟨A, hQX A hAQ⟩⟩
  let η : Env (rt_model_l U hs.target_nonempty_l) 2 :=
    ⟨Fin.cases ⟨Y, hQU Y hYQ⟩ (fun _ => ⟨A, hQU A hAQ⟩), fun _ => ⟨A, hQU A hAQ⟩⟩
  let ζ : Env (rt_model_l B hnB) 2 :=
    ⟨Fin.cases ⟨Z, hZB⟩ (fun _ => ⟨A, haB⟩), fun _ => ⟨A, haB⟩⟩
  have hlocal : ∃ t, φ.matrix.toUnarySchema.denote η t := by
    refine ⟨⟨T, hTU⟩, (rt_model_delta_l htU hs.target_nonempty_l φ.matrix.delta0 (η.push ⟨T, hTU⟩)).mpr ?_⟩
    exact (Formula.closed_env_l _ φ.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))).mpr hT
  have small := (hs.witness _ _ φ.matrix ξ η (fun i => by cases i using Fin.cases <;> rfl)).mpr hlocal
  have moved := (hf.formula_l hs.nonempty hnB (.existsE φ.matrix.body) φ.schema.freeClosed ξ ζ
    (Fin.cases hYZ (fun _ => hAa))).mp ((Formula.satisfies_exists_iff ξ φ.matrix.body).mpr small)
  obtain ⟨t, ht⟩ := (Formula.satisfies_exists_iff ζ φ.matrix.body).mp moved
  have hz : φ.schema.denote ρ A Z := by
    apply (φ.sat_l ρ A Z).mpr
    refine ⟨t.val, ?_⟩
    have hh := (rt_model_delta_l htB hnB φ.matrix.delta0 (ζ.push t)).mp ht
    exact (Formula.closed_env_l _ φ.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))).mp hh
  have eq := hu Z hz
  subst Z
  obtain ⟨G, hG⟩ := ZF.exists_inclusionInjection hZF I (htB Y hZB)
  obtain ⟨H, hH⟩ := hf.pull_injection_l hKP hG
  obtain ⟨K, hK⟩ := hXκ
  exact ZF.exists_compositionInjection hZF I hH hK

end YesMetaZFC.SetTheory
