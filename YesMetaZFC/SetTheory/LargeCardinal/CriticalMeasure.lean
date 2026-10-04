import YesMetaZFC.SetTheory.LargeCardinal.DerivedFilter
import YesMetaZFC.SetTheory.LargeCardinal.Woodin
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 临界点派生测度的非主性

若 κ=crit(j)，以 κ 为种子得到的超滤不包含任何单点集：
j 固定每个 x<κ，故 j({x})={x}，但种子 κ 不等于 x。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ed_nonprincipal_d (U : M.Domain) : Prop :=
  ∀ x s, (∀ y, M.mem y s ↔ y = x) → ¬ M.mem s U

def ed_nonprincipal_m {d} (U : Term d) : Formula 1 d := .forallE (.forallE (.imp
  (.forallE (.iff (.mem .newest (.bound 1)) (Formula.extensionalEq .newest (.bound 2))))
  (.neg (.mem .newest U.weaken.weaken))))
derive_free_closed ed_nonprincipal_m

theorem ed_nonprincipal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (U : Term d) :
    Formula.satisfies ρ (ed_nonprincipal_m U) ↔ Ed_nonprincipal_d (U.eval ρ) := by
  simp only [ed_nonprincipal_m, Ed_nonprincipal_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  rfl

theorem ed_critical_nonprincipal_l (hZF : M.Models ZF) {ω X A Y B j κ k U}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ k) (hU : Ed_filter_d I j κ κ U) : Ed_nonprincipal_d U := by
  intro x s hs hsU
  obtain ⟨hsub, s', hjs, hκ⟩ := (hU s).mp hsU
  have hx := hsub x ((hs x).mpr rfl)
  have hjx := hc.fixed x hx
  have tr := spred_delta_l I hZF hω h hX hY (n := 2)
    (Formula.forallMem (.bound 1) (Formula.extensionalEq .newest (.bound 1)))
    (by simp) (.forallMem _ (.atom _ _ _))
    ⟨Fin.cases x (fun _ => s), fun _ => x⟩ ⟨Fin.cases x (fun _ => s'), fun _ => x⟩
    (Fin.cases hjx (fun _ => hjs))
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] at tr
  have he : κ = x := tr.mp (fun y hy => (hs y).mp hy) κ hκ
  exact KP.mem_irrefl_d (ZF.modelsKP hZF) κ (he.symm ▸ hx)

/-- 从临界点嵌入同时返回派生图、极大适当性与非主性。 -/
theorem ed_critical_measure_l (hZF : M.Models ZF) {ω X A Y B j κ k P}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ k) (hκ : M.mem κ k) (hP : M.IsPowerSetOf P κ) (hPX : M.mem P X) :
    ∃ U, Ed_filter_d I j κ κ U ∧ FilterZF.Maximal_d (ℳ := M) κ U ∧ Ed_nonprincipal_d U := by
  obtain ⟨U, hU, hu⟩ := ed_ultrafilter_l I hZF hω h hX hY hP hPX hc.image hκ
  exact ⟨U, hU, hu, ed_critical_nonprincipal_l I hZF hω h hX hY hc hU⟩

end YesMetaZFC.SetTheory.LargeCardinal
