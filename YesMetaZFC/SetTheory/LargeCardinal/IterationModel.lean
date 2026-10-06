import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource
import YesMetaZFC.Model.SetTheory.Internal.SourceBranchSyntax
import YesMetaZFC.Model.SetTheory.Internal.SourceRankSizeInitial
import YesMetaZFC.Model.SetTheory.Internal.SourcePower
import YesMetaZFC.Model.SetTheory.Internal.SourceCover
import YesMetaZFC.Model.SetTheory.Internal.RankSkolem

/-! # 下降递归所用模型及其实际初始实例

将复制步一直维护的性质合为一个可编码证书。正规 Vδ 提供初始实例；
重新选取字母表只改变有限列空间，其余性质仍属于同一个模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Pn_model_d (hZF : M.Models ZF) (ω κ K X R : M.Domain) : Prop where
  source : Ep_source_d hZF ω κ K X R
  branches : Sc_branch_d ω X
  hierarchy : Sc_hierarchy_d X
  power : Sc_power_d X
  cover : Sc_cover_d X
  small : Sh_source_d (ZF.modelsKP hZF) ω X
  inaccessible : Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X

def pn_branch_m {d} (ω X : Term d) : Formula 1 d := set[d] ⟪
  ∀ A ∈ ⌜X⌝ₛ, ∀ R ∈ ⌜X⌝ₛ, (∃ f, ⌜sb_chain_m⌝ₚ(⌜ω⌝ₛ, A, R, f)) →
    ∃ f ∈ ⌜X⌝ₛ, ⌜sb_chain_m⌝ₚ(⌜ω⌝ₛ, A, R, f)⟫
derive_free_closed pn_branch_m

private theorem pn_branch_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X : Term d) :
    Formula.satisfies ρ (pn_branch_m ω X) ↔ Sc_branch_d (ω.eval ρ) (X.eval ρ) := by
  simp only [pn_branch_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff, sb_chain_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h A R ha hr => h A ha R hr, fun h A ha R hr => h A R ha hr⟩

private def pn_base_m : Formula 1 0 := .conj sc_hierarchy_m (.conj sc_power_m sc_cover_m)
private theorem pn_base_closed_l : pn_base_m.FreeClosed := by
  simp -implicitDefEqProofs [pn_base_m, sc_hierarchy_m, Definitional.Formula.FreeClosed]

def pn_structure_m {d} (X : Term d) : Formula 1 d := lr_rel_m pn_base_m X Fin.elim0
@[simp] theorem pn_structure_closed_l {d} (X : Term d) (hx : X.freeSupport = []) : (pn_structure_m X).FreeClosed :=
  lr_rel_closed_l _ pn_base_closed_l X Fin.elim0 hx (fun i => Fin.elim0 i)

def pn_closure_m {d} (ω X : Term d) : Formula 1 d :=
  lr_rel_m (n := 1) (.conj (sh_source_m .newest) (sc_inaccessible_closure_m .newest)) X (fun _ => ω)
derive_free_closed pn_closure_m

def pn_model_m {d} (ω κ K X R : Term d) : Formula 1 d := .conj (ep_source_m ω κ K X R)
  (.conj (pn_branch_m ω X) (.conj (pn_structure_m X) (pn_closure_m ω X)))
derive_free_closed pn_model_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_model_sat_l {d} (ρ : Env M d) (ω κ K X R : Term d) :
    Formula.satisfies ρ (pn_model_m ω κ K X R) ↔ Pn_model_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have read (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ)) :
      (Formula.satisfies ρ (pn_structure_m X) ∧ Formula.satisfies ρ (pn_closure_m ω X)) ↔
        (Sc_hierarchy_d (X.eval ρ) ∧ Sc_power_d (X.eval ρ) ∧ Sc_cover_d (X.eval ρ)) ∧
          Sh_source_d (ZF.modelsKP hZF) (ω.eval ρ) (X.eval ρ) ∧ Sc_inaccessible_closure_d I (ω.eval ρ) (X.eval ρ) := by
    obtain ⟨c, hm⟩ := source.code
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, source.omega_mem⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 0 := ⟨Fin.elim0, fun _ => ⟨ω.eval ρ, source.omega_mem⟩⟩
    let θ : Env (rt_model_l (X.eval ρ) nx) 1 := ⟨fun _ => ⟨ω.eval ρ, source.omega_mem⟩, η.free⟩
    have base := sc_relative_sat_l I hm source.transitive nx pn_base_m pn_base_closed_l η ρ X Fin.elim0 rfl (fun i => Fin.elim0 i)
    have closure := sc_relative_sat_l I hm source.transitive nx
      (.conj (sh_source_m .newest) (sc_inaccessible_closure_m .newest)) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])
      θ ρ X (fun _ => ω) rfl (fun _ => rfl)
    simp only [pn_base_m, Formula.satisfies_conj_iff, sc_hierarchy_sat_l (ZF.modelsKP hZF) source.transitive nx,
      sc_power_sat_l source.transitive nx, sc_cover_sat_l source.transitive nx] at base
    rw [Formula.satisfies_conj_iff, source.skolem_source_sat_l hZF nx θ rfl,
      sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) source.transitive source.theory.algebra.pair nx θ .newest] at closure
    exact and_congr base closure
  simp only [pn_model_m, Formula.satisfies_conj_iff, ep_source_sat_l hZF, pn_branch_sat_l hZF.1]
  exact ⟨fun ⟨s, b, h⟩ => let ⟨⟨v, p, c⟩, k, i⟩ := (read s).mp h; ⟨s, b, v, p, c, k, i⟩,
    fun h => ⟨h.source, h.branches, (read h.source).mpr ⟨⟨h.hierarchy, h.power, h.cover⟩, h.small, h.inaccessible⟩⟩⟩

theorem Pn_model_d.rebase_l {ω κ K X R μ : M.Domain} (h : Pn_model_d hZF ω κ K X R)
    (hμ : M.mem μ X) (above : M.MemberSubset ω μ) (small : Sc_small_d X μ) : ∃ K', Pn_model_d hZF ω μ K' X R := by
  obtain ⟨K', s⟩ := h.source.rebase_l hZF hμ above small
  exact ⟨K', s, h.branches, h.hierarchy, h.power, h.cover, h.small, h.inaccessible⟩

/-- 初始模型就是给定正规秩层；所有递归字段均有原生构造。 -/
theorem pn_regular_model_l (hZFC : M.Models ZFC) {ω δ V : M.Domain} (hω : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) :
    ∃ K R, Pn_model_d (ZFC.models_zf_l hZFC) ω ω K V R := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K, seq⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω ω
  obtain ⟨R, s⟩ := ep_regular_source_l hZFC hω above regular rank above (fun _ h => h) seq
  exact ⟨K, R, s, sc_v_branch_l hZF regular.isLimitOrdinal rank s.omega_mem,
    sc_v_hierarchy_l hZF regular.isLimitOrdinal rank, sc_v_power_l hZF regular.isLimitOrdinal rank,
    sc_v_cover_l hZF rank, sh_source_of_v_l hZFC hω regular.isLimitOrdinal above rank,
    sc_v_inaccessible_closure_l hZFC hω regular.isLimitOrdinal rank⟩

end YesMetaZFC.SetTheory.LargeCardinal
