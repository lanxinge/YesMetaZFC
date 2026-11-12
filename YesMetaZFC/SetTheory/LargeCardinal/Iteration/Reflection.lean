import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Reflection.RankSkolem
import YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.CumulativeRelative
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 下降递归所用模型及其实际初始实例

将复制步一直维护的性质合为一个可编码证书。正规 Vδ 提供初始实例；
重新选取字母表只改变有限列空间，其余性质仍属于同一个模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Pn_model_d (hZF : M.Models ZF) (ω κ K X R : M.Domain) : Prop where
  source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R
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
  have read (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ)) :
      (Formula.satisfies ρ (pn_structure_m X) ∧ Formula.satisfies ρ (pn_closure_m ω X)) ↔
        (Sc_hierarchy_d (X.eval ρ) ∧ Sc_power_d (X.eval ρ) ∧ Sc_cover_d (X.eval ρ)) ∧
          Sh_source_d (ZF.modelsKP hZF) (ω.eval ρ) (X.eval ρ) ∧ Sc_inaccessible_closure_d I (ω.eval ρ) (X.eval ρ) := by
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, source.omega_mem⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 0 := ⟨Fin.elim0, fun _ => ⟨ω.eval ρ, source.omega_mem⟩⟩
    let θ : Env (rt_model_l (X.eval ρ) nx) 1 := ⟨fun _ => ⟨ω.eval ρ, source.omega_mem⟩, η.free⟩
    have base := sc_relative_sat_l source.transitive nx pn_base_m pn_base_closed_l η ρ X Fin.elim0 rfl (fun i => Fin.elim0 i)
    have closure := sc_relative_sat_l source.transitive nx
      (.conj (sh_source_m .newest) (sc_inaccessible_closure_m .newest)) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])
      θ ρ X (fun _ => ω) rfl (fun _ => rfl)
    simp only [pn_base_m, Formula.satisfies_conj_iff, sc_hierarchy_sat_l (ZF.modelsKP hZF) source.transitive nx,
      sc_power_sat_l source.transitive nx, sc_cover_sat_l source.transitive nx] at base
    rw [Formula.satisfies_conj_iff, source.skolem_source_sat_l hZF nx θ rfl,
      sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair nx θ .newest] at closure
    exact and_congr base closure
  simp only [pn_model_m, Formula.satisfies_conj_iff, ep_source_sat_l (ZF.modelsKP hZF), pn_branch_sat_l hZF.1]
  exact ⟨fun ⟨s, b, h⟩ => let ⟨⟨v, p, c⟩, k, i⟩ := (read s).mp h; ⟨s, b, v, p, c, k, i⟩,
    fun h => ⟨h.source, h.branches, (read h.source).mpr ⟨⟨h.hierarchy, h.power, h.cover⟩, h.small, h.inaccessible⟩⟩⟩

theorem Pn_model_d.rebase_l {ω κ K X R μ : M.Domain} (h : Pn_model_d hZF ω κ K X R)
    (hμ : M.mem μ X) (above : M.MemberSubset ω μ) (small : Rf_small_d (kp_pair_l (ZF.modelsKP hZF)) X R μ) : ∃ K', Pn_model_d hZF ω μ K' X R := by
  obtain ⟨K', s⟩ := h.source.rebase_l hμ above small
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
    sc_v_hierarchy_l hZF regular.isLimitOrdinal rank, sc_v_power_l (ZF.modelsKP hZF) regular.isLimitOrdinal rank,
    sc_v_cover_l hZF rank, sh_source_of_v_l hZFC hω regular.isLimitOrdinal above rank,
    sc_v_inaccessible_closure_l hZFC hω regular.isLimitOrdinal rank⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 整树复制中的可数闭工作模型

秩层、幂集、小覆盖及不可达闭包统一解释在工作模型的原关系中，完整全称核
沿实际初等图搬运，覆盖新参数。正规秩层仍给出原初值；源数据和外部可数闭性
保持既有条件，不从这份有限核推断工作模型满足完整 ZFC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 秩层、幂集、小覆盖及不可达闭包组成同一有限全称核。 -/
def ic_core0_m : Formula 1 1 :=
  .conj ((.conj sc_hierarchy_m (.conj sc_power_m sc_cover_m) : Formula 1 0).rename Fin.elim0)
    (sc_inaccessible_closure_m .newest)

theorem ic_core0_closed_l : ic_core0_m.FreeClosed := by
  simp -implicitDefEqProofs [ic_core0_m, sc_hierarchy_m, Definitional.Formula.FreeClosed]

def ic_core_m {d} (ω X R : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) ic_core0_m X R (fun _ : Fin 1 => ω)

@[simp] theorem ic_core_closed_l {d} (ω X R : Term d)
    (hw : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (ic_core_m ω X R).FreeClosed := rr_truth_closed_l _ ic_core0_closed_l _ _ _ hX hR (fun _ => hw)

theorem ic_core_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d) (ω X R : Term d) :
    Formula.satisfies ρ (ic_core_m ω X R) ↔
      Rr_truth_d I (X.eval ρ) (R.eval ρ) ic_core0_m (fun _ : Fin 1 => ω.eval ρ) := by
  rw [ic_core_m, rr_truth_sat_l I _ _ ic_core0_closed_l]

/-- 字面读取只使用实际隶属码、传递性、ω 所属及配对闭包。 -/
theorem ic_core_mem_l (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
    {c ω X R : M.Domain} (model : Smem_d I c X R) (xt : M.TransitiveSet X) (hw : M.mem ω X)
    (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b) :
    Rr_truth_d I X R ic_core0_m (fun _ : Fin 1 => ω) ↔
      Sc_hierarchy_d X ∧ Sc_power_d X ∧ Sc_cover_d X ∧ Sc_inaccessible_closure_d (kp_pair_l hKP) ω X := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω,hw⟩,fun _ => ⟨ω,hw⟩⟩
  have read : Rr_truth_d I X R ic_core0_m (fun _ : Fin 1 => ω) ↔ Formula.satisfies ρ ic_core0_m :=
    ⟨fun ⟨_,h⟩ => (smem_formula_l I model nx ic_core0_m ρ).mpr h,
      fun h => ⟨fun _ => hw,(smem_formula_l I model nx ic_core0_m ρ).mp h⟩⟩
  rw [read, ic_core0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename]
  simp only [Formula.satisfies_conj_iff, sc_hierarchy_sat_l hKP xt nx,
    sc_power_sat_l xt nx, sc_cover_sat_l xt nx, sc_inaccessible_closure_sat_l hKP xt pair nx]
  exact and_assoc.trans (and_congr_right fun _ => and_assoc)

structure Ic_model_d (hZF : M.Models ZF) (ω κ K X R : M.Domain) : Prop where
  source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R
  closed : Sc_omega_closed_d (kp_pair_l (ZF.modelsKP hZF)) ω X R
  core : Rr_truth_d (kp_pair_l (ZF.modelsKP hZF)) X R ic_core0_m (fun _ : Fin 1 => ω)

def ic_model_m {d} (ω κ K X R : Term d) : Formula 1 d := .conj (ep_source_m ω κ K X R)
  (.conj (sc_omega_closed_m ω X R) (ic_core_m ω X R))
derive_free_closed ic_model_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_model_sat_l {d} (ρ : Env M d) (ω κ K X R : Term d) :
    Formula.satisfies ρ (ic_model_m ω κ K X R) ↔
      Ic_model_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [ic_model_m, Formula.satisfies_conj_iff, ep_source_sat_l (ZF.modelsKP hZF),
    sc_omega_closed_sat_l I hZF.1, ic_core_sat_l I]
  exact ⟨fun ⟨s,c,k⟩ => ⟨s,c,k⟩, fun h => ⟨h.source,h.closed,h.core⟩⟩

/-- 现有隶属源的实际消费者从同一原关系核读取四项结构条件。 -/
theorem Ic_model_d.read_l {ω κ K X R : M.Domain} (h : Ic_model_d hZF ω κ K X R) :
    Sc_hierarchy_d X ∧ Sc_power_d X ∧ Sc_cover_d X ∧ Sc_inaccessible_closure_d I ω X := by
  obtain ⟨c, model⟩ := h.source.code
  exact (ic_core_mem_l I (ZF.modelsKP hZF) model h.source.transitive h.source.omega_mem (h.source.algebra_l (ZF.modelsKP hZF)).pair).mp h.core

theorem Ic_model_d.rebase_l {ω κ K X R μ : M.Domain} (h : Ic_model_d hZF ω κ K X R)
    (hμ : M.mem μ X) (above : M.MemberSubset ω μ) (small : Rf_small_d (kp_pair_l (ZF.modelsKP hZF)) X R μ) :
    ∃ K', Ic_model_d hZF ω μ K' X R := by
  obtain ⟨K', s⟩ := h.source.rebase_l hμ above small
  exact ⟨K', s, h.closed, h.core⟩

variable (hZFC : M.Models ZFC)

theorem ic_regular_model_l {ω δ V : M.Domain} (hω : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) :
    ∃ K R, Ic_model_d (ZFC.models_zf_l hZFC) ω ω K V R := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K, seq⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω ω
  obtain ⟨R, s⟩ := ep_regular_source_l hZFC hω above regular rank above (fun _ h => h) seq
  obtain ⟨c, model⟩ := s.code
  exact ⟨K, R, s, sc_v_omega_closed_l hZF hω regular above rank s.omega_mem model,
    (ic_core_mem_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.modelsKP hZF) model s.transitive s.omega_mem (s.algebra_l (ZF.modelsKP hZF)).pair).mpr
      ⟨sc_v_hierarchy_l hZF regular.isLimitOrdinal rank, sc_v_power_l (ZF.modelsKP hZF) regular.isLimitOrdinal rank,
        sc_v_cover_l hZF rank, sc_v_inaccessible_closure_l hZFC hω regular.isLimitOrdinal rank⟩⟩

/-- 所属源只须对有界值域可数闭；工作源的完整闭性由同一个超幂保持。 -/
theorem Ic_model_d.ultra_l {ω κ K X R K' Y R' L F c d N S j : M.Domain}
    (h : Ic_model_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R') (agree : Ea_agree_d ω κ X Y)
    (closed : Sc_bounded_omega_closed_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω Y R') (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Y L)
    (hL : M.IsLimitOrdinal L) (loc : It_local_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω Y R' κ L F) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L Y F)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F c d j) :
    ∃ K₀, Ic_model_d (ZFC.models_zf_l hZFC) ω ω K₀ N S := by
  let hZF := ZFC.models_zf_l hZFC
  have hN := ultra.transitive_l hZF hn.1
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hw := hj.omega_l (kp_pair_l (ZF.modelsKP hZF)) hZF h.source.omega h.source.transitive hN hm hn h.source.omega_mem
  obtain ⟨K₀, s⟩ := h.source.successor_l hZF hm hn hN hj (hj.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    ((hj.small_l (kp_pair_l (ZF.modelsKP hZF)) hZF h.source.omega hm.1 hn.1 hw).mp (h.source.cardinal_small.mono_mem_l (kp_pair_l (ZF.modelsKP hZF)) hm h.source.omega_mem h.source.below))
  obtain ⟨hierarchy, power, _, _⟩ := h.read_l hZF
  exact ⟨K₀, s, ultra.closed_l hZFC h.source owner agree h.closed closed hierarchy power op oc bound sizes hL loc strength hm hn,
    Rr_truth_d.map_l (kp_pair_l (ZF.modelsKP hZF)) hZF h.source.omega hm.1 hn.1 hj ic_core0_closed_l h.core (fun _ => hw)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数闭工作模型的实际 nice 后继

所属模型可以不同于施加源。原内部共同纤维产生良基超幂，最大强度识别
两侧共同秩段。扩展器来自拥有秩段时，先逐项向上读取原公式，再施加同一扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_model_d.apply_l {ω κ K X R K' Y S L F c : M.Domain}
    (h : Ic_model_d hZF ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (closed : Sc_bounded_omega_closed_d I ω Y S) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (agree : Ea_agree_d ω κ X Y)
    (hm : Smem_d I c X R) (loc : It_local_d I ω Y S κ L F)
    (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F) (hL : M.IsLimitOrdinal L) :
    ∃ N V d j K₀ W, Smem_d I d N V ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j ∧
      Ic_model_d hZF ω L K₀ N V ∧ M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
      Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  obtain ⟨co, mo⟩ := owner.code
  have data := loc
  obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp data
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hwL := hL.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := hL.1.transitive ω hwL
  obtain ⟨P, hP, ps⟩ := op K' owner.finite.mem_l
  obtain ⟨J, O, Z, A, p, T, U, q, b, C, W, system, limit, model, _, _, collapse⟩ :=
    loc.closed_limit_l hZFC h.source owner closed agree hP ps
  obtain ⟨_, c₀, i, N, e, _, d, V, j, mx, hi, constants, ht, wc, bij, hn, he, _, _, _, hj, js, _⟩ := collapse
  obtain ⟨eq, _⟩ := smem_unique_l I hZF.1 mx hm
  subst c₀
  have ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j := ⟨X, R, N, V, J, O, Z, A, p, T, U, q, b, C, W, i, e,
    hm, hn, system, limit, model, wc, bij, he, hi, constants, hj, hj.1.1.1.1,
    fun x y => (js x y).trans ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  obtain ⟨K₁, next⟩ := h.ultra_l hZFC owner agree closed op oc bound sizes hL loc strength hm hn ultra
  have reverse : Ea_agree_d ω κ Y X := fun n D B hn hd sub => (agree n D B hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP ps)).transfer_l reverse
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have seed := (ep_seed_collapse_l hZF h.source ord.1.transitive hL.1.transitive family coherent
    (loc.atoms_l hZF (owner.read_source_l hZF) owner.code) ((loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner h.source agree.subset_l)
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have hLN := ep_support_mem_l hZFC h.source family coherent system limit model ht hn he seed ord.1 hL.1
  obtain ⟨K₀, ready⟩ := next.rebase_l hZF hLN below
    (sc_ordinal_small_l hZF h.source.omega ht hn next.source.theory hLN hL.1)
  have successor : Ep_successor_d hZF ω κ L X R F N V :=
    ⟨J, O, Z, A, p, T, U, q, b, C, W, d, e, system, limit, model, hn, ht, wc, bij, he⟩
  obtain ⟨rₛ, pₛ, _, _⟩ := ready.read_l hZF
  obtain ⟨W₀, hw, rank, level, sizes', exactness, common⟩ := loc.rank_agree_l hZFC h.source owner ready.source
    agree (closed.branch_l (ZF.modelsKP hZF) owner.omega owner.transitive mo owner.omega_mem) op oc rₛ pₛ sizes hL successor strength
  exact ⟨N, V, d, j, K₀, W₀, hn, ultra, ready, hw, rank, level, sizes', exactness, common⟩

/-- 小秩段中的 nice 判断先向上保持；输出的边实际施加到完整工作源。 -/
theorem Ic_model_d.rank_apply_l {ω κ K X R K' Y S δ A R₀ L F c : M.Domain}
    (h : Ic_model_d hZF ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (closed : Sc_bounded_omega_closed_d I ω Y S) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (agree : Ea_agree_d ω κ X Y) (hm : Smem_d I c X R)
    (hA : M.mem A Y) (rank : Vr_d Y δ A) (hδ : M.IsLimitOrdinal δ)
    (code : ∃ a, Smem_d I a A R₀) (loc : It_local_d I ω A R₀ κ L F) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L A F)
    (inaccessible : Sc_inaccessible_d ω A L) :
    It_local_d I ω Y S κ L F ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F ∧ Sc_inaccessible_d ω Y L ∧
      ∃ N V d j K₀ W, Smem_d I d N V ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j ∧
        Ic_model_d hZF ω L K₀ N V ∧ M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
        Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  have up := loc.of_rank_l hZF owner hA rank hδ code
  have strong := strength.of_rank_l hZF owner.transitive hA rank hδ
  have card := inaccessible.of_rank_l hZF owner.transitive (owner.algebra_l (ZF.modelsKP hZF)).pair hA rank hδ
  have hL := card.limit_l (ZF.modelsKP hZF) owner.transitive (owner.algebra_l (ZF.modelsKP hZF)).pair
  exact ⟨up, strong, card, h.apply_l hZFC owner closed op oc bound sizes agree hm up strong hL⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限原公式族的两层反射上下文

内层由有限反射实际产生，包含指定参数及 ω；外层取包含内层及其高度的
正则秩包络。相对秩历史和有限读写闭包保存在这同一个外层中，供不同
迭代构造读取各自的有限规则，不把某个游戏的全称核写进通用工厂。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 同一实际隶属模型中的相对秩、极限高度和有限闭包进入原关系真值。 -/
theorem ir_context_data_l (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
    {ω c X R η C : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R)
    (hη : M.mem η X) (hC : M.mem C X) (rank : Vr_d X η C) (limit : M.IsLimitOrdinal η)
    (finite : Fs_read_d ω C) :
    Rr_truth_d (n := 1) I X R (v_sigma_m (.bound 1) .newest) (Fin.cases C (fun _ => η)) ∧
    Rr_truth_d (n := 0) I X R (Formula.isLimitOrdinal .newest) (fun _ => η) ∧
    Rr_truth_d (n := 1) I X R (fs_read_m (.bound 1) .newest) (Fin.cases C (fun _ => ω)) := by
  have hw := trans C hC ω finite.omega_mem
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω,hw⟩⟩
  let N := rt_model_l X nx
  have en := rt_model_ext_l hKP.1 trans nx
  have move {n} (φ : Formula 1 (n+1)) (v : Fin (n+1) → N.Domain)
      (valid : Formula.satisfies (⟨v,fun _ => v 0⟩ : Env N (n+1)) φ) :
      Rr_truth_d I X R φ (fun i => (v i).val) :=
    ⟨fun i => (v i).property,(smem_formula_l I model nx φ _).mp valid⟩
  let r : Fin 2 → N.Domain := fun i =>
    ⟨(Fin.cases C (fun _ => η) : Fin 2 → M.Domain) i,Fin.cases hC (fun _ => hη) i⟩
  let f : Fin 2 → N.Domain := fun i =>
    ⟨(Fin.cases C (fun _ => ω) : Fin 2 → M.Domain) i,Fin.cases hC (fun _ => hw) i⟩
  exact ⟨move _ r ((vr_sat_l hKP trans nx _ (.bound 1) .newest).mpr rank),
    move _ (fun _ => ⟨η,hη⟩)
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr ((rt_limit_l trans nx hKP ⟨η,hη⟩).mpr limit)),
    move _ f ((fs_read_sat_l en _ (.bound 1) .newest).mpr
      (finite.source_l hKP.1 trans nx ⟨ω,hw⟩ ⟨C,hC⟩))⟩

/-- 两层、原关系码和全部有限反射证书来自同一次实际构造。 -/
theorem ir_context_l (hZFC : M.Models ZFC) {ω : M.Domain}
    (hω : M.IsOmega ω) (A : M.Domain) (Φ : List Lr_formula) :
    ∃ θ X R c K η C,
      M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ X ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R ∧
      Ic_model_d (ZFC.models_zf_l hZFC) ω ω K X R ∧
      M.mem η X ∧ M.mem C X ∧ Vr_d X η C ∧ M.IsLimitOrdinal η ∧
      Fs_read_d ω C ∧ M.mem A C ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P,pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω A
  obtain ⟨η,C,rank,limit,hP,reflect⟩ := ZF.lr_finite_l I hZF Φ P
  have trans := v_transitive_l I rank
  have hωC := trans P hP ω ((pair ω).mpr (Or.inl rfl))
  have hAC := trans P hP A ((pair A).mpr (Or.inr rfl))
  obtain ⟨B,pair'⟩ := KP.exists_pair (ZF.modelsKP hZF) η C
  obtain ⟨θ,X,regular,above,outer,hB⟩ := ZFC.v_regular_cover_l I hZFC hω B
  obtain ⟨K,R,source⟩ := ic_regular_model_l hZFC hω above regular outer
  obtain ⟨c,code⟩ := source.source.code
  have hηX := source.source.transitive B hB η ((pair' η).mpr (Or.inl rfl))
  have hCX := source.source.transitive B hB C ((pair' C).mpr (Or.inr rfl))
  obtain ⟨D,F,hD,hF,cert,_⟩ := vr_source_l hZF outer regular.isLimitOrdinal
    (ZF.v_ordinal_height_l hZF outer limit.1 hηX) rank
  have relative : Vr_d X η C := ⟨D,F,hD,hF,fun t _ => cert t⟩
  exact ⟨θ,X,R,c,K,η,C,regular,outer,code,source,hηX,hCX,relative,limit,
    source.source.rank_read_source_l hZF hCX relative limit hωC,hAC,reflect⟩

end YesMetaZFC.SetTheory.LargeCardinal
