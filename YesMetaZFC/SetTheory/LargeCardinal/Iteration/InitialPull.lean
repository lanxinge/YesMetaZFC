import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Reflection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Coherence
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence

/-! # 下降历史的实际模型行及全前驱公式

历史行只记录模型、嵌入图及可数编号；原树的模型码和支撑图作为固定参数。
所有前驱一致性都由同一个公式检查，不对宿主自然数作任何有限性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def pn_rank_m {d} (X α V : Term d) : Formula 1 d := set[d] ⟪
  ∃ B ∈ ⌜X⌝ₛ, ∃ F ∈ ⌜X⌝ₛ, ∀ t ∈ ⌜X⌝ₛ, ⌜vc_matrix_m⌝ₚ(⌜α⌝ₛ, ⌜V⌝ₛ, B, F, t)⟫
derive_free_closed pn_rank_m

theorem pn_rank_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X α V : Term d) :
    Formula.satisfies ρ (pn_rank_m X α V) ↔ Vr_d (X.eval ρ) (α.eval ρ) (V.eval ρ) := by
  simp only [pn_rank_m, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    vc_matrix_sat_l hKP, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨B, hB, F, hF, h⟩ => ⟨B, F, hB, hF, h⟩,
    fun ⟨B, F, hB, hF, h⟩ => ⟨B, hB, F, hF, h⟩⟩

def pn_agree_m {d} (X Y π N Z σ ρ φ : Term d) : Formula 1 d := set[d] ⟪
  Trans(⌜X⌝ₛ) ∧ Trans(⌜Y⌝ₛ) ∧ Trans(⌜N⌝ₛ) ∧ Trans(⌜Z⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜ρ⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜φ⌝ₛ) ∧
  (∃ W ∈ ⌜X⌝ₛ, W ∈ ⌜N⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, ⌜ρ⌝ₛ, W) ∧ ⌜pn_rank_m⌝ₚ(⌜N⌝ₛ, ⌜ρ⌝ₛ, W) ∧
    (∀ x ∈ W, ∀ y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜π⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(x, y, ⌜σ⌝ₛ))) ∧
  (∃ V ∈ ⌜Y⌝ₛ, V ∈ ⌜Z⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜φ⌝ₛ, V) ∧ ⌜pn_rank_m⌝ₚ(⌜Z⌝ₛ, ⌜φ⌝ₛ, V)) ∧
  ⌜rd_entry0_m⌝ₚ(⌜ρ⌝ₛ, ⌜φ⌝ₛ, ⌜π⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜ρ⌝ₛ, ⌜φ⌝ₛ, ⌜σ⌝ₛ)⟫
derive_free_closed pn_agree_m

theorem pn_agree_sat_l (hKP : M.Models KP) {d} (η : Env M d) (X Y π N Z σ ρ φ : Term d) :
    Formula.satisfies η (pn_agree_m X Y π N Z σ ρ φ) ↔
      Pn_agree_d (X.eval η) (Y.eval η) (π.eval η) (N.eval η) (Z.eval η) (σ.eval η) (ρ.eval η) (φ.eval η) := by
  simp only [pn_agree_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hKP.1, pn_rank_sat_l hKP, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨a, b, c, d, l, m, ⟨W, wx, wn, w, w', p⟩, q, r, s⟩
    exact ⟨a, b, c, d, l, m, ⟨W, wx, wn, w, w', fun x y hx => p x hx y⟩, q, r, s⟩
  · intro h
    obtain ⟨W, wx, wn, w, w', p⟩ := h.source_rank
    exact ⟨h.source_left, h.target_left, h.source_right, h.target_right, h.source_limit, h.target_limit,
      ⟨W, wx, wn, w, w', fun x hx y => p x y hx⟩, h.target_rank, h.left_end, h.right_end⟩

def Pn_row_d (ω a X P π ι : M.Domain) : Prop := M.TransitiveSet X ∧ ∃ R S c μ K,
  Smem_d I a X R ∧ Smem_d I c P S ∧ Pn_model_d hZF ω μ K P S ∧ M.mem π P ∧ M.mem ι P ∧
    Smap_d I ω a c X P π ∧ M.IsSetInjectionFromTo I ι π ω

def pn_row_m {d} (ω a X P π ι : Term d) : Formula 1 d := set[d] ⟪
  Trans(⌜X⌝ₛ) ∧ (∃ R S c μ K, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, ⌜X⌝ₛ, R) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜P⌝ₛ, S) ∧ ⌜pn_model_m⌝ₚ(⌜ω⌝ₛ, μ, K, ⌜P⌝ₛ, S) ∧
    ⌜π⌝ₛ ∈ ⌜P⌝ₛ ∧ ⌜ι⌝ₛ ∈ ⌜P⌝ₛ ∧ ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, c, ⌜X⌝ₛ, ⌜P⌝ₛ, ⌜π⌝ₛ) ∧
    ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜ι⌝ₛ, ⌜π⌝ₛ, ⌜ω⌝ₛ))⟫
derive_free_closed pn_row_m

theorem pn_row_sat_l {d} (ρ : Env M d) (ω a X P π ι : Term d) : Formula.satisfies ρ (pn_row_m ω a X P π ι) ↔
    Pn_row_d hZF (ω.eval ρ) (a.eval ρ) (X.eval ρ) (P.eval ρ) (π.eval ρ) (ι.eval ρ) := by
  simp only [pn_row_m, Pn_row_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, smem_sat_l I, pn_model_sat_l hZF, Formula.satisfies_mem_iff, smap_sat_l I hZF.1,
    Formula.satisfies_isInjectionFromTo_iff I hZF.1, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 下降递归的初始行

可数传递定义域先由实际遗传大小界进入正规秩层。函数值的秩由正则性统一
控制，所以给定初等图及其可数编号都在同一初始模型内。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_initial_row_l {ω β P a X R b S π η : M.Domain}
    (hω : M.IsOmega ω) (above : M.mem ω β) (regular : M.IsRegularCardinal I β)
    (rank : V_d I β P) (hX : M.TransitiveSet X) (hm : Smem_d I a X R) (hn : Smem_d I b P S)
    (embed : Smap_d I ω a b X P π) (countable : M.IsSetInjectionFromTo I η X ω) :
    ∃ ι, Pn_row_d hZF ω a X P π ι := by
  obtain ⟨K, S', model⟩ := pn_regular_model_l hZFC hω above regular rank
  obtain ⟨b', code⟩ := model.source.code
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 code hn
  obtain ⟨T, μ, tc, hμ, size⟩ := ZF.hmem_of_subset_l I hZF regular.isLimitOrdinal hX
    (fun _ h => h) above ⟨η, countable⟩
  have hXP := ZF.rk_transitive_bound_l I hZF tc.1 regular.isCardinal hμ size rank X tc.2.1
  obtain ⟨C, hC, fn, hπ⟩ := ZF.v_small_function_l hZF regular above ⟨η, countable⟩ hXP rank embed.1.1
  obtain ⟨U, hU, xu, wu⟩ := v_joint_bound_l I rank hXP model.source.omega_mem
  have hη : M.mem η P := v_relation_mem_l I rank regular.isLimitOrdinal hU (fun p hp => by
    obtain ⟨x, hx, i, hi, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) countable.1).1 p hp
    exact ⟨x, xu x hx, i, wu i hi, pair⟩)
  obtain ⟨ι, hι, index⟩ := sc_graph_numbering_l hZF hω model.source.transitive code model.source.theory
    model.source.omega_mem hXP hC hη hπ countable (fn0_of_function_l (ZF.modelsKP hZF) fn)
  exact ⟨ι, hX, R, S', b', ω, K, hm, code, model, hπ, hι, embed, index⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数壳的根秩段自动给出下降递归的初始行

大根秩段是真实正则 Vβ。外层嵌入在小秩段上的限制和实际可数编号，
直接满足原初始行构造的全部前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_initial_pull_l {ω B R b K U S u J π a d β V P : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K B R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (count : M.CardinalLessOrEqual I B ω) (had : Rd_entry_d a d π) (md : Smem_d I d V P)
    (above : M.mem ω β) (regular : M.IsRegularCardinal I β) (rank : V_d I β V) :
    ∃ X Q p ι, Smem_d I a X Q ∧ Rd_entry_d X V π ∧ M.IsRestrictionOf I p π X ∧ Pn_row_d hZF ω a X V p ι := by
  obtain ⟨L, seq⟩ := ZF.fseq_space_exists_l I hZF source.omega ω
  obtain ⟨P', child⟩ := ep_regular_source_l hZFC source.omega above regular rank above (fun _ h => h) seq
  obtain ⟨d', md'⟩ := child.code
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 md' md
  obtain ⟨X, Q, _, p, mx, sx, hXV, restriction, hp⟩ := ep_set_source_pull_l hZF source target mb mu hj had md child
  obtain ⟨η, inj⟩ := count
  obtain ⟨η', res⟩ := ZF.exists_restriction hZF I η X
  have index : M.IsSetInjectionFromTo I η' X ω :=
    ⟨res.isSetFunctionFromTo inj.1 (source.transitive X (hj.1.1.input_mem_of_pairMember hXV)),
      fun x y n hx hy => inj.2 x y n ((res.2 x n).mp hx).2 ((res.2 y n).mp hy).2⟩
  obtain ⟨ι, row⟩ := pn_initial_row_l hZFC source.omega above regular rank sx.transitive mx md hp index
  exact ⟨X, Q, p, ι, mx, hXV, restriction, row⟩

end YesMetaZFC.SetTheory.LargeCardinal
