import YesMetaZFC.SetTheory.LargeCardinal.ExtenderAlgebra
import YesMetaZFC.SetTheory.LargeCardinal.DerivedSeparation

/-! # 测度族算子与嵌入限制的精确识别

对任意有限列集合 A，实际算子满足 E(A)=j(A)∩L^{<ω}，不限于同一长度。
这是标准短扩展器的有限列表示；未把原嵌入作为算子的定义参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ex_derived_d (j S E : M.Domain) : Prop := ∀ A B, Rd_entry_d A B E →
  ∃ A', Rd_entry_d A A' j ∧ ∀ a, M.mem a B ↔ M.mem a S ∧ M.mem a A'

variable (hZF : M.Models ZF) {ω δ X C Y Q j κ k L S F : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
  (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y Q j) (hY : M.TransitiveSet Y)
  (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
  (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
  (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
include hZF hω hX hδ h hY hc hL hS hSY hF

theorem ex_value_trace_l {A A' B : M.Domain} (hjA : Rd_entry_d A A' j) (he : Ex_value_d F S A B) :
    ∀ a, M.mem a B ↔ M.mem a S ∧ M.mem a A' := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  intro a
  constructor
  · intro ha
    obtain ⟨haS, U, D, haU, hDU, hDA⟩ := (he a).mp ha
    obtain ⟨_, _, _, _, _, hu⟩ := (hF.2.2 a U).mp haU
    obtain ⟨_, D', hjD, haD⟩ := (hu D).mp hDU
    exact ⟨haS, (ed_subset_l I hZF hω h ht hY hjD hjA).mp hDA a haD⟩
  · rintro ⟨haS, haA⟩
    obtain ⟨n, hn, hna⟩ := (hS a).mp haS
    have ha := fn0_of_function_l (ZF.modelsKP hZF) hna
    obtain ⟨U, haU⟩ := (hF.2.1 a).mp haS
    obtain ⟨_, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
    have en := hm.domain_eq_l hZF.1 ha
    subst m
    have hnκ := hc.ordinal.transitive ω hωκ n hn
    have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hnκ)
      (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
    obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
    have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL (hSY a haS) ha
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
    let φ : Delta0UnarySchema 1 := { body := .mem .newest (.bound 1), delta0 := .mem _ _ }
    obtain ⟨T, _, spec, read⟩ := ed_separate_delta_l I hZF hω h ht hY hP (ht P (ZF.v_power_mem_l I hZF hX hδ hDX hP))
      hjD haD hU φ ⟨fun _ => A, fun _ => A⟩ ⟨fun _ => A', fun _ => A'⟩ (fun _ => hjA)
    simp only [φ, UnarySchema.denote, Formula.satisfies_mem_iff] at spec read
    exact (he a).mpr ⟨haS, U, T, haU, read.mpr haA, fun s hs => ((spec s).mp hs).2⟩

/-- 整张幂集算子等于原嵌入在有限支撑空间上的限制。 -/
theorem ex_derived_l {K E : M.Domain} (hK : Fseq_space_d I ω κ K) (he : Ex_operator_d K S F E) :
    Ex_derived_d j S E := by
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hKX := ZF.v_relations_mem_l I hZF hX hδ hc.source (T := K) (fun f hf p hp => by
    obtain ⟨n, hn, hfn⟩ := (hK f).mp hf
    obtain ⟨i, hi, x, hx, hp⟩ := (fn0_of_function_l (ZF.modelsKP hZF) hfn).1 p hp
    exact ⟨i, hc.ordinal.transitive ω hωκ i (hω.transitive hZF n hn i hi), x, hx, hp⟩)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  intro A B hab
  obtain ⟨sub, value⟩ := he.at_l hab
  obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (ZF.v_power_mem_l I hZF hX hδ hKX hP) A ((hP A).mpr sub))
  exact ⟨A', hjA, ex_value_trace_l hZF hω hX hδ h hY hc hL hS hSY hF hjA value⟩

end YesMetaZFC.SetTheory.LargeCardinal
