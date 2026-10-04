import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBounded
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRestriction
import YesMetaZFC.SetTheory.LargeCardinal.JointFiber

/-! # 通用短扩展器的有限列接口

预扩展器由实际测度图及其代数、坐标、正规性和临界点性质刻画；可数共同
纤维另列为扩展器条件。全部后续运算读取 F，不以原嵌入为参数。
采用有限列表示，与 Neeman 的有限列集合算子约定相配。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ex_pre_d (hZF : M.Models ZF) (ω κ L F : M.Domain) : Prop where
  omega : M.IsOmega ω
  critical : M.IsCardinal (kp_pair_l (ZF.modelsKP hZF)) κ
  uncountable : M.mem ω κ
  length : M.IsOrdinal L
  above : M.mem κ L
  graph : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) F
  measures : Em_family_d ω κ L F
  coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F
  complete : ∀ n a U D, Fn0_d n L a → Rd_entry_d a U F →
    (∀ s, M.mem s D ↔ Fn0_d n κ s) → Ed_complete_d κ D U
  atoms : Ea_atoms_d ω κ L F
  normal : En_normal_d ω κ L F
  principal : ∀ n a U, M.mem n ω → Fn0_d n κ a → Rd_entry_d a U F →
    ∀ A, M.mem A U ↔ (∀ s, M.mem s A → Fn0_d n κ s) ∧ M.mem a A
  nonprincipal : ∀ a U i α, Rd_entry_d a U F → Rd_entry_d i α a → ¬ M.mem α κ → Ed_nonprincipal_d U

structure Ex_short_d (hZF : M.Models ZF) (ω κ L F : M.Domain) : Prop
    extends Ex_pre_d hZF ω κ L F where
  countable : ∀ H f, Ef_levels_d ω κ H →
    Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f → ∃ g, Ef_fiber_d ω κ H g

/-- 实际强嵌入生成全部预扩展器性质，特别是正规性和真正的临界基数。 -/
theorem es_pre_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X C Y E j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.IsOrdinal L) (hκL : M.mem κ L)
    (hLk : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F) :
    Ex_pre_d hZF ω κ L F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  obtain ⟨U, hU, hu, hn⟩ := ed_critical_measure_l I hZF hω h ht hY hc (hLk κ hκL) hP
    (ZF.v_power_mem_l I hZF hX hδ hc.source hP)
  have hcard := ed_cardinal_l I hZF hc.ordinal hu hn
    (ed_complete_l I hZF hω h hY hX hδ hc hc.image (hLk κ hκL) hU)
  refine ⟨hω, hcard, hωκ, hL, hκL, hF.1, es_measures_l hZF hω hX hδ h hY hc hLk hS hSY hF,
    es_coherent_l I hZF hω hX hδ h hY hc hLk hSY hF, ?_,
    es_atoms_l hZF hω hX hδ h hY hc hLk hSY hF,
    es_normal_l hZF hω hX hδ h hY hc hL hLk hS hSY hF,
    fun n a U hn ha hu => es_principal_l hZF hω hX hδ h hY hc hF (hc.ordinal.transitive ω hωκ n hn) ha hu,
    fun a U i α hu hi hα => es_nonprincipal_l hZF hω hX hδ h hY hc hF hu hi hα hS⟩
  intro n a U D ha hu hd
  obtain ⟨m, D', hm, hD', _, _, complete⟩ := es_family_ultra_l I hZF hω hX hδ h hY hc hLk hS hSY hF hu
  have en := hm.domain_eq_l hZF.1 ha
  subst m
  exact hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hd s).symm) ▸ complete

/-- 算子表述的可数完备性：像层有共同纤维，则原层也有共同纤维。 -/
theorem ex_countable_l (hZF : M.Models ZF) {ω κ L F K S E H f : M.Domain}
    (h : Ex_short_d hZF ω κ L F) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (he : Ex_operator_d K S F E) (hH : Ef_levels_d ω κ H)
    (hf : Ef_image_fiber_d (kp_pair_l (ZF.modelsKP hZF)) E ω L H f) : ∃ g, Ef_fiber_d ω κ H g := by
  apply h.countable H f hH
  refine ⟨hf.1, fun n hn => ?_⟩
  obtain ⟨A, B, a, hA, hab, haB, ha, sub⟩ := hf.2 n hn
  obtain ⟨U, haU⟩ := h.measures.total n a hn ha
  have haS := (hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩
  exact ⟨A, a, U, hA, ha, sub, haU, (ex_value_at_l hZF.1 h.measures haS ha haU (hH.2 n A hA) (he.at_l hab).2).mp haB⟩

end YesMetaZFC.SetTheory.LargeCardinal
