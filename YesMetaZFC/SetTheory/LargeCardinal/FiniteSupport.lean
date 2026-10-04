import YesMetaZFC.SetTheory.LargeCardinal.FiberCompleteness
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 全部有限支撑上的实际测度图

长度由支撑函数的定义域唯一确定。对 a:n→L，在 κ^n 上取种子 a 派生的测度；
全部分量同时收集成内部集合函数，不在元层逐个选择测度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_value_d (j κ L a U : M.Domain) : Prop := ∃ n D, Fn0_d n L a ∧
  (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧ Ed_filter_d I j a D U

def es_value_m {d} (j κ L a U : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (fn0_m (.bound 1) L.weaken.weaken a.weaken.weaken) (.conj
    (.forallE (.iff (.mem .newest (.bound 1)) (fn0_m (.bound 2) κ.weaken.weaken.weaken .newest)))
    (ed_filter_m (𝒞 := 𝒞) j.weaken.weaken a.weaken.weaken .newest U.weaken.weaken))))
derive_free_closed es_value_m

theorem es_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j κ L a U : Term d) :
    Formula.satisfies ρ (es_value_m (𝒞 := 𝒞) j κ L a U) ↔
      Es_value_d I (j.eval ρ) (κ.eval ρ) (L.eval ρ) (a.eval ρ) (U.eval ρ) := by
  simp only [es_value_m, Es_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    ed_filter_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem es_value_unique_l (hE : Extensional M) {j κ L a U V}
    (hU : Es_value_d I j κ L a U) (hV : Es_value_d I j κ L a V) : U = V := by
  obtain ⟨n, D, hn, hD, hU⟩ := hU
  obtain ⟨m, E, hm, hS, hV⟩ := hV
  have he := hn.domain_eq_l hE hm
  subst m
  have he := hE.eq_of_same_members D E (fun s => (hD s).trans (hS s).symm)
  subst E
  exact ed_filter_unique_l I hE hU hV

def Es_family_d (j κ L S F : M.Domain) : Prop := M.IsSetFunction I F ∧ M.IsDomainOf I S F ∧
  ∀ a U, M.PairMember I a U F ↔ M.mem a S ∧ Es_value_d I j κ L a U

def es_family_m {d} (j κ L S F : Term d) : Formula 1 d :=
  .conj (Formula.isFunction 𝒞 F) (.conj (Formula.isDomain 𝒞 S F) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken) (.conj (.mem (.bound 1) S.weaken.weaken)
      (es_value_m (𝒞 := 𝒞) j.weaken.weaken κ.weaken.weaken L.weaken.weaken (.bound 1) .newest))))))
derive_free_closed es_family_m

theorem es_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j κ L S F : Term d) :
    Formula.satisfies ρ (es_family_m (𝒞 := 𝒞) j κ L S F) ↔
      Es_family_d I (j.eval ρ) (κ.eval ρ) (L.eval ρ) (S.eval ρ) (F.eval ρ) := by
  simp only [es_family_m, Es_family_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, es_value_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem es_family_exists_l (hZF : M.Models ZF) {ω L S} (hω : M.IsOmega ω)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (j κ : M.Domain) :
    ∃ F, Es_family_d I j κ L S F := by
  let K := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨T, hT⟩ := ZF.fseq_space_exists_l K hZF hω κ
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF T
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 3 := ⟨Fin.cases L (Fin.cases κ (fun _ => j)), fun _ => κ⟩
  let φ : BinarySchema 3 := { body := es_value_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a U : φ.denote ρ a U ↔ Es_value_d I j κ L a U := es_value_sat_l I hZF.1 _ _ _ _ _ _
  obtain ⟨F, hf, hp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := S) (target := Q) (fun a ha => by
      obtain ⟨n, _, hn⟩ := (hS a).mp ha
      obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF K n κ
      obtain ⟨U, hU⟩ := ed_filter_exists_l I hZF j a D
      exact ⟨U, (sat a U).mpr ⟨n, D, fn0_of_function_l (ZF.modelsKP hZF) hn,
        fun s => (hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩, hU⟩⟩)
    (fun a _ U V hU hV => es_value_unique_l I hZF.1 ((sat a U).mp hU) ((sat a V).mp hV))
    (fun a U ha hU => by
      obtain ⟨m, hm, hma⟩ := (hS a).mp ha
      obtain ⟨n, D, hna, hD, hU⟩ := (sat a U).mp hU
      have he := hna.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
      apply (hQ U).mpr
      intro s hs
      exact (hP s).mpr fun b hb => (hT b).mpr ⟨n, he.symm ▸ hm,
        fn0_function_l (ZF.modelsKP hZF) ((hD b).mp (((hU s).mp hs).1 b hb))⟩)
  exact ⟨F, hf.1, hf.2.1, fun a U => (hp a U).trans (and_congr_right fun _ => sat a U)⟩

/-- j(κ^n) 对目标中的全部对象给出正确函数空间，而非仅对 j 的像成立。 -/
theorem es_seed_l (hZF : M.Models ZF) {ω X C Y E j n κ k D D' L a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hjn : M.PairMember I n n j) (hjκ : M.PairMember I κ k j) (hjD : M.PairMember I D D' j)
    (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) (hL : M.MemberSubset L k) (haY : M.mem a Y)
    (ha : Fn0_d n L a) : M.mem a D' := by
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest)
  have tr := spred_forall_delta_l I hZF hω h hX hY φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem _ _) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases k (fun _ => n)), fun _ => n⟩ (Fin.cases hjD (Fin.cases hjκ (fun _ => hjn)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  exact (tr.mp (fun s _ => hD s) a haY).mpr (ha.mono_target_l hL)

/-- 每个有限支撑分量都是其对应 κ^n 上的适当超滤。 -/
theorem es_family_ultra_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d I j κ L S F) {a U} (ha : M.PairMember I a U F) :
    ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
      Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U := by
  have ht := ZF.v_transitive_l I hZF hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨haS, n, D, hna, hD, hU⟩ := (hF.2.2 a U).mp ha
  obtain ⟨m, hm, hma⟩ := (hS a).mp haS
  have he := hna.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
  have hn : M.mem n ω := he.symm ▸ hm
  have hnκ := hc.ordinal.transitive ω hωκ n hn
  have hDn : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) D n κ := fun s =>
    (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩
  have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hnκ) hDn
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL (hSY a haS) hna
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨V, hV, hv⟩ := ed_ultrafilter_l I hZF hω h ht hY hP (ZF.v_power_mem_l I hZF hX hδ hDX hP) hjD haD
  exact ⟨n, D, hna, hD, hU, ed_filter_unique_l I hZF.1 hV hU ▸ hv,
    ed_complete_l I hZF hω h hY hX hδ hc hjD haD hU⟩

end YesMetaZFC.SetTheory.LargeCardinal
