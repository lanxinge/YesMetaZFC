import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded
import YesMetaZFC.Model.SetTheory.Internal.TypeRank
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph

/-! # 原类型查询域的有界识别

名字表逐项核验变量、指定常量和集合常量，并要求这些名字全部出现。
有限名字列空间由实际秩界回收，再用原 Kuratowski 乘积构造完整查询域。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tn_names0_m {d} (n U N : Term d) : Formula 1 d := set[d] ⟪
  (∀ a ∈ ⌜N⌝ₛ, ⌜tn_name_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, a)) ∧ ⌜n⌝ₛ ⊆ ⌜N⌝ₛ ∧ ⌜n⌝ₛ ∈ ⌜N⌝ₛ ∧
  (∀ x ∈ ⌜U⌝ₛ, ∃ a ∈ ⌜N⌝ₛ, ⌜kpair0_m⌝ₚ(a, x, x))⟫
derive_free_closed tn_names0_m

theorem tn_names0_delta_l {d} (n U N : Term d) : (tn_names0_m n U N).IsDelta0 :=
  .conj (.forallMem _ (tn_name_delta_l ..)) (.conj (.atom ..)
    (.conj (.mem ..) (.forallMem _ (.existsMem _ (kpair0_delta_l ..)))))

theorem tn_names0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (n U N : Term d) :
    Formula.satisfies ρ (tn_names0_m n U N) ↔ Tn_names_d (n.eval ρ) (U.eval ρ) (N.eval ρ) := by
  simp only [tn_names0_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff,
    tn_name_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨valid, vars, point, constants⟩ a
    refine ⟨valid a, ?_⟩
    rintro (hi | rfl | ⟨x, hx, pair⟩)
    · exact vars a hi
    · exact point
    · obtain ⟨b, hb, code⟩ := constants x hx
      exact kpair_unique_l M hKP.1 code pair ▸ hb
  · intro names
    refine ⟨fun a => (names a).mp, fun a ha => (names a).mpr (Or.inl ha),
      (names (n.eval ρ)).mpr (Or.inr (Or.inl rfl)), fun x hx => ?_⟩
    obtain ⟨a, pair⟩ := (kp_pair_l hKP).total x x
    exact ⟨a, (names a).mpr (Or.inr (Or.inr ⟨x, hx, pair⟩)), pair⟩

def tt_pool0_m {d} (ω X n U D : Term d) : Formula 1 d := set[d] ⟪∃ N ∈ ⌜X⌝ₛ, ∃ E ∈ ⌜X⌝ₛ,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, N, E) ∧
  ⌜rd_graph_m .prod⌝ₚ(⌜ω⌝ₛ, E, ⌜ω⌝ₛ, ⌜D⌝ₛ)⟫
derive_free_closed tt_pool0_m

theorem tt_pool0_delta_l {d} (ω X n U D : Term d) : (tt_pool0_m ω X n U D).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (tn_names0_delta_l ..) (.conj (fs_space0_delta_l ..) (rd_graph_delta_l ..))))

theorem tt_pool0_rank_l (hZF : M.Models ZF) {d δ} (ρ : Env M d) (ω X n U D : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ (X.eval ρ))
    (hδ : M.IsLimitOrdinal δ) (hωX : M.mem (ω.eval ρ) (X.eval ρ))
    (hn : M.mem (n.eval ρ) (ω.eval ρ)) (hU : M.mem (U.eval ρ) (X.eval ρ)) :
    Formula.satisfies ρ (tt_pool0_m ω X n U D) ↔
      Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := ZF.v_transitive_l I hZF hX
  have product E : Rd_fun_d .prod (ω.eval ρ) E (ω.eval ρ) (D.eval ρ) ↔
      M.IsCartesianProduct I (D.eval ρ) (ω.eval ρ) E := by
    exact ⟨fun h p => (h p).trans ⟨fun ⟨a, b, ha, hb, pair⟩ => ⟨a, ha, b, hb, pair⟩,
      fun ⟨a, ha, b, hb, pair⟩ => ⟨a, b, ha, hb, pair⟩⟩,
      fun h p => (h p).trans ⟨fun ⟨a, ha, b, hb, pair⟩ => ⟨a, b, ha, hb, pair⟩,
        fun ⟨a, b, ha, hb, pair⟩ => ⟨a, ha, b, hb, pair⟩⟩⟩
  have spaces N E E₀ (seq : Fseq_space_d I (ω.eval ρ) N E₀) (hE : M.mem E₀ (X.eval ρ)) :
      Formula.satisfies ((ρ.push N).push E) (fs_space0_m ω.weaken.weaken X.weaken.weaken Term.newest.weaken .newest) ↔ E = E₀ := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := E₀) ((ρ.push N).push E)
        ω.weaken.weaken X.weaken.weaken Term.newest.weaken .newest
        (by simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
        (by simpa only [Definitional.Term.eval_weaken, Structure.MemberSubset] using trans E₀ hE)
  simp only [tt_pool0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l (ZF.modelsKP hZF), rd_graph_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, product]
  constructor
  · rintro ⟨N, hN, E, _, names, matrix, prod⟩
    obtain ⟨E₀, seq⟩ := ZF.fseq_space_exists_l I hZF hω N
    have hE₀ := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hN seq
    exact ⟨N, E, names, ((spaces N E E₀ seq hE₀).mp matrix).symm ▸ seq, prod⟩
  · rintro ⟨N, E, names, seq, prod⟩
    have hN := names.rank_mem_l hZF hω hX hδ hωX hn hU
    have hE := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hN seq
    exact ⟨N, hN, E, hE, names, (spaces N E E seq hE).mpr rfl, prod⟩

end YesMetaZFC.SetTheory.Internal
