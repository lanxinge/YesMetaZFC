import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Classes

/-! # 约化幂的实际内部结构码

在全部等价类组成的集合上分离商关系，并证明它可用任意代表元读取。
源关系与函数值域可以位于任意秩，不要求派生测度的原嵌入作用于这些函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Rp_model_d (D Q U R c G p C T : M.Domain) : Prop where
  map : Rp_map_d I D Q U G p C
  code : Smdl_d I c C T
  relation : ∀ f g B E, M.PairMember I f B p → M.PairMember I g E p →
    (M.PairMember I B E T ↔ Rp_rel_d I Q U R f g)

def rp_model_m {d} (D Q U R c G p C T : Term d) : Formula 1 d := .conj (rp_map_m (𝒞 := 𝒞) D Q U G p C)
  (.conj (smdl_m (𝒞 := 𝒞) c C T) (.forallE (.forallE (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) p.weaken.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest p.weaken.weaken.weaken.weaken)
        (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest T.weaken.weaken.weaken.weaken)
          (rp_rel_m (𝒞 := 𝒞) Q.weaken.weaken.weaken.weaken U.weaken.weaken.weaken.weaken
            R.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))))))))))
derive_free_closed rp_model_m

theorem rp_model_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D Q U R c G p C T : Term d) :
    Formula.satisfies ρ (rp_model_m (𝒞 := 𝒞) D Q U R c G p C T) ↔
      Rp_model_d I (D.eval ρ) (Q.eval ρ) (U.eval ρ) (R.eval ρ) (c.eval ρ) (G.eval ρ) (p.eval ρ) (C.eval ρ) (T.eval ρ) := by
  simp only [rp_model_m, Formula.satisfies_conj_iff, rp_map_sat_l I hE, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, rp_rel_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.map, h.code, h.relation⟩⟩

theorem rp_model_exists_l (hZF : M.Models ZF) {D Q U G} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hG : ∀ f, M.mem f G → Fn0_d D Q f) (h : ∃ f, M.mem f G) (R : M.Domain) :
    ∃ c p C T, Rp_model_d I D Q U R c G p C T := by
  obtain ⟨p, C, hp⟩ := rp_map_exists_l I hZF hG
  obtain ⟨f, hfG⟩ := h
  obtain ⟨B, hBC, _⟩ := hp.projection.2.2 f hfG
  let ρ : Env M 5 := ⟨Fin.cases p (Fin.cases G (Fin.cases Q (Fin.cases U (fun _ => R)))), fun _ => Q⟩
  let φ : BinarySchema 5 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 4)) (.conj
      (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))
      (rp_rel_m (𝒞 := 𝒞) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest)))) }
  have sat B E : φ.denote ρ B E ↔ ∃ f, M.mem f G ∧ ∃ g, M.mem g G ∧
      M.PairMember I f B p ∧ M.PairMember I g E p ∧ Rp_rel_d I Q U R f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rp_rel_sat_l I hZF.1]
    rfl
  obtain ⟨c, T, hc, ht⟩ := smdl_exists_l I hZF φ ρ ⟨B, hBC⟩
  refine ⟨c, p, C, T, ⟨hp, hc, fun f g B E hf hg => (ht B E).trans ?_⟩⟩
  rw [sat B E]
  constructor
  · rintro ⟨_, _, f', hfG, g', hgG, hf', hg', hfg⟩
    exact rp_rel_transport_l I hU (hp.functions f' hfG) (hp.functions g' hgG)
      ((rp_kernel_l I hZF.1 hU hp hf' hf).mp rfl) ((rp_kernel_l I hZF.1 hU hp hg' hg).mp rfl) hfg
  · intro hfg
    exact ⟨hp.projection.output_mem_of_pairMember hf, hp.projection.output_mem_of_pairMember hg,
      f, hp.projection.input_mem_of_pairMember hf, g, hp.projection.input_mem_of_pairMember hg, hf, hg, hfg⟩

/-- 指定候选函数集合后，实际分离全部合法代表并形成商结构。 -/
theorem rp_family_model_l (hZF : M.Models ZF) {D Q U B f} (hU : FilterZF.Base_d (ℳ := M) D U)
    (hfB : M.mem f B) (hf : Fn0_d D Q f) (R : M.Domain) : ∃ G c p C T,
      (∀ g, M.mem g G ↔ M.mem g B ∧ Fn0_d D Q g) ∧ Rp_model_d I D Q U R c G p C T := by
  obtain ⟨G, hG⟩ := rp_family_exists_l (ZF.modelsKP hZF) D Q B
  obtain ⟨c, p, C, T, h⟩ := rp_model_exists_l I hZF hU (fun g hg => ((hG g).mp hg).2)
    ⟨f, (hG f).mpr ⟨hfB, hf⟩⟩ R
  exact ⟨G, c, p, C, T, hG, h⟩

end YesMetaZFC.SetTheory.Internal
