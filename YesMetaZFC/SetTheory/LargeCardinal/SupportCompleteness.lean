import YesMetaZFC.SetTheory.LargeCardinal.FiniteSupport

/-! # 有限支撑测度族自身的共同纤维条件

条件只读取实际测度函数 F，不把派生它的嵌入作为完备性参数。
第 n 个前缀所对应的测度包含第 n 层，恰好等价于像层具有共同纤维。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_fiber_d (ω L F H f : M.Domain) : Prop := Fn0_d ω L f ∧ ∀ n, M.mem n ω →
  ∃ A a U, Rd_entry_d n A H ∧ Fn0_d n L a ∧ M.MemberSubset a f ∧ M.PairMember I a U F ∧ M.mem A U

def es_fiber_m {d} (ω L F H f : Term d) : Formula 1 d := .conj (fn0_m ω L f)
  (Formula.forallMem ω (.existsE (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken) (.conj
      (fn0_m (.bound 3) L.weaken.weaken.weaken.weaken (.bound 1)) (.conj
        (Formula.subset (.bound 1) f.weaken.weaken.weaken.weaken) (.conj
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))))))
derive_free_closed es_fiber_m

theorem es_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L F H f : Term d) :
    Formula.satisfies ρ (es_fiber_m (𝒞 := 𝒞) ω L F H f) ↔
      Es_fiber_d I (ω.eval ρ) (L.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [es_fiber_m, Es_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem es_fiber_iff_l (hKP : M.Models KP) {j ω κ L S F H f}
    (hS : Fseq_space_d (kp_pair_l hKP) ω L S) (hF : Es_family_d I j κ L S F) (hH : Ef_levels_d ω κ H) :
    Es_fiber_d I ω L F H f ↔ Ef_image_fiber_d I j ω L H f := by
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun n hn => ?_⟩
    obtain ⟨A, a, U, hA, ha, haf, haU, hAU⟩ := h n hn
    obtain ⟨_, _, _, _, _, hU⟩ := (hF.2.2 a U).mp haU
    obtain ⟨_, A', hjA, haA⟩ := (hU A).mp hAU
    exact ⟨A, A', a, hA, hjA, haA, ha, haf⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun n hn => ?_⟩
    obtain ⟨A, A', a, hA, hjA, haA, ha, haf⟩ := h n hn
    obtain ⟨U, haU⟩ := (hF.2.1 a).mp ((hS a).mpr ⟨n, hn, fn0_function_l hKP ha⟩)
    obtain ⟨_, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
    have he := ha.domain_eq_l hKP.1 hm
    exact ⟨A, a, U, hA, ha, haf, haU, (hU A).mpr
      ⟨fun s hs => (hD s).mpr (he ▸ hH.2 n A hA s hs), A', hjA, haA⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
