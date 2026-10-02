import YesMetaZFC.Model.SetTheory.Internal.CanonicalRows

/-! # 全部内部公式的规范自然数码与双向编码表

先逐行编码原程序，再编码整列，最后配对程序码与根行号。定义中没有任选
编号图；同一原公式码在所有构造见证下都有同一自然数码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_num_d (ω a z : M.Domain) : Prop := ∃ n F k G c, Sformula_d I ω a n F k ∧
  Sc_rows_d I ω n F G ∧ Oc_seq_d I ω G c ∧ Oc_pair_d I c k z

def sc_num_m {d} (ω a z : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (sformula_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken a.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2))
    (.conj (sc_rows_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 1))
      (.conj (oc_seq_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest)
        (oc_pair_m (𝒞 := 𝒞) .newest (.bound 2) z.weaken.weaken.weaken.weaken.weaken))))))))
derive_free_closed sc_num_m

theorem sc_num_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω a z : Term d) :
    Formula.satisfies ρ (sc_num_m (𝒞 := 𝒞) ω a z) ↔ Sc_num_d I (ω.eval ρ) (a.eval ρ) (z.eval ρ) := by
  simp only [sc_num_m, Sc_num_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sformula_sat_l I hE, sc_rows_sat_l I hE, oc_seq_sat_l I hE, oc_pair_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sc_num_exists_l (hZF : M.Models ZF) {ω a n F k} (hω : M.IsOmega ω)
    (h : Sformula_d I ω a n F k) : ∃ z, Sc_num_d I ω a z := by
  obtain ⟨G, hg⟩ := sc_rows_exists_l I hZF hω h.2.1
  have ho : M.IsOrdinalValuedSequence I G n :=
    ⟨⟨h.2.1.2.1.1, hg.1.1, hg.1.2.1⟩,
      fun _ _ z hz => hω.members_areOrdinals hZF z (hg.1.output_mem_of_pairMember hz)⟩
  obtain ⟨c, hc⟩ := oc_seq_exists_l I hZF h.2.1.1 ho
  obtain ⟨z, hz⟩ := oc_pair_exists_l I hZF (oc_seq_ordinal_l I hZF hc) (h.2.1.2.1.1.mem h.2.2)
  exact ⟨z, n, F, k, G, c, h, hg, hc, hz⟩

theorem sc_num_natural_l (hZF : M.Models ZF) {ω a z} (hω : M.IsOmega ω) (h : Sc_num_d I ω a z) : M.mem z ω := by
  obtain ⟨n, F, k, G, c, hf, hg, hc, hz⟩ := h
  exact oc_pair_natural_l I hZF hω (oc_seq_natural_l I hZF hω hg.1 hc)
    (hω.transitive hZF n hf.2.1.1 k hf.2.2) hz

theorem sc_num_unique_l (hZF : M.Models ZF) {ω a z w} (h : Sc_num_d I ω a z) (g : Sc_num_d I ω a w) : z = w := by
  obtain ⟨n, F, k, G, c, hf, hg, hc, hz⟩ := h
  obtain ⟨m, H, j, K, d, hh, hk, hd, hw⟩ := g
  obtain ⟨rfl, rfl, rfl⟩ := sformula_unique_l I hZF.1 hf hh
  have eq := hg.unique_l I hZF.1 hk; subst K
  have eq := oc_seq_unique_l I hZF hc hd; subst d
  exact oc_pair_unique_l I hZF hz hw

theorem sc_num_injective_l (hZF : M.Models ZF) {ω a b z} (hω : M.IsOmega ω)
    (h : Sc_num_d I ω a z) (g : Sc_num_d I ω b z) : a = b := by
  obtain ⟨n, F, k, G, c, hf, hg, hc, hz⟩ := h
  obtain ⟨m, H, j, K, d, hh, hk, hd, hw⟩ := g
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF hz hw
  have eq := oc_seq_injective_l I hZF hω hc hd; subst K
  have eq := hg.source_unique_l I hZF hf.2.1.2.1 hh.2.1.2.1 hk; subst H
  exact I.unique hf.1 hh.1

/-- 自动构造全部原公式码、合法自然数码集、规范编码图及逆解码图。 -/
theorem sc_num_tables_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ C N E D,
    Scode_d I ω C ∧ M.MemberSubset N ω ∧ M.IsSetBijectionFromTo I E C N ∧ M.IsSetBijectionFromTo I D N C ∧
      (∀ a z, M.PairMember I a z E ↔ Sc_num_d I ω a z) ∧
      (∀ z a, M.PairMember I z a D ↔ Sc_num_d I ω a z) ∧
      (∀ z, M.mem z N ↔ ∃ a, Sc_num_d I ω a z) := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : BinarySchema 1 := { body := sc_num_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  have sat a z : φ.denote ρ a z ↔ Sc_num_d I ω a z := sc_num_sat_l I hZF.1 _ _ _ _
  have total a (ha : M.mem a C) : ∃ z, φ.denote ρ a z := by
    obtain ⟨n, F, k, ha⟩ := (hC a).mp ha
    exact (sc_num_exists_l I hZF hω ha).imp fun z hz => (sat a z).mpr hz
  have unique a (_ : M.mem a C) z w (hz : φ.denote ρ a z) (hw : φ.denote ρ a w) : z = w :=
    sc_num_unique_l I hZF ((sat a z).mp hz) ((sat a w).mp hw)
  have source {a z} (h : Sc_num_d I ω a z) : M.mem a C := by
    obtain ⟨n, F, k, _, _, h, _⟩ := h
    exact (hC a).mpr ⟨n, F, k, h⟩
  obtain ⟨N, hN⟩ := ZF.exists_functionalImageOn hZF φ ρ C total unique
  obtain ⟨E, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun a z ha hz => (hN z).mpr ⟨a, ha, hz⟩)
  have graph a z : M.PairMember I a z E ↔ Sc_num_d I ω a z :=
    (he a z).trans ⟨fun h => (sat a z).mp h.2, fun h => ⟨source h, (sat a z).mpr h⟩⟩
  have bij : M.IsSetBijectionFromTo I E C N := by
    refine ⟨⟨hf, fun a b z h g => sc_num_injective_l I hZF hω ((graph a z).mp h) ((graph b z).mp g)⟩,
      fun z hz => ?_⟩
    obtain ⟨a, ha, hz⟩ := (hN z).mp hz
    exact ⟨a, ha, (graph a z).mpr ((sat a z).mp hz)⟩
  obtain ⟨D, hd, inv⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  refine ⟨C, N, E, D, hC, fun z hz => ?_, bij, hd, graph, fun z a => (inv z a).trans (graph a z), ?_⟩
  · obtain ⟨a, _, hz⟩ := (hN z).mp hz
    exact sc_num_natural_l I hZF hω ((sat a z).mp hz)
  · intro z
    exact (hN z).trans ⟨fun ⟨a, _, h⟩ => ⟨a, (sat a z).mp h⟩,
      fun ⟨a, h⟩ => ⟨a, source h, (sat a z).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal
