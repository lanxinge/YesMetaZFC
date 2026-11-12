import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.Ord.Code.Sequence

/-! # 现有内部指令的规范自然数编码

保留原指令与程序图，按固定的两次序数配对给〈操作符，左参数，右参数〉编号。
逐行转换是模型内部唯一函数图，并可从转换后的程序恢复全部原指令。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_node_d (c z : M.Domain) : Prop := ∃ k p i j t,
  I.Codes c k p ∧ I.Codes p i j ∧ Oc_pair_d I i j t ∧ Oc_pair_d I k t z

def sc_node_m {d} (c z : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (𝒞.code c.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3))
    (.conj (𝒞.code (.bound 3) (.bound 2) (.bound 1))
      (.conj (oc_pair_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest)
        (oc_pair_m (𝒞 := 𝒞) (.bound 4) .newest z.weaken.weaken.weaken.weaken.weaken))))))))
derive_free_closed sc_node_m

theorem sc_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (c z : Term d) :
    Formula.satisfies ρ (sc_node_m (𝒞 := 𝒞) c z) ↔ Sc_node_d I (c.eval ρ) (z.eval ρ) := by
  simp only [sc_node_m, Sc_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, oc_pair_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sc_node_unique_l (hZF : M.Models ZF) {c z w} (h : Sc_node_d I c z) (g : Sc_node_d I c w) : z = w := by
  obtain ⟨k, p, i, j, t, hc, hp, ht, hz⟩ := h
  obtain ⟨l, q, a, b, s, hc', hq, hs, hw⟩ := g
  obtain ⟨rfl, rfl⟩ := I.injective hc hc'
  obtain ⟨rfl, rfl⟩ := I.injective hp hq
  have eq := oc_pair_unique_l I hZF ht hs; subst s
  exact oc_pair_unique_l I hZF hz hw

theorem sc_node_injective_l (hZF : M.Models ZF) {c d z} (h : Sc_node_d I c z) (g : Sc_node_d I d z) : c = d := by
  obtain ⟨k, p, i, j, t, hc, hp, ht, hz⟩ := h
  obtain ⟨l, q, a, b, s, hd, hq, hs, hw⟩ := g
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF hz hw
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF ht hs
  have eq := I.unique hp hq; subst q
  exact I.unique hc hd

theorem sc_node_exists_l (hZF : M.Models ZF) {ω P Q c} (hω : M.IsOmega ω)
    (hP : M.IsCartesianProduct I P ω ω) (hQ : M.IsCartesianProduct I Q ω P) (hc : M.mem c Q) :
    ∃ z, M.mem z ω ∧ Sc_node_d I c z := by
  obtain ⟨k, hk, p, hp, hc⟩ := (hQ c).mp hc
  obtain ⟨i, hi, j, hj, hp⟩ := (hP p).mp hp
  obtain ⟨t, ht⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals (ZF.modelsKP hZF) i hi) (hω.members_areOrdinals (ZF.modelsKP hZF) j hj)
  obtain ⟨z, hz⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals (ZF.modelsKP hZF) k hk) (oc_pair_types_l I hZF ht).2.2
  exact ⟨z, oc_pair_natural_l I hZF hω hk (oc_pair_natural_l I hZF hω hi hj ht) hz,
    k, p, i, j, t, hc, hp, ht, hz⟩

def Sc_rows_d (ω n F G : M.Domain) : Prop := M.IsSetFunctionFromTo I G n ω ∧
  ∀ i z, M.PairMember I i z G ↔ M.mem i n ∧ ∃ c, M.PairMember I i c F ∧ Sc_node_d I c z

def sc_rows_m {d} (ω n F G : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 G n ω)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
    (.conj (.mem (.bound 1) n.weaken.weaken) (.existsE
      (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest F.weaken.weaken.weaken)
        (sc_node_m (𝒞 := 𝒞) .newest (.bound 1))))))))
derive_free_closed sc_rows_m

theorem sc_rows_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n F G : Term d) :
    Formula.satisfies ρ (sc_rows_m (𝒞 := 𝒞) ω n F G) ↔ Sc_rows_d I (ω.eval ρ) (n.eval ρ) (F.eval ρ) (G.eval ρ) := by
  simp only [sc_rows_m, Sc_rows_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, sc_node_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sc_rows_exists_l (hZF : M.Models ZF) {ω n F} (hω : M.IsOmega ω) (hf : Sfm_d I ω n F) :
    ∃ G, Sc_rows_d I ω n F G := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω P
  have total i (hi : M.mem i n) c (hic : M.PairMember I i c F) : ∃ z, M.mem z ω ∧ Sc_node_d I c z :=
    sc_node_exists_l I hZF hω hP hQ (sfm_node_mem_l I hZF hω hP hQ
      (hω.transitive (ZF.modelsKP hZF) n hf.1 i hi) (hf.2.2 i c hic))
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (sc_node_m (𝒞 := 𝒞) .newest (.bound 1))) }
  have sat i z : φ.denote ρ i z ↔ ∃ c, M.PairMember I i c F ∧ Sc_node_d I c z := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, sc_node_sat_l I hZF.1]
    rfl
  obtain ⟨G, hg, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := ω) (by
    intro i hi
    obtain ⟨c, hic⟩ := (hf.2.1.2.2 i).mp hi
    obtain ⟨z, _, hz⟩ := total i hi c hic
    exact ⟨z, (sat i z).mpr ⟨c, hic, hz⟩⟩) (by
      intro i _ z w hz hw
      obtain ⟨c, hc, hz⟩ := (sat i z).mp hz
      obtain ⟨d, hd, hw⟩ := (sat i w).mp hw
      have eq := hf.2.1.2.1.2 i c d hc hd; subst d
      exact sc_node_unique_l I hZF hz hw) (by
        intro i z hi hz
        obtain ⟨c, hc, hz⟩ := (sat i z).mp hz
        obtain ⟨w, hw, hc'⟩ := total i hi c hc
        exact (sc_node_unique_l I hZF hz hc').symm ▸ hw)
  exact ⟨G, hg, fun i z => (he i z).trans (and_congr_right fun _ => sat i z)⟩

theorem Sc_rows_d.unique_l (hE : Extensional M) {ω n F G H}
    (h : Sc_rows_d I ω n F G) (g : Sc_rows_d I ω n F H) : G = H :=
  h.1.1.1.eq_of_pairMember_iff hE g.1.1.1 (fun i z => (h.2 i z).trans (g.2 i z).symm)

theorem Sc_rows_d.source_unique_l (hZF : M.Models ZF) {ω n m F H G}
    (hf : M.IsSequenceOfLength I F n) (hh : M.IsSequenceOfLength I H m)
    (h : Sc_rows_d I ω n F G) (g : Sc_rows_d I ω m H G) : F = H := by
  have eq := h.1.2.1.eq hZF.1 g.1.2.1; subst m
  have transfer {F H : M.Domain} (hf : M.IsSequenceOfLength I F n)
      (h : Sc_rows_d I ω n F G) (g : Sc_rows_d I ω n H G) {i c} (hic : M.PairMember I i c F) : M.PairMember I i c H := by
    have hi := (hf.2.2 i).mpr ⟨c, hic⟩
    obtain ⟨z, _, hz⟩ := h.1.2.2 i hi
    obtain ⟨_, c', hic', hc⟩ := (h.2 i z).mp hz
    have eq := hf.2.1.2 i c c' hic hic'; subst c'
    obtain ⟨_, d, hid, hd⟩ := (g.2 i z).mp hz
    exact (sc_node_injective_l I hZF hc hd).symm ▸ hid
  exact hf.2.1.1.eq_of_pairMember_iff hZF.1 hh.2.1.1 (fun _ _ => ⟨transfer hf h g, transfer hh g h⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 全部内部公式的规范自然数码与双向编码表

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
      fun _ _ z hz => hω.members_areOrdinals (ZF.modelsKP hZF) z (hg.1.output_mem_of_pairMember hz)⟩
  obtain ⟨c, hc⟩ := oc_seq_exists_l I hZF h.2.1.1 ho
  obtain ⟨z, hz⟩ := oc_pair_exists_l I hZF (oc_seq_ordinal_l I hZF hc) (h.2.1.2.1.1.mem h.2.2)
  exact ⟨z, n, F, k, G, c, h, hg, hc, hz⟩

theorem sc_num_natural_l (hZF : M.Models ZF) {ω a z} (hω : M.IsOmega ω) (h : Sc_num_d I ω a z) : M.mem z ω := by
  obtain ⟨n, F, k, G, c, hf, hg, hc, hz⟩ := h
  exact oc_pair_natural_l I hZF hω (oc_seq_natural_l I hZF hω hg.1 hc)
    (hω.transitive (ZF.modelsKP hZF) n hf.2.1.1 k hf.2.2) hz

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
