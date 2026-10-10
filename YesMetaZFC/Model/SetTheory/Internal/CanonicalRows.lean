import YesMetaZFC.Model.SetTheory.Internal.FormulaCode
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
  obtain ⟨t, ht⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF i hi) (hω.members_areOrdinals hZF j hj)
  obtain ⟨z, hz⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF k hk) (oc_pair_types_l I hZF ht).2.2
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
      (hω.transitive hZF n hf.1 i hi) (hf.2.2 i c hic))
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
