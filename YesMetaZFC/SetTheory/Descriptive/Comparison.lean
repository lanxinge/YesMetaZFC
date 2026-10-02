import YesMetaZFC.SetTheory.Descriptive.Topology
import YesMetaZFC.SetTheory.Card.Arithmetic.PowerSet

/-! # Baire 与 Cantor 空间的具体比较

两空间使用同一内部 ω 和同一配对约定。Cantor 的拓扑正是 Baire 的子空间拓扑；
Cantor 在 Baire 中闭且无处稠密。其点集通过已有特征函数构造与内部幂集等势。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 一次取得两个空间、内部可数前缀集、完整拓扑及各自的开集判据。 -/
theorem baire_cantor_l (hZF : M.Models ZF) : ∃ ω D B C S T τ υ,
    Baire_d I ω B ∧ M.IsOrdinalTwo D ∧ M.IsFunctionSpace I C ω D ∧
    Fseq_space_d I ω ω S ∧ M.CardinalLessOrEqual I S ω ∧
    Fseq_space_d I ω D T ∧ M.CardinalLessOrEqual I T ω ∧
    Top_d B τ ∧ Top_d C υ ∧
    (∀ U, M.mem U τ ↔ Open_d S B U) ∧ (∀ U, M.mem U υ ↔ Open_d T C U) := by
  obtain ⟨ω, D, B, C, S, T, hB, hD, hC, hS, hs, hT, ht⟩ := ds_spaces_l I hZF
  obtain ⟨τ, hτ, hτ'⟩ := ds_topology_l I hZF hB.1 hB.2 hS
  obtain ⟨υ, hυ, hυ'⟩ := ds_topology_l I hZF hB.1 hC hT
  exact ⟨ω, D, B, C, S, T, τ, υ, hB, hD, hC, hS, hs, hT, ht, hτ, hυ, hτ', hυ'⟩

theorem cantor_nonempty_l (hZF : M.Models ZF) {ω C} (hC : Cantor_d I ω C) : ∃ f, M.mem f C := by
  obtain ⟨_, D, hD, hC⟩ := hC
  obtain ⟨a, ha⟩ := hD.nonempty
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
  exact ⟨f, (hC f).mpr hf⟩

theorem baire_nonempty_l (hZF : M.Models ZF) {ω B} (hB : Baire_d I ω B) : ∃ f, M.mem f B := by
  obtain ⟨a, _, ha⟩ := hB.1.1.1
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
  exact ⟨f, (hB.2 f).mpr hf⟩

/-- Cantor 空间的相对补可由非二元坐标的有限前缀见证。 -/
theorem cantor_closed_l (hZF : M.Models ZF) {ω B C S}
    (hB : Baire_d I ω B) (hC : Cantor_d I ω C) (hS : Fseq_space_d I ω ω S) :
    ∃ V, (∀ f, M.mem f V ↔ M.mem f B ∧ ¬ M.mem f C) ∧ Open_d S B V := by
  obtain ⟨_, D, _, hc⟩ := hC
  obtain ⟨V, hV⟩ := KP.difference_exists_d (ZF.modelsKP hZF) C B
  refine ⟨V, hV, fun f hf => ((hV f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hfB, hfC⟩ := (hV f).mp hf
  have hf := (hB.2 f).mp hfB
  have bad : ∃ i a, M.mem i ω ∧ M.PairMember I i a f ∧ ¬ M.mem a D := by
    apply Classical.byContradiction
    intro h
    apply hfC
    apply (hc f).mpr
    refine ⟨hf.1, hf.2.1, fun i hi => ?_⟩
    obtain ⟨a, _, ha⟩ := hf.2.2 i hi
    exact ⟨a, Classical.byContradiction (fun hn => h ⟨i, a, hi, ha, hn⟩), ha⟩
  obtain ⟨i, a, hi, hia, ha⟩ := bad
  obtain ⟨n, hni, hn⟩ := hB.1.1.2 i hi
  obtain ⟨s, hs, hsf, _⟩ := ds_prefix_l I hZF hB.1 hf hn
  refine ⟨s, (hS s).mpr ⟨n, hn, hs⟩, (ds_restrict_iff_l I hs hf.1).mp hsf, fun g hg hsg => ?_⟩
  apply (hV g).mpr
  refine ⟨hg, fun hgc => ?_⟩
  have hr := (ds_restrict_iff_l I hs ((hB.2 g).mp hg).1).mpr hsg
  exact ha (((hc g).mp hgc).output_mem_of_pairMember
    ((hr.2 i a).mp ((hsf.2 i a).mpr ⟨hni.predecessor_mem, hia⟩)).2)

/-- 每个非空 Baire 开集都有非二元点；结合闭性即 Cantor 的无处稠密性。 -/
theorem cantor_empty_interior_l (hZF : M.Models ZF) {ω B C S U}
    (hB : Baire_d I ω B) (hC : Cantor_d I ω C) (hS : Fseq_space_d I ω ω S)
    (hU : Open_d S B U) (hn : ∃ f, M.mem f U) : ∃ g, M.mem g U ∧ ¬ M.mem g C := by
  obtain ⟨hω, D, hD, hC⟩ := hC
  obtain ⟨f, hf⟩ := hn
  obtain ⟨s, hs, _, hu⟩ := hU.2 f hf
  obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
  obtain ⟨g, hg, hr, hng⟩ := ds_extend_l I hZF hω hn hsn (ds_two_mem_l hZF.1 hω hD)
  exact ⟨g, hu g ((hB.2 g).mpr hg) ((ds_restrict_iff_l I hsn hg.1).mp hr),
    fun hgc => KP.mem_irrefl_d (ZF.modelsKP hZF) D (((hC g).mp hgc).output_mem_of_pairMember hng)⟩

/-- 内部子字母表空间的开集恰为大空间开集的相对迹。 -/
theorem ds_subspace_l (hZF : M.Models ZF) {ω X Y B C S T V}
    (hω : M.IsOmega ω) (hXY : M.MemberSubset Y X)
    (hB : M.IsFunctionSpace I B ω X) (hC : M.IsFunctionSpace I C ω Y)
    (hS : Fseq_space_d I ω X S) (hT : Fseq_space_d I ω Y T) :
    Open_d T C V ↔ ∃ U, Open_d S B U ∧ ∀ f, M.mem f V ↔ M.mem f C ∧ M.mem f U := by
  have hCB := ds_space_mono_l I hXY hC hB
  constructor
  · intro hV
    let ρ : Env M 3 := ((⟨fun _ => T, fun _ => T⟩ : Env M 1).push C).push V
    let φ : UnarySchema 3 := {
      body := Formula.existsMem (.bound 3)
        (.conj (Formula.subset .newest (.bound 1)) (Formula.forallMem (.bound 3)
          (.imp (Formula.subset (.bound 1) .newest) (.mem .newest (.bound 3))))) }
    have hp f : φ.denote ρ f ↔ ∃ s, M.mem s T ∧ M.MemberSubset s f ∧
        ∀ g, M.mem g C → M.MemberSubset s g → M.mem g V := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_mem_iff]
      rfl
    obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF φ ρ B
    have hU f : M.mem f U ↔ M.mem f B ∧ ∃ s, M.mem s T ∧ M.MemberSubset s f ∧
        ∀ g, M.mem g C → M.MemberSubset s g → M.mem g V :=
      (hU' f).trans (and_congr_right fun _ => hp f)
    refine ⟨U, ⟨fun f hf => ((hU f).mp hf).1, fun f hf => ?_⟩, fun f => ?_⟩
    · obtain ⟨_, s, hs, hsf, hh⟩ := (hU f).mp hf
      exact ⟨s, ds_nodes_mono_l I hXY hT hS s hs, hsf, fun g hg hsg =>
        (hU g).mpr ⟨hg, s, hs, hsg, hh⟩⟩
    · exact ⟨fun hf => ⟨hV.1 f hf, (hU f).mpr ⟨hCB f (hV.1 f hf), hV.2 f hf⟩⟩,
        fun ⟨hf, hu⟩ => ((hU f).mp hu).2.elim fun s h => h.2.2 f hf h.2.1⟩
  · rintro ⟨U, hU, he⟩
    refine ⟨fun f hf => ((he f).mp hf).1, fun f hf => ?_⟩
    obtain ⟨hfC, hfU⟩ := (he f).mp hf
    obtain ⟨s, hs, hsf, hu⟩ := hU.2 f hfU
    obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
    have hr := (ds_restrict_iff_l I hsn ((hB f).mp (hCB f hfC)).1).mpr hsf
    have hsY := hr.isSetFunctionFromTo ((hC f).mp hfC) (hω.transitive hZF n hn)
    exact ⟨s, (hT s).mpr ⟨n, hn, hsY⟩, hsf, fun g hg hsg => (he g).mpr ⟨hg, hu g (hCB g hg) hsg⟩⟩

/-- 对实际二元字母表实例化子空间定理。 -/
theorem cantor_subspace_l (hZF : M.Models ZF) {ω D B C S T V}
    (hB : Baire_d I ω B) (hD : M.IsOrdinalTwo D) (hC : M.IsFunctionSpace I C ω D)
    (hS : Fseq_space_d I ω ω S) (hT : Fseq_space_d I ω D T) :
    Open_d T C V ↔ ∃ U, Open_d S B U ∧ ∀ f, M.mem f V ↔ M.mem f C ∧ M.mem f U :=
  ds_subspace_l I hZF hB.1 (hB.1.transitive hZF D (ds_two_mem_l hZF.1 hB.1 hD)) hB.2 hC hS hT

/-- Cantor 点集与内部自然数幂集的等势由实际特征函数双射给出。 -/
theorem cantor_power_l (hZF : M.Models ZF) {ω C P} (hC : Cantor_d I ω C)
    (hP : M.IsPowerSetOf P ω) : M.Equinumerous I P C := by
  obtain ⟨_, D, hD, hC⟩ := hC
  obtain ⟨z, o, hzo, hd⟩ := ds_two_l hZF.1 hD
  exact ZF.equinumerous_powerSet_functionSpace hZF I hP hd hzo hC

end YesMetaZFC.SetTheory.Descriptive
