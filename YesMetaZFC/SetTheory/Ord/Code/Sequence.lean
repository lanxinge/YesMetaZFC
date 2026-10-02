import YesMetaZFC.SetTheory.Ord.Code.Prefix
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion

/-! # 全部内部有限序数列的规范编码

编码为〈长度，折叠值〉的规范序数配对。长度参与编码，故空列、重复项及不同
长度都能唯一恢复；自然数列的代码仍是自然数。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Oc_seq_d (ω F c : M.Domain) : Prop := ∃ n b, M.mem n ω ∧ M.IsOrdinalValuedSequence I F n ∧
  Oc_fold_d I F n b ∧ Oc_pair_d I n b c

def oc_seq_m {d} (ω F c : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (.mem (.bound 1) ω.weaken.weaken)
    (.conj (Formula.isOrdinalValuedSequence 𝒞 F.weaken.weaken (.bound 1))
      (.conj (oc_fold_m (𝒞 := 𝒞) F.weaken.weaken (.bound 1) .newest)
        (oc_pair_m (𝒞 := 𝒞) (.bound 1) .newest c.weaken.weaken)))))
derive_free_closed oc_seq_m

theorem oc_seq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F c : Term d) :
    Formula.satisfies ρ (oc_seq_m (𝒞 := 𝒞) ω F c) ↔ Oc_seq_d I (ω.eval ρ) (F.eval ρ) (c.eval ρ) := by
  simp only [oc_seq_m, Oc_seq_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isOrdinalValuedSequence_iff I hE,
    oc_fold_sat_l I hE, oc_pair_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem oc_seq_prefix_l {F n} (h : M.IsOrdinalValuedSequence I F n) : Oc_prefix_d I n F := by
  refine ⟨h.1.2.1, fun i hi => ?_⟩
  obtain ⟨a, ha⟩ := (h.1.2.2 i).mp hi
  exact ⟨a, h.2 i hi a ha, ha⟩

theorem oc_seq_exists_l (hZF : M.Models ZF) {ω F n} (hn : M.mem n ω)
    (hf : M.IsOrdinalValuedSequence I F n) : ∃ c, Oc_seq_d I ω F c := by
  obtain ⟨b, hb⟩ := oc_fold_exists_l I hZF hf.1.2.1 hf.1.1
  obtain ⟨c, hc⟩ := oc_pair_exists_l I hZF hf.1.1 (oc_fold_ordinal_l I hZF hb)
  exact ⟨c, n, b, hn, hf, hb, hc⟩

theorem oc_seq_unique_l (hZF : M.Models ZF) {ω F c d} (h : Oc_seq_d I ω F c) (g : Oc_seq_d I ω F d) : c = d := by
  obtain ⟨n, b, _, hf, hb, hc⟩ := h
  obtain ⟨m, a, _, hg, ha, hd⟩ := g
  have eq := hf.1.length_eq hZF.1 hg.1; subst m
  have eq := oc_fold_unique_l I hZF hf.1.2.1 hb ha; subst a
  exact oc_pair_unique_l I hZF hc hd

theorem oc_seq_injective_l (hZF : M.Models ZF) {ω F G c} (hω : M.IsOmega ω)
    (h : Oc_seq_d I ω F c) (g : Oc_seq_d I ω G c) : F = G := by
  obtain ⟨n, b, hn, hf, hb, hc⟩ := h
  obtain ⟨m, a, _, hg, ha, hd⟩ := g
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF hc hd
  have same := oc_fold_injective_l I hZF hω n hn F G b (oc_seq_prefix_l I hf) (oc_seq_prefix_l I hg) hb ha
  exact hf.1.2.1.1.eq_of_pairMember_iff hZF.1 hg.1.2.1.1 (fun i z =>
    ⟨fun h => (same i ((hf.1.2.2 i).mpr ⟨z, h⟩) z).mp h,
      fun h => (same i ((hg.1.2.2 i).mpr ⟨z, h⟩) z).mpr h⟩)

theorem oc_seq_ordinal_l (hZF : M.Models ZF) {ω F c} (h : Oc_seq_d I ω F c) : M.IsOrdinal c := by
  obtain ⟨_, _, _, _, _, hc⟩ := h
  exact (oc_pair_types_l I hZF hc).2.2

theorem oc_seq_natural_l (hZF : M.Models ZF) {ω F n c} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I F n ω) (h : Oc_seq_d I ω F c) : M.mem c ω := by
  obtain ⟨m, b, hm, hg, hb, hc⟩ := h
  have hbω := oc_fold_natural_l I hZF hω m hm F b (oc_seq_prefix_l I hg)
    (fun _ _ _ h => hf.output_mem_of_pairMember h) hb
  exact oc_pair_natural_l I hZF hω hm hbω hc

/-- 空参数列以内部零编码，供零参数定义直接调用。 -/
theorem oc_seq_empty_l (hZF : M.Models ZF) {ω e} (he : ∀ z, ¬ M.mem z e) (heω : M.mem e ω) : Oc_seq_d I ω e e := by
  have hs := Structure.IsSequenceOfLength.empty I he
  obtain ⟨b, hb⟩ := oc_fold_exists_l I hZF hs.2.1 hs.1
  have eq := hZF.1.eq_of_same_members b e (fun z => iff_of_false (oc_fold_zero_l I he hb z) (he z))
  subst b
  exact ⟨e, e, heω, ⟨hs, fun i hi => (he i hi).elim⟩, hb, oc_pair_zero_l I hZF he⟩

/-- 序数 α 的全部有限列，具有同一原公式定义的实际编码与逆解码表。 -/
theorem oc_seq_tables_l (hZF : M.Models ZF) {ω a S} (hω : M.IsOmega ω) (ha : M.IsOrdinal a)
    (hS : Fseq_space_d I ω a S) : ∃ C E D,
      (∀ c, M.mem c C → M.IsOrdinal c) ∧ M.IsSetBijectionFromTo I E S C ∧ M.IsSetBijectionFromTo I D C S ∧
      (∀ F c, M.PairMember I F c E ↔ M.mem F S ∧ Oc_seq_d I ω F c) ∧
      (∀ c F, M.PairMember I c F D ↔ M.mem F S ∧ Oc_seq_d I ω F c) := by
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : BinarySchema 1 := { body := oc_seq_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  have sat F c : φ.denote ρ F c ↔ Oc_seq_d I ω F c := oc_seq_sat_l I hZF.1 _ _ _ _
  have total F (hF : M.mem F S) : ∃ c, φ.denote ρ F c := by
    obtain ⟨n, hn, hf⟩ := (hS F).mp hF
    obtain ⟨c, hc⟩ := oc_seq_exists_l I hZF hn
      ⟨⟨hω.members_areOrdinals hZF n hn, hf.1, hf.2.1⟩, fun _ _ _ hz => ha.mem (hf.output_mem_of_pairMember hz)⟩
    exact ⟨c, (sat F c).mpr hc⟩
  have unique F (_ : M.mem F S) c d (hc : φ.denote ρ F c) (hd : φ.denote ρ F d) : c = d :=
    oc_seq_unique_l I hZF ((sat F c).mp hc) ((sat F d).mp hd)
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ S total unique
  obtain ⟨E, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun F c hF hc => (hC c).mpr ⟨F, hF, hc⟩)
  have bij : M.IsSetBijectionFromTo I E S C := by
    refine ⟨⟨hf, fun F G c h g => oc_seq_injective_l I hZF hω
      ((sat F c).mp ((he F c).mp h).2) ((sat G c).mp ((he G c).mp g).2)⟩, fun c hc => ?_⟩
    obtain ⟨F, hF, hc⟩ := (hC c).mp hc
    exact ⟨F, hF, (he F c).mpr ⟨hF, hc⟩⟩
  obtain ⟨D, hd, inv⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have code F c := (he F c).trans (and_congr_right fun _ => sat F c)
  exact ⟨C, E, D, fun c hc => (hC c).mp hc |>.elim fun F h => oc_seq_ordinal_l I hZF ((sat F c).mp h.2),
    bij, hd, code, fun c F => (inv c F).trans (code F c)⟩

end YesMetaZFC.SetTheory
