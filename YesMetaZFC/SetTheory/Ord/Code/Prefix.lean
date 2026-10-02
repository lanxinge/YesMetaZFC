import YesMetaZFC.SetTheory.Ord.Code.Fold
import YesMetaZFC.SetTheory.Ord.Code.Natural

/-! # 内部有限前缀的恢复与自然数编码界

归纳命题量化任意后续内容，故剥去末项后可直接复用同一输入图；不必为每个
前缀重新建立一套递归。归纳性质均由实际原公式分离。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Oc_prefix_d (n F : M.Domain) : Prop := M.IsSetFunction I F ∧
  ∀ i, M.mem i n → ∃ a, M.IsOrdinal a ∧ M.PairMember I i a F

def oc_prefix_m {d} (n F : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 F)
  (Formula.forallMem n (.existsE (.conj (Formula.isOrdinal .newest)
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken))))
derive_free_closed oc_prefix_m

theorem oc_prefix_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n F : Term d) :
    Formula.satisfies ρ (oc_prefix_m (𝒞 := 𝒞) n F) ↔ Oc_prefix_d I (n.eval ρ) (F.eval ρ) := by
  simp only [oc_prefix_m, Oc_prefix_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem Oc_prefix_d.mono_l {n s F} (h : Oc_prefix_d I s F) (hn : M.MemberSubset n s) : Oc_prefix_d I n F :=
  ⟨h.1, fun i hi => h.2 i (hn i hi)⟩

/-- 同长前缀的折叠值相等时，原输入逐项相等，包括非标准有限前缀。 -/
theorem oc_fold_injective_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) :
    ∀ n, M.mem n ω → ∀ F G c, Oc_prefix_d I n F → Oc_prefix_d I n G →
      Oc_fold_d I F n c → Oc_fold_d I G n c →
        ∀ i, M.mem i n → ∀ a, M.PairMember I i a F ↔ M.PairMember I i a G := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  let φ : UnarySchema 0 := {
    body := .forallE (.forallE (.forallE
      (.imp (oc_prefix_m (𝒞 := 𝒞) (.bound 3) (.bound 2))
        (.imp (oc_prefix_m (𝒞 := 𝒞) (.bound 3) (.bound 1))
          (.imp (oc_fold_m (𝒞 := 𝒞) (.bound 2) (.bound 3) .newest)
            (.imp (oc_fold_m (𝒞 := 𝒞) (.bound 1) (.bound 3) .newest)
              (Formula.forallMem (.bound 3) (.forallE (.iff
                (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
                (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))))))))))) }
  have sat n : φ.denote ρ n ↔ ∀ F G c, Oc_prefix_d I n F → Oc_prefix_d I n G →
      Oc_fold_d I F n c → Oc_fold_d I G n c →
        ∀ i, M.mem i n → ∀ a, M.PairMember I i a F ↔ M.PairMember I i a G := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      oc_prefix_sat_l I hZF.1, oc_fold_sat_l I hZF.1, Formula.satisfies_forallMem_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  apply hω.induction (fun n => ∀ F G c, Oc_prefix_d I n F → Oc_prefix_d I n G →
    Oc_fold_d I F n c → Oc_fold_d I G n c →
      ∀ i, M.mem i n → ∀ a, M.PairMember I i a F ↔ M.PairMember I i a G)
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => sat n)⟩
  · exact fun e he _ _ _ _ _ _ _ i hi _ => (he i hi).elim
  · intro n _ ih s hs F G c hf hg hc hd
    obtain ⟨a, ha, hfa⟩ := hf.2 n hs.predecessor_mem
    obtain ⟨b, hb, hgb⟩ := hg.2 n hs.predecessor_mem
    obtain ⟨u, hu, huc⟩ := oc_fold_succ_l I hZF hf.1 hs ha hfa hc
    obtain ⟨v, hv, hvc⟩ := oc_fold_succ_l I hZF hg.1 hs hb hgb hd
    obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF huc hvc
    have sub : M.MemberSubset n s := fun i hi => (hs i).mpr (Or.inl hi)
    have same := ih F G u (hf.mono_l I sub) (hg.mono_l I sub) hu hv
    intro i hi z
    rcases (hs i).mp hi with hin | he
    · exact same i hin z
    · have eq := hZF.1.eq_of_same_members i n he; subst i
      exact ⟨fun hz => (hf.1.2 n z a hz hfa).symm ▸ hgb,
        fun hz => (hg.1.2 n z a hz hgb).symm ▸ hfa⟩

theorem oc_fold_natural_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) :
    ∀ n, M.mem n ω → ∀ F c, Oc_prefix_d I n F →
      (∀ i, M.mem i n → ∀ a, M.PairMember I i a F → M.mem a ω) →
        Oc_fold_d I F n c → M.mem c ω := by
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := {
    body := .forallE (.forallE (.imp (oc_prefix_m (𝒞 := 𝒞) (.bound 2) (.bound 1))
      (.imp (Formula.forallMem (.bound 2) (.forallE (.imp
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3)) (.mem .newest (.bound 5)))))
        (.imp (oc_fold_m (𝒞 := 𝒞) (.bound 1) (.bound 2) .newest) (.mem .newest (.bound 3)))))) }
  have sat n : φ.denote ρ n ↔ ∀ F c, Oc_prefix_d I n F →
      (∀ i, M.mem i n → ∀ a, M.PairMember I i a F → M.mem a ω) →
        Oc_fold_d I F n c → M.mem c ω := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      oc_prefix_sat_l I hZF.1, oc_fold_sat_l I hZF.1, Formula.satisfies_forallMem_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
    rfl
  apply hω.induction (fun n => ∀ F c, Oc_prefix_d I n F →
    (∀ i, M.mem i n → ∀ a, M.PairMember I i a F → M.mem a ω) → Oc_fold_d I F n c → M.mem c ω)
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => sat n)⟩
  · intro e he F c _ _ hc
    obtain ⟨z, hz, hzω⟩ := hω.1.1
    exact (hZF.1.eq_of_same_members c z (fun x => iff_of_false (oc_fold_zero_l I he hc x) (hz x))).symm ▸ hzω
  · intro n _ ih s hs F c hf hv hc
    obtain ⟨a, ha, hfa⟩ := hf.2 n hs.predecessor_mem
    obtain ⟨b, hb, hbc⟩ := oc_fold_succ_l I hZF hf.1 hs ha hfa hc
    have sub : M.MemberSubset n s := fun i hi => (hs i).mpr (Or.inl hi)
    exact oc_pair_natural_l I hZF hω (ih F b (hf.mono_l I sub) (fun i hi => hv i (sub i hi)) hb)
      (hv n hs.predecessor_mem a hfa) hbc

end YesMetaZFC.SetTheory
