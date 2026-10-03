import YesMetaZFC.SetTheory.Descriptive.Borel.HierarchyRules
import YesMetaZFC.SetTheory.Descriptive.Borel.Rules

/-! # Borel 树全部节点的实际解释集合

一次分离和替代给出整树的解释函数，因而可数并处不需要可数选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bn_d (B T R N F a K : M.Domain) : Prop := ∀ x, M.mem x K ↔
  M.mem x B ∧ ∃ V, Bsem_d I T R N F x V ∧ M.mem a V
def bn_m {d} (B T R N F a K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (.existsE (.conj
    (bsem_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken (.bound 1) .newest)
    (.mem a.weaken.weaken .newest)))))
derive_free_closed bn_m
theorem bn_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B T R N F a K : Term d) :
    Formula.satisfies ρ (bn_m (𝒞 := 𝒞) B T R N F a K) ↔
      Bn_d I (B.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (a.eval ρ) (K.eval ρ) := by
  simp only [bn_m, Bn_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    bsem_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bn_graph_l (hZF : M.Models ZF) (B T R N F : M.Domain) :
    ∃ P G, M.IsPowerSetOf P B ∧ M.IsSetFunctionFromTo I G T P ∧
      ∀ a K, M.PairMember I a K G → Bn_d I B T R N F a K := by
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push T).push R).push N).push F
  let φ : BinarySchema 5 := { body := bn_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have ep a K : φ.denote ρ a K ↔ Bn_d I B T R N F a K := bn_sat_l I hZF.1 _ _ _ _ _ _ _ _
  have total a : ∃ K, Bn_d I B T R N F a K := by
    let ψ : UnarySchema 6 := { body := .existsE (.conj
      (bsem_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (.mem (.bound 2) .newest)) }
    obtain ⟨K, hk⟩ := ZF.separation_exists_d hZF ψ (ρ.push a) B
    refine ⟨K, fun x => ?_⟩
    simpa only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      bsem_sat_l I hZF.1, Formula.satisfies_mem_iff] using! hk x
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := P)
    (fun a _ => (total a).imp fun K hk => (ep a K).mpr hk)
    (fun a _ K L hk hl => hZF.1.eq_of_same_members K L (fun x => ((ep a K).mp hk x).trans ((ep a L).mp hl x).symm))
    (fun a K _ hk => (hp K).mpr (fun x hx => (((ep a K).mp hk x).mp hx).1))
  exact ⟨P, G, hp, hg, fun a K hk => (ep a K).mp ((eg a K).mp hk).2⟩

theorem bn_mem_l (hZF : M.Models ZF) {B T R N F a K x V} (hw : Wf_rel_d T R)
    (h : Bn_d I B T R N F a K) (hv : Bsem_d I T R N F x V) : M.mem x K ↔ M.mem x B ∧ M.mem a V := by
  obtain ⟨W, _, unique⟩ := bsem_exists_unique_l I hZF hw N F x
  exact (h x).trans (and_congr_right fun _ => ⟨fun ⟨U, hu, ha⟩ => ((unique U hu).trans (unique V hv).symm) ▸ ha,
    fun ha => ⟨V, hv, ha⟩⟩)

theorem bn_leaf_l (hZF : M.Models ZF) {ω A S B T R N F a s K} (ht : Btree_d I ω A S T R N F)
    (hs : M.PairMember I a s F) (hk : Bn_d I B T R N F a K) : Cyl_d B s K := by
  intro x
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
  exact (bn_mem_l I hZF ht.wf hk hv).trans (and_congr_right fun _ =>
    bsem_leaf_l I hv ht.leaf_fn (ht.leaf a s hs).1 (ht.leaf a s hs).2.2.1 hs)

theorem bn_neg_l (hZF : M.Models ZF) {ω A S B T R N F a b K L} (ht : Btree_d I ω A S T R N F)
    (hn : M.mem a N) (hb : M.mem b T) (hba : Rd_entry_d b a R)
    (hu : ∀ c, M.mem c T → Rd_entry_d c a R → c = b)
    (hk : Bn_d I B T R N F a K) (hl : Bn_d I B T R N F b L) : Cm_d B L K := by
  intro x
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
  have no : ¬ ∃ s, M.PairMember I a s F := fun ⟨s, hs⟩ => (ht.leaf a s hs).2.2.1 hn
  refine (bn_mem_l I hZF ht.wf hk hv).trans (and_congr_right fun hx => ?_)
  exact (bsem_neg_l I hv (ht.neg_sub a hn) hn no hb hba hu).trans
    (not_congr ((bn_mem_l I hZF ht.wf hl hv).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).symm

/-- 把子节点的解释函数按一个已有的自然数单射重新索引。 -/
theorem bn_union_family_l (hZF : M.Models ZF) {ω A S B T R N F a K P G}
    (ht : Btree_d I ω A S T R N F) (hc : M.CardinalLessOrEqual I T ω)
    (hg : M.IsSetFunctionFromTo I G T P)
    (eg : ∀ b C, M.PairMember I b C G → Bn_d I B T R N F b C)
    (ha : M.mem a T) (hn : ¬ M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F)
    (hk : Bn_d I B T R N F a K) :
    ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H →
      ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b C G := by
  obtain ⟨E, he⟩ := hc
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 5 := ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push R).push a).push E).push G
  let φ : BinarySchema 5 := { body := .existsE (.conj (.mem .newest (.bound 7)) (.conj
    (rd_entry_m .newest (.bound 5) (.bound 6)) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))))) }
  have ep i C : φ.denote ρ i C ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b i E ∧ M.PairMember I b C G := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry_sat_l hZF.1, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨H, hh, eh⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i C : M.PairMember I i C H ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b i E ∧ M.PairMember I b C G := by
    refine ((eh i C).trans (and_congr_right fun _ => and_congr_right fun _ => ep i C)).trans ⟨fun h => h.2.2, ?_⟩
    intro h
    obtain ⟨b, hb, hba, hbi, hbC⟩ := h
    exact ⟨(hw i).mpr (Or.inl (he.1.output_mem_of_pairMember hbi)), (hw C).mpr (Or.inr (hg.output_mem_of_pairMember hbC)), b, hb, hba, hbi, hbC⟩
  refine ⟨H, ⟨⟨hh.1, ?_⟩, ?_, ?_⟩, fun i C h => (pair i C).mp h |>.elim fun b h => ⟨b, h.1, h.2.1, h.2.2.2⟩⟩
  · intro i C D hc hd
    obtain ⟨b, _, _, hbi, hbC⟩ := (pair i C).mp hc
    obtain ⟨c, _, _, hci, hcD⟩ := (pair i D).mp hd
    exact hg.1.2 b C D hbC (he.2 c b i hci hbi ▸ hcD)
  · intro i C h
    obtain ⟨_, _, _, hbi, _⟩ := (pair i C).mp h
    exact he.1.output_mem_of_pairMember hbi
  · intro x
    obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
    constructor
    · intro hx
      obtain ⟨hxB, hav⟩ := (bn_mem_l I hZF ht.wf hk hv).mp hx
      obtain ⟨b, hb, hba, hbV⟩ := (bsem_union_l I hv ha hn hf).mp hav
      obtain ⟨C, _, hbC⟩ := hg.2.2 b hb
      obtain ⟨i, _, hbi⟩ := he.1.2.2 b hb
      exact ⟨i, C, (pair i C).mpr ⟨b, hb, hba, hbi, hbC⟩, (bn_mem_l I hZF ht.wf (eg b C hbC) hv).mpr ⟨hxB, hbV⟩⟩
    · rintro ⟨i, C, hc, hx⟩
      obtain ⟨b, hb, hba, _, hbC⟩ := (pair i C).mp hc
      obtain ⟨hxB, hbV⟩ := (bn_mem_l I hZF ht.wf (eg b C hbC) hv).mp hx
      exact (bn_mem_l I hZF ht.wf hk hv).mpr ⟨hxB, (bsem_union_l I hv ha hn hf).mpr ⟨b, hb, hba, hbV⟩⟩

end YesMetaZFC.SetTheory.Descriptive
