import YesMetaZFC.SetTheory.Descriptive.Borel.Code
import YesMetaZFC.SetTheory.Collapse.RelationRank

/-! # Borel 码树的内部序数秩

Brank 是整棵码树上的实际秩函数；Bcr 是其根值，叶和空并的树秩为零。
这是具体语法码的高度，不将它混同于取遍等价表示后的集合层级秩。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Brank_d (ω A S c H : M.Domain) : Prop := ∃ T R N F,
  Bpack_d I c T R N F ∧ Btree_d I ω A S T R N F ∧ Wr_d I T R H
def brank_m {d} (ω A S c H : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest) (.conj
  (btree_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken S.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (wr_m (𝒞 := 𝒞) (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken))))))
derive_free_closed brank_m
theorem brank_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c H : Term d) :
    Formula.satisfies ρ (brank_m (𝒞 := 𝒞) ω A S c H) ↔
      Brank_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (H.eval ρ) := by
  simp only [brank_m, Brank_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, wr_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem brank_unique_l (hZF : M.Models ZF) {ω A S c H G}
    (h : Brank_d I ω A S c H) (k : Brank_d I ω A S c G) : H = G := by
  obtain ⟨T, R, N, F, hp, ht, hr⟩ := h
  obtain ⟨T', R', N', F', hq, _, hs⟩ := k
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hq
  exact wr_unique_l I hZF ht.wf hr hs
theorem brank_exists_l (hZF : M.Models ZF) {ω A S c} (hc : Bcode_d I ω A S c) :
    ∃ H, Brank_d I ω A S c H := by
  obtain ⟨T, R, N, F, hp, ht⟩ := hc
  obtain ⟨_, H, _, _, _, hr⟩ := wr_exists_l I hZF ht.wf
  exact ⟨H, T, R, N, F, hp, ht, hr⟩

def Bcr_d (ω A S c α : M.Domain) : Prop := ∃ H z,
  Brank_d I ω A S c H ∧ (∀ p, ¬ M.mem p z) ∧ M.PairMember I z α H
def bcr_m {d} (ω A S c α : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (brank_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken S.weaken.weaken c.weaken.weaken (.bound 1)) (.conj
  (Formula.isEmpty .newest) (Formula.orderedPairMem 𝒞 .newest α.weaken.weaken (.bound 1)))))
derive_free_closed bcr_m
theorem bcr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c α : Term d) :
    Formula.satisfies ρ (bcr_m (𝒞 := 𝒞) ω A S c α) ↔
      Bcr_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (α.eval ρ) := by
  simp only [bcr_m, Bcr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, brank_sat_l I hE,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl
theorem bcr_unique_l (hZF : M.Models ZF) {ω A S c α β} (h : Bcr_d I ω A S c α) (k : Bcr_d I ω A S c β) : α = β := by
  obtain ⟨H, z, hh, hz, ha⟩ := h
  obtain ⟨G, w, hg, hw, hb⟩ := k
  have e := brank_unique_l I hZF hg hh
  subst G
  have e := hZF.1.eq_of_same_members w z (fun p => iff_of_false (hw p) (hz p))
  subst w
  obtain ⟨_, _, _, _, _, _, hr⟩ := hh
  exact hr.1.2 z α β ha hb

/-- 根秩实际存在、唯一且内部可数，整树也有一个共同的可数秩界。 -/
theorem bcr_exists_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (ha : M.CardinalLessOrEqual I A ω) (hc : Bcode_d I ω A S c) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bcr_d I ω A S c α := by
  obtain ⟨T, R, N, F, hp, ht⟩ := hc
  obtain ⟨E, he⟩ := ha
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I ht.tree.1
  obtain ⟨β, H, hb, count, hh, hr⟩ := wr_countable_l I hZF hω ht.wf (ZF.exists_compositionInjection hZF I hd he)
  obtain ⟨z, hz, hzT⟩ := ht.root
  obtain ⟨α, hα, hza⟩ := hh.2.2 z hzT
  obtain ⟨V, hv⟩ := ZF.exists_inclusionInjection hZF I (hb.transitive.memberSubset hα)
  obtain ⟨W, hw⟩ := count
  exact ⟨α, hb.mem hα, ZF.exists_compositionInjection hZF I hv hw, H, z, ⟨T, R, N, F, hp, ht, hr⟩, hz, hza⟩

/-- 节点秩满足通常的 sup(子秩+1) 方程，而非任意下降标号。 -/
theorem brank_equation_l {ω A S c H T R N F a α} (h : Brank_d I ω A S c H)
    (hp : Bpack_d I c T R N F) (ha : M.PairMember I a α H) : M.IsOrdinal α ∧ ∀ β, M.mem β α ↔
      ∃ b γ, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b γ H ∧ (β = γ ∨ M.mem β γ) := by
  obtain ⟨T', R', N', F', hq, _, hr⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hq
  exact hr.2.2 a α ha

end YesMetaZFC.SetTheory.Descriptive
