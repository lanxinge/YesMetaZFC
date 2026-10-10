import YesMetaZFC.SetTheory.Descriptive.Borel.PullbackTree
import YesMetaZFC.SetTheory.Descriptive.Continuous

/-! # 连续逆像码的唯一原公式构造 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bplab_d (ω A E f F b t : M.Domain) : Prop := M.mem b A ∧ M.mem t A ∧ ∃ a s i,
  M.PairMember I a s F ∧ M.PairMember I t i E ∧ Cov_d I f s t ∧ Fseq_end_d I ω b a i
def bplab_m {d} (ω A E f F b t : Term d) : Formula 1 d := .conj (.mem b A) (.conj (.mem t A)
  (.existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 t.weaken.weaken.weaken .newest E.weaken.weaken.weaken) (.conj
      (cov_m (𝒞 := 𝒞) f.weaken.weaken.weaken (.bound 1) t.weaken.weaken.weaken)
      (fseq_end_m (𝒞 := 𝒞) ω.weaken.weaken.weaken b.weaken.weaken.weaken (.bound 2) .newest))))))))
derive_free_closed bplab_m
theorem bplab_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f F b t : Term d) :
    Formula.satisfies ρ (bplab_m (𝒞 := 𝒞) ω A E f F b t) ↔
      Bplab_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (F.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [bplab_m, Bplab_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, cov_sat_l I,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Bpex_d (ω A E f T F U Q G : M.Domain) : Prop :=
  (∀ a, M.mem a U ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s) ∧ Edge_d I ω U Q ∧
  M.IsSetRelation I G ∧ ∀ a s, M.PairMember I a s G ↔ Bplab_d I ω A E f F a s
def bpex_m {d} (ω A E f T F U Q G : Term d) : Formula 1 d := .conj
  (.forallE (.iff (.mem .newest U.weaken) (.disj (.mem .newest T.weaken) (.existsE
    (bplab_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken E.weaken.weaken f.weaken.weaken F.weaken.weaken (.bound 1) .newest)))))
  (.conj (edge_m (𝒞 := 𝒞) ω U Q) (.conj (Formula.isRelation 𝒞 G)
    (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
      (bplab_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken E.weaken.weaken f.weaken.weaken F.weaken.weaken (.bound 1) .newest))))))
derive_free_closed bpex_m
theorem bpex_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f T F U Q G : Term d) :
    Formula.satisfies ρ (bpex_m (𝒞 := 𝒞) ω A E f T F U Q G) ↔
      Bpex_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (T.eval ρ) (F.eval ρ) (U.eval ρ) (Q.eval ρ) (G.eval ρ) := by
  simp only [bpex_m, Bpex_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, bplab_sat_l I hE, edge_sat_l I hE,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem bpex_exists_l (hZF : M.Models ZF) {ω A E f T F} (hT : M.MemberSubset T A) :
    ∃ U Q G, Bpex_d I ω A E f T F U Q G := by
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push E).push f).push F
  let φ : BinarySchema 5 := { body := bplab_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp a s : φ.denote ρ a s ↔ Bplab_d I ω A E f F a s := bplab_sat_l I hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨G, hG, hg⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have labels a s : M.PairMember I a s G ↔ Bplab_d I ω A E f F a s :=
    ((hg a s).trans (and_congr_right fun _ => and_congr_right fun _ => hp a s)).trans
      ⟨fun h => h.2.2, fun h => ⟨h.1, h.2.1, h⟩⟩
  let η : Env M 2 := (⟨fun _ => T, fun _ => T⟩ : Env M 1).push G
  let ψ : UnarySchema 2 := {
    body := .disj (.mem .newest (.bound 2)) (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))) }
  obtain ⟨U, hU⟩ := ZF.separation_exists_d hZF ψ η A
  have nodes a : M.mem a U ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s := by
    have eqn : ψ.denote η a ↔ M.mem a T ∨ ∃ s, Bplab_d I ω A E f F a s := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
        Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]
      exact or_congr Iff.rfl (exists_congr fun s => labels a s)
    exact ((hU a).trans (and_congr_right fun _ => eqn)).trans
      ⟨And.right, fun h => ⟨h.elim (hT a) (fun ⟨_, h⟩ => h.1), h⟩⟩
  obtain ⟨Q, hQ⟩ := tree_edges_l I hZF ω U
  exact ⟨U, Q, G, nodes, hQ, hG.1, labels⟩

theorem bpex_blext_l (hE : Extensional M) {ω A E f T F U Q G}
    (he : M.IsSetInjectionFromTo I E A ω) (h : Bpex_d I ω A E f T F U Q G) :
    Blext_d I ω A A T F U Q G := by
  refine ⟨fun a => (h.1 a).trans (or_congr Iff.rfl (exists_congr fun s => (h.2.2.2 a s).symm)),
    h.2.1, ⟨h.2.2.1, ?_⟩, ?_, ?_⟩
  · intro b t u ht hu
    obtain ⟨_, _, a, s, i, _, hit, _, hb⟩ := (h.2.2.2 b t).mp ht
    obtain ⟨_, _, a', s', j, _, hiu, _, hb'⟩ := (h.2.2.2 b u).mp hu
    exact he.2 t u i hit ((fseq_end_unique_l I hE hb' hb).2 ▸ hiu)
  · intro b t ht
    have ht := (h.2.2.2 b t).mp ht
    exact ⟨ht.1, ht.2.1⟩
  · intro b t ht
    obtain ⟨_, _, a, s, i, ha, _, _, hb⟩ := (h.2.2.2 b t).mp ht
    exact ⟨a, s, ha, i, hb⟩

def Bpull_d (ω A E f c d : M.Domain) : Prop := ∃ T R N F U Q G,
  Bpack_d I c T R N F ∧ Bpack_d I d U Q N G ∧ Bpex_d I ω A E f T F U Q G
def bpull_m {d} (ω A E f c e : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3)) (.conj
    (bpack_m (𝒞 := 𝒞) e.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 4) .newest)
    (bpex_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      E.weaken.weaken.weaken.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 6) (.bound 3) (.bound 2) (.bound 1) .newest)))))))))
derive_free_closed bpull_m
theorem bpull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E f c e : Term d) :
    Formula.satisfies ρ (bpull_m (𝒞 := 𝒞) ω A E f c e) ↔
      Bpull_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (f.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [bpull_m, Bpull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, bpex_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bpull_unique_l (hE : Extensional M) {ω A E f c d e}
    (h : Bpull_d I ω A E f c d) (k : Bpull_d I ω A E f c e) : d = e := by
  obtain ⟨T, R, N, F, U, Q, G, hc, hd, h⟩ := h
  obtain ⟨T', R', N', F', U', Q', G', hc', he, k⟩ := k
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hc hc'
  have e := hE.eq_of_same_members U U' (fun a => (h.1 a).trans (k.1 a).symm)
  subst U'
  have e := tree_edges_unique_l I hE h.2.1 k.2.1
  subst Q'
  have e := h.2.2.1.eq_of_pairMember_iff hE k.2.2.1 (fun a s => (h.2.2.2 a s).trans (k.2.2.2 a s).symm)
  subst G'
  exact bpack_ext_l I hd he

theorem bpull_exists_l (hZF : M.Models ZF) {ω A E f c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hc : Bcode_d I ω A A c) :
    ∃ d, Bpull_d I ω A E f c d ∧ Bcode_d I ω A A d := by
  obtain ⟨T, R, N, F, hp, hc⟩ := hc
  obtain ⟨U, Q, G, h⟩ := bpex_exists_l I hZF (E := E) (f := f) (F := F) hc.tree.1
  obtain ⟨d, hd⟩ := bpack_exists_l I U Q N G
  exact ⟨d, ⟨T, R, N, F, U, Q, G, hp, hd, h⟩,
    U, Q, N, G, hd, blext_valid_l I hZF hω hA hc (bpex_blext_l I hZF.1 he h)⟩

end YesMetaZFC.SetTheory.Descriptive
