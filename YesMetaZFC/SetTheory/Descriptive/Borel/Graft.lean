import YesMetaZFC.SetTheory.Descriptive.Borel.Rules
import YesMetaZFC.SetTheory.Descriptive.TreeTail

/-! # 可数码族的内部子树拼接

码族由以内部自然数为指标的部分函数图给出。每棵子树的地址加上指标作首项，
新根单独加入；节点、补标记和叶标签均由原公式分离形成实际集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bfam_d (ω A S H : M.Domain) : Prop := M.IsSetFunction I H ∧
  ∀ i c, M.PairMember I i c H → M.mem i ω ∧ Bcode_d I ω A S c
def bfam_m {d} (ω A S H : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H)
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
    (.conj (.mem (.bound 1) ω.weaken.weaken) (bcode_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken S.weaken.weaken .newest)))))
derive_free_closed bfam_m
theorem bfam_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S H : Term d) :
    Formula.satisfies ρ (bfam_m (𝒞 := 𝒞) ω A S H) ↔ Bfam_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (H.eval ρ) := by
  simp only [bfam_m, Bfam_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Bsub_d (H i T R N F : M.Domain) : Prop := ∃ c, M.PairMember I i c H ∧ Bpack_d I c T R N F
def bsub_m {d} (H i T R N F : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 i.weaken .newest H.weaken) (bpack_m (𝒞 := 𝒞) .newest T.weaken R.weaken N.weaken F.weaken))
derive_free_closed bsub_m
theorem bsub_sat_l {d} (ρ : Env M d) (H i T R N F : Term d) :
    Formula.satisfies ρ (bsub_m (𝒞 := 𝒞) H i T R N F) ↔
      Bsub_d I (H.eval ρ) (i.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bsub_m, Bsub_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, bpack_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem bsub_valid_l {ω A S H i T R N F} (hH : Bfam_d I ω A S H) (h : Bsub_d I H i T R N F) :
    M.mem i ω ∧ Btree_d I ω A S T R N F := by
  obtain ⟨c, hi, hp⟩ := h
  obtain ⟨hiω, T', R', N', F', hp', hc⟩ := hH.2 i c hi
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hp'
  exact ⟨hiω, hc⟩

theorem bsub_unique_l {H i T R N F T' R' N' F'} (hH : M.IsSetFunction I H)
    (h : Bsub_d I H i T R N F) (k : Bsub_d I H i T' R' N' F') :
    T = T' ∧ R = R' ∧ N = N' ∧ F = F' := by
  obtain ⟨c, hi, hp⟩ := h
  obtain ⟨c', hi', hp'⟩ := k
  exact bpack_unique_l I hp (hH.2 i c' c hi' hi ▸ hp')

def Bshift_d (z H t s N F : M.Domain) : Prop := ∃ i T R,
  Bsub_d I H i T R N F ∧ M.mem s T ∧ Cons_d I z i s t
def bshift_m {d} (z H t s N F : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (bsub_m (𝒞 := 𝒞) H.weaken.weaken.weaken (.bound 2) (.bound 1) .newest N.weaken.weaken.weaken F.weaken.weaken.weaken)
  (.conj (.mem s.weaken.weaken.weaken (.bound 1))
    (cons_m (𝒞 := 𝒞) z.weaken.weaken.weaken (.bound 2) s.weaken.weaken.weaken t.weaken.weaken.weaken)))))
derive_free_closed bshift_m
theorem bshift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t s N F : Term d) :
    Formula.satisfies ρ (bshift_m (𝒞 := 𝒞) z H t s N F) ↔
      Bshift_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) (s.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bshift_m, Bshift_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsub_sat_l I, Formula.satisfies_mem_iff, cons_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bshift_type_l (hZF : M.Models ZF) {ω A S z H t s N F} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H)
    (h : Bshift_d I z H t s N F) : M.mem t A ∧ t ≠ z := by
  obtain ⟨i, T, R, hc, hs, ht⟩ := h
  obtain ⟨hi, hc⟩ := bsub_valid_l I hH hc
  obtain ⟨n, hn, hs⟩ := (hA s).mp (hc.tree.1 s hs)
  obtain ⟨k, hk, _, ht'⟩ := cons_type_l I hZF hω hz hi hn hs ht
  exact ⟨(hA t).mpr ⟨k, hk, ht'⟩, cons_ne_empty_l I hz ht⟩

theorem bshift_unique_l (hZF : M.Models ZF) {ω A S z H t s N F s' N' F'} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H)
    (h : Bshift_d I z H t s N F) (k : Bshift_d I z H t s' N' F') : s = s' ∧ N = N' ∧ F = F' := by
  obtain ⟨i, T, R, hc, hs, ht⟩ := h
  obtain ⟨j, T', R', hc', hs', ht'⟩ := k
  obtain ⟨n, hn, hsf⟩ := (hA s).mp ((bsub_valid_l I hH hc).2.tree.1 s hs)
  obtain ⟨m, hm, hsf'⟩ := (hA s').mp ((bsub_valid_l I hH hc').2.tree.1 s' hs')
  obtain ⟨rfl, es⟩ := cons_injective_l I hZF hω hz hn hm hsf hsf' ht ht'
  have e := bsub_unique_l I hH.1 hc hc'
  exact ⟨es, e.2.2.1, e.2.2.2⟩

def Gnode_d (z H t : M.Domain) : Prop := t = z ∨ ∃ s N F, Bshift_d I z H t s N F
def Gneg_d (z H E t : M.Domain) : Prop := (t = z ∧ M.mem z E) ∨
  ∃ s N F, Bshift_d I z H t s N F ∧ M.mem s N
def Glab_d (z H t v : M.Domain) : Prop := ∃ s N F, Bshift_d I z H t s N F ∧ M.PairMember I s v F
def gnode_m {d} (z H t : Term d) : Formula 1 d := .disj (Formula.extensionalEq t z)
  (.existsE (.existsE (.existsE (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken
    t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))
def gneg_m {d} (z H E t : Term d) : Formula 1 d := .disj (.conj (Formula.extensionalEq t z) (.mem z E))
  (.existsE (.existsE (.existsE (.conj (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken
    t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) (.mem (.bound 2) (.bound 1))))))
def glab_m {d} (z H t v : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
  (Formula.orderedPairMem 𝒞 (.bound 2) v.weaken.weaken.weaken .newest))))
derive_free_closed gnode_m
derive_free_closed gneg_m
derive_free_closed glab_m
theorem gnode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t : Term d) :
    Formula.satisfies ρ (gnode_m (𝒞 := 𝒞) z H t) ↔ Gnode_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) := by
  simp only [gnode_m, Gnode_d, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, bshift_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem gneg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H E t : Term d) :
    Formula.satisfies ρ (gneg_m (𝒞 := 𝒞) z H E t) ↔ Gneg_d I (z.eval ρ) (H.eval ρ) (E.eval ρ) (t.eval ρ) := by
  simp only [gneg_m, Gneg_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, bshift_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem glab_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t v : Term d) :
    Formula.satisfies ρ (glab_m (𝒞 := 𝒞) z H t v) ↔ Glab_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) (v.eval ρ) := by
  simp only [glab_m, Glab_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bshift_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

structure Bgraft_d (ω z H E T R N F : M.Domain) : Prop where
  nodes : ∀ t, M.mem t T ↔ Gnode_d I z H t
  edges : Edge_d I ω T R
  negs : ∀ t, M.mem t N ↔ Gneg_d I z H E t
  relation : M.IsSetRelation I F
  labels : ∀ t v, M.PairMember I t v F ↔ Glab_d I z H t v

/-- 拼接集合的实际存在性，尚不预先假设新树良基。 -/
theorem bgraft_exists_l (hZF : M.Models ZF) {ω A S z H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (E : M.Domain) : ∃ T R N F, Bgraft_d I ω z H E T R N F := by
  let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push H).push E
  let φ : UnarySchema 3 := { body := gnode_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest }
  let ψ : UnarySchema 3 := { body := gneg_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  let θ : BinarySchema 3 := { body := glab_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest }
  have typed t : Gnode_d I z H t → M.mem t A := fun h => h.elim
    (fun e => e.symm ▸ (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩)
    (fun ⟨_, _, _, h⟩ => (bshift_type_l I hZF hω hA hz hH h).1)
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ A
  have hT t : M.mem t T ↔ Gnode_d I z H t := ((hT' t).trans
    (and_congr_right fun _ => gnode_sat_l I hZF.1 _ _ _ _)).trans ⟨And.right, fun h => ⟨typed t h, h⟩⟩
  obtain ⟨N, hN'⟩ := ZF.separation_exists_d hZF ψ ρ A
  have hN t : M.mem t N ↔ Gneg_d I z H E t := ((hN' t).trans
    (and_congr_right fun _ => gneg_sat_l I hZF.1 _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨typed t (h.elim (fun h => Or.inl h.1) (fun ⟨s, N, F, h, _⟩ => Or.inr ⟨s, N, F, h⟩)), h⟩⟩
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A S
  obtain ⟨F, hf, hF⟩ := ZF.exists_setRelationOn_of_denote hZF I θ ρ W
  obtain ⟨R, hR⟩ := tree_edges_l I hZF ω T
  refine ⟨T, R, N, F, hT, hR, hN, hf.1, fun t v => ?_⟩
  have hh : θ.denote ρ t v ↔ Glab_d I z H t v := glab_sat_l I hZF.1 _ _ _ _ _
  refine ((hF t v).trans (and_congr_right fun _ => and_congr_right fun _ => hh)).trans ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨s, N, G, hs, hv⟩ := h
  obtain ⟨i, U, Q, hc, hst, hcons⟩ := hs
  have hvS := (bsub_valid_l I hH hc).2.leaf s v hv |>.2.1
  have hs : Bshift_d I z H t s N G := ⟨i, U, Q, hc, hst, hcons⟩
  exact ⟨(hW t).mpr (Or.inl (typed t (Or.inr ⟨s, N, G, hs⟩))), (hW v).mpr (Or.inr hvS), s, N, G, hs, hv⟩

end YesMetaZFC.SetTheory.Descriptive
