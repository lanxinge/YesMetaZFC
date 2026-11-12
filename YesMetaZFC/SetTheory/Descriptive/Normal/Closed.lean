import YesMetaZFC.SetTheory.Descriptive.Coding.FunctionCode
import YesMetaZFC.SetTheory.Descriptive.Analytic.Code
import YesMetaZFC.SetTheory.Descriptive.Topology.Completion
import YesMetaZFC.SetTheory.Descriptive.Game.Closed

/-! # Borel 求值的闭证书语法

证书实数在节点编号处记数值：零为假，非零为真；真并节点记所选子编号的后继。
违规由有限读数见证。叶为假的违规读取完整有限标签，叶为真的违规则读取一处冲突。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ns_d (T R E a v : M.Domain) : Prop := ∃ b j,
  M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b j E ∧ M.SuccessorOf v j
def ns_m {d} (T R E a v : Term d) : Formula 1 d := .existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken)
  (.conj (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken) (Formula.isSuccessor v.weaken.weaken .newest)))))
derive_free_closed ns_m
theorem ns_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R E a v : Term d) :
    Formula.satisfies ρ (ns_m (𝒞 := 𝒞) T R E a v) ↔
      Ns_d I (T.eval ρ) (R.eval ρ) (E.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [ns_m, Ns_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

def Nl_d (F E z x w : M.Domain) : Prop := ∃ a s v, M.PairMember I a s F ∧ Nv_d I E w a v ∧
  ((v = z ∧ M.MemberSubset s x) ∨ (v ≠ z ∧ ∃ j, Diff_d I s x j))
def nl_m {d} (F E z x w : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken w.weaken.weaken.weaken (.bound 2) .newest)
  (.disj (.conj (Formula.extensionalEq .newest z.weaken.weaken.weaken) (Formula.subset (.bound 1) x.weaken.weaken.weaken))
    (.conj (.neg (Formula.extensionalEq .newest z.weaken.weaken.weaken))
      (.existsE (diff_m (𝒞 := 𝒞) (.bound 2) x.weaken.weaken.weaken.weaken .newest))))))))
derive_free_closed nl_m
theorem nl_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F E z x w : Term d) :
    Formula.satisfies ρ (nl_m (𝒞 := 𝒞) F E z x w) ↔
      Nl_d I (F.eval ρ) (E.eval ρ) (z.eval ρ) (x.eval ρ) (w.eval ρ) := by
  simp only [nl_m, Nl_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, nv_sat_l I, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_subset_iff, Formula.satisfies_neg_iff,
    diff_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Nn_d (R N E z w : M.Domain) : Prop := ∃ a b v u, M.mem a N ∧ Rd_entry_d b a R ∧
  Nv_d I E w a v ∧ Nv_d I E w b u ∧ (v = z ↔ u = z)
def nn_m {d} (R N E z w : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (.mem (.bound 3) N.weaken.weaken.weaken.weaken) (.conj
  (rd_entry_m (.bound 2) (.bound 3) R.weaken.weaken.weaken.weaken) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken.weaken w.weaken.weaken.weaken.weaken (.bound 3) (.bound 1)) (.conj
  (nv_m (𝒞 := 𝒞) E.weaken.weaken.weaken.weaken w.weaken.weaken.weaken.weaken (.bound 2) .newest)
  (.iff (Formula.extensionalEq (.bound 1) z.weaken.weaken.weaken.weaken)
    (Formula.extensionalEq .newest z.weaken.weaken.weaken.weaken)))))))))
derive_free_closed nn_m
theorem nn_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R N E z w : Term d) :
    Formula.satisfies ρ (nn_m (𝒞 := 𝒞) R N E z w) ↔
      Nn_d I (R.eval ρ) (N.eval ρ) (E.eval ρ) (z.eval ρ) (w.eval ρ) := by
  simp only [nn_m, Nn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry_sat_l hE, nv_sat_l I, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

def Nu_d (T R E z a v w : M.Domain) : Prop :=
  (v = z ∧ ∃ b u, M.mem b T ∧ Rd_entry_d b a R ∧ Nv_d I E w b u ∧ u ≠ z) ∨
  (v ≠ z ∧ ¬ Ns_d I T R E a v) ∨
  ∃ b j, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b j E ∧ M.SuccessorOf v j ∧ Nv_d I E w b z
def nu_m {d} (T R E z a v w : Term d) : Formula 1 d := .disj
  (.conj (Formula.extensionalEq v z) (.existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken)
    (.conj (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken) (.conj
      (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) .newest)
      (.neg (Formula.extensionalEq .newest z.weaken.weaken)))))))) (.disj
  (.conj (.neg (Formula.extensionalEq v z)) (.neg (ns_m (𝒞 := 𝒞) T R E a v)))
  (.existsE (.existsE (.conj (.mem (.bound 1) T.weaken.weaken) (.conj
    (rd_entry_m (.bound 1) a.weaken.weaken R.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken) (.conj
    (Formula.isSuccessor v.weaken.weaken .newest)
    (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) z.weaken.weaken))))))))
derive_free_closed nu_m
theorem nu_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R E z a v w : Term d) :
    Formula.satisfies ρ (nu_m (𝒞 := 𝒞) T R E z a v w) ↔
      Nu_d I (T.eval ρ) (R.eval ρ) (E.eval ρ) (z.eval ρ) (a.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [nu_m, Nu_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    rd_entry_sat_l hE, nv_sat_l I, Formula.satisfies_neg_iff, ns_sat_l I hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

def Nb_d (T R N F E z x w : M.Domain) : Prop := Nv_d I E w z z ∨ Nl_d I F E z x w ∨
  Nn_d I R N E z w ∨ ∃ a v, Buni_d I N F a ∧ Nv_d I E w a v ∧ Nu_d I T R E z a v w
def nb_m {d} (T R N F E z x w : Term d) : Formula 1 d := .disj (nv_m (𝒞 := 𝒞) E w z z) (.disj
  (nl_m (𝒞 := 𝒞) F E z x w) (.disj (nn_m (𝒞 := 𝒞) R N E z w)
    (.existsE (.existsE (.conj (buni_m (𝒞 := 𝒞) N.weaken.weaken F.weaken.weaken (.bound 1))
      (.conj (nv_m (𝒞 := 𝒞) E.weaken.weaken w.weaken.weaken (.bound 1) .newest)
        (nu_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken E.weaken.weaken z.weaken.weaken (.bound 1) .newest w.weaken.weaken)))))))
derive_free_closed nb_m
theorem nb_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F E z x w : Term d) :
    Formula.satisfies ρ (nb_m (𝒞 := 𝒞) T R N F E z x w) ↔
      Nb_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (E.eval ρ) (z.eval ρ) (x.eval ρ) (w.eval ρ) := by
  simp only [nb_m, Nb_d, Formula.satisfies_disj_iff, nv_sat_l I, nl_sat_l I hE, nn_sat_l I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, buni_sat_l I, nu_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 闭证书的可靠性

证书与已有内部求值逐节点相符。比较性质是实际原公式，使用内部良基归纳，
不把非标准树当成外部良基树处理。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem nf_nodiff_l (hZF : M.Models ZF) {ω n s x} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (hx : M.IsSetFunctionFromTo I x ω ω)
    (h : ∀ j, ¬ Diff_d I s x j) : M.MemberSubset s x := by
  intro p hp
  obtain ⟨i, a, hc⟩ := hs.1.1 p hp
  obtain ⟨b, _, hb⟩ := hx.2.2 i (hω.transitive (ZF.modelsKP hZF) n hn i (hs.input_mem_of_pairMember ⟨p, hc, hp⟩))
  have e : a = b := Classical.byContradiction (fun e => h i ⟨a, b, ⟨p, hc, hp⟩, hb, e⟩)
  obtain ⟨q, hq, hqx⟩ := hb
  exact (I.unique (e ▸ hc) hq).symm ▸ hqx

theorem nb_agree_l (hZF : M.Models ZF) {ω A T R N F E z x w V} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F)
    (he : M.IsSetFunctionFromTo I E T ω) (hx : M.IsSetFunctionFromTo I x ω ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (hn : ¬ Nb_d I T R N F E z x w)
    (hv : Bsem_d I T R N F x V) : ∀ a, M.mem a T → ∀ v, Nv_d I E w a v → (M.mem a V ↔ v ≠ z) := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => E, fun _ => E⟩ : Env M 1).push w).push z).push V
  let φ : UnarySchema 4 := {
    body := .forallE (.imp (nv_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 1) .newest)
      (.iff (.mem (.bound 1) (.bound 2)) (.neg (Formula.extensionalEq .newest (.bound 3))))) }
  have hp a : φ.denote ρ a ↔ ∀ v, Nv_d I E w a v → (M.mem a V ↔ v ≠ z) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      nv_sat_l I, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all := wf_rel_ind_l hZF hc.wf φ ρ (fun a ha ih => (hp a).mpr (by
    intro v hav
    by_cases hf : ∃ s, M.PairMember I a s F
    · obtain ⟨s, hs⟩ := hf
      have leaf := hc.leaf a s hs
      refine (bsem_leaf_l I hv hc.leaf_fn ha leaf.2.2.1 hs).trans ⟨?_, ?_⟩
      · exact fun hsx e => hn (Or.inr (Or.inl ⟨a, s, v, hs, hav, Or.inl ⟨e, hsx⟩⟩))
      · intro hne
        obtain ⟨n, hnω, hsF⟩ := (hA s).mp leaf.2.1
        exact nf_nodiff_l I hZF hω hnω hsF hx (fun j hd =>
          hn (Or.inr (Or.inl ⟨a, s, v, hs, hav, Or.inr ⟨hne, j, hd⟩⟩)))
    · by_cases haN : M.mem a N
      · obtain ⟨b, hb, hba, hu⟩ := hc.neg a haN
        obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
        have ib := (hp b).mp (ih b hb hba) u hbu
        have wrong : ¬ (v = z ↔ u = z) := fun h => hn (Or.inr (Or.inr (Or.inl ⟨a, b, v, u, haN, hba, hav, hbu, h⟩)))
        have eqn : v ≠ z ↔ u = z := ⟨fun h => Classical.byContradiction (fun h' => wrong (iff_of_false h h')),
          fun h e => wrong (iff_of_true e h)⟩
        have val : M.mem a V ↔ u = z := by
          simpa only [Classical.not_not] using (bsem_neg_l I hv ha haN hf hb hba hu).trans (not_congr ib)
        exact val.trans eqn.symm
      · have hu : Buni_d I N F a := ⟨haN, hf⟩
        have bad (h : Nu_d I T R E z a v w) := hn (Or.inr (Or.inr (Or.inr ⟨a, v, hu, hav, h⟩)))
        refine (bsem_union_l I hv ha haN hf).trans ⟨?_, ?_⟩
        · rintro ⟨b, hb, hba, hbV⟩ e
          obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
          exact bad (Or.inl ⟨e, b, u, hb, hba, hbu, ((hp b).mp (ih b hb hba) u hbu).mp hbV⟩)
        · intro hne
          have sel : Ns_d I T R E a v := Classical.byContradiction (fun h => bad (Or.inr (Or.inl ⟨hne, h⟩)))
          obtain ⟨b, j, hb, hba, hbj, hj⟩ := sel
          obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
          have hne' : u ≠ z := fun e => bad (Or.inr (Or.inr ⟨b, j, hb, hba, hbj, hj, e ▸ hbu⟩))
          exact ⟨b, hb, hba, ((hp b).mp (ih b hb hba) u hbu).mpr hne'⟩))
  exact fun a ha => (hp a).mp (all a ha)

theorem nb_sound_l (hZF : M.Models ZF) {ω A c T R N F E z x w} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F) (hpack : Bpack_d I c T R N F)
    (he : M.IsSetFunctionFromTo I E T ω) (hz : ∀ p, ¬ M.mem p z)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (hn : ¬ Nb_d I T R N F E z x w) : Bsat_d I ω A A c x := by
  obtain ⟨e, he0, het⟩ := hc.root
  have hzT := hZF.1.eq_of_same_members e z (fun p => iff_of_false (he0 p) (hz p)) ▸ het
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  obtain ⟨v, _, h⟩ := nv_total_l I he hw hzT
  exact (bsat_root_l I hZF hpack hc hv hz).mpr
    ((nb_agree_l I hZF hω hA hc he hx hw hn hv z hzT v h).mpr (fun e => hn (Or.inl (e ▸ h))))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 闭证书的实际存在性

真并节点选择真子节点编号中的内部最小者。节点值图经编号的逆图搬到 ω，
域外填零，得到实际 Baire 实数；没有逐节点调用选择公理。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ch_d (R E V a j : M.Domain) : Prop := ∃ b, M.mem b V ∧ Rd_entry_d b a R ∧ M.PairMember I b j E
def ch_m {d} (R E V a j : Term d) : Formula 1 d := Formula.existsMem V (.conj
  (rd_entry_m .newest a.weaken R.weaken) (Formula.orderedPairMem 𝒞 .newest j.weaken E.weaken))
derive_free_closed ch_m
theorem ch_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R E V a j : Term d) :
    Formula.satisfies ρ (ch_m (𝒞 := 𝒞) R E V a j) ↔
      Ch_d I (R.eval ρ) (E.eval ρ) (V.eval ρ) (a.eval ρ) (j.eval ρ) := by
  simp only [ch_m, Ch_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl
def Nj_d (R E V a j : M.Domain) : Prop := Ch_d I R E V a j ∧ ∀ k, Ch_d I R E V a k → ¬ M.mem k j
def nj_m {d} (R E V a j : Term d) : Formula 1 d := .conj (ch_m (𝒞 := 𝒞) R E V a j)
  (.forallE (.imp (ch_m (𝒞 := 𝒞) R.weaken E.weaken V.weaken a.weaken .newest) (.neg (.mem .newest j.weaken))))
derive_free_closed nj_m
theorem nj_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R E V a j : Term d) :
    Formula.satisfies ρ (nj_m (𝒞 := 𝒞) R E V a j) ↔
      Nj_d I (R.eval ρ) (E.eval ρ) (V.eval ρ) (a.eval ρ) (j.eval ρ) := by
  simp only [nj_m, Nj_d, Formula.satisfies_conj_iff, ch_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem nj_exists_l (hZF : M.Models ZF) {ω T R E V a} (he : M.IsSetFunctionFromTo I E T ω)
    (h : ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) : ∃ j, Nj_d I R E V a j := by
  let ρ : Env M 4 := (((⟨fun _ => R, fun _ => R⟩ : Env M 1).push E).push V).push a
  let φ : UnarySchema 4 := { body := ch_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ ω
  have hD j : M.mem j D ↔ Ch_d I R E V a j := ((hD' j).trans
    (and_congr_right fun _ => ch_sat_l I hZF.1 _ _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨h.elim fun _ h => he.output_mem_of_pairMember h.2.2, h⟩⟩
  obtain ⟨b, hb, hba, hbV⟩ := h
  obtain ⟨i, _, hbi⟩ := he.2.2 b hb
  obtain ⟨j, hj, hmin⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨i, (hD i).mpr ⟨b, hbV, hba, hbi⟩⟩
  exact ⟨j, (hD j).mp hj, fun k hk => hmin k ((hD k).mpr hk)⟩

theorem nj_unique_l (hE : Extensional M) {ω T R E V a i j} (hω : M.IsOrdinal ω)
    (he : M.IsSetFunctionFromTo I E T ω) (h : Nj_d I R E V a i) (k : Nj_d I R E V a j) : i = j := by
  have typed {i} (h : Ch_d I R E V a i) := h.elim fun _ h => he.output_mem_of_pairMember h.2.2
  rcases hω.wellOrder.linear.compare i (typed h.1) j (typed k.1) with e | hij | hji
  · exact hE.eq_of_same_members i j e
  · exact (k.2 i h.1 hij).elim
  · exact (h.2 j k.1 hji).elim

def Nw_d (R N F E V z o a v : M.Domain) : Prop :=
  (¬ M.mem a V ∧ v = z) ∨ (M.mem a V ∧ ((¬ Buni_d I N F a ∧ v = o) ∨
    (Buni_d I N F a ∧ ∃ j, Nj_d I R E V a j ∧ M.SuccessorOf v j)))
def nw_m {d} (R N F E V z o a v : Term d) : Formula 1 d := .disj
  (.conj (.neg (.mem a V)) (Formula.extensionalEq v z)) (.conj (.mem a V) (.disj
  (.conj (.neg (buni_m (𝒞 := 𝒞) N F a)) (Formula.extensionalEq v o))
  (.conj (buni_m (𝒞 := 𝒞) N F a) (.existsE (.conj
    (nj_m (𝒞 := 𝒞) R.weaken E.weaken V.weaken a.weaken .newest) (Formula.isSuccessor v.weaken .newest))))))
derive_free_closed nw_m
theorem nw_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R N F E V z o a v : Term d) :
    Formula.satisfies ρ (nw_m (𝒞 := 𝒞) R N F E V z o a v) ↔
      Nw_d I (R.eval ρ) (N.eval ρ) (F.eval ρ) (E.eval ρ) (V.eval ρ) (z.eval ρ) (o.eval ρ) (a.eval ρ) (v.eval ρ) := by
  simp only [nw_m, Nw_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hE, buni_sat_l I,
    Formula.satisfies_exists_iff, nj_sat_l I hE, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

theorem nw_real_l (hZF : M.Models ZF) {ω T R N F E V z x} (hω : M.IsOmega ω)
    (he : M.IsSetInjectionFromTo I E T ω) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hv : Bsem_d I T R N F x V) : ∃ w, M.IsSetFunctionFromTo I w ω ω ∧
      (∀ a v, M.mem a T → Nv_d I E w a v → (M.mem a V ↔ v ≠ z)) ∧
      ∀ a v, M.mem a T → Nv_d I E w a v → M.mem a V → Buni_d I N F a →
        ∃ b j, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V ∧ M.PairMember I b j E ∧ M.SuccessorOf v j := by
  classical
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  let ρ : Env M 7 := ((((((⟨fun _ => R, fun _ => R⟩ : Env M 1).push N).push F).push E).push V).push z).push o
  let φ : BinarySchema 7 := { body := nw_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp a v : φ.denote ρ a v ↔ Nw_d I R N F E V z o a v := nw_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _
  have typed {a j} (h : Nj_d I R E V a j) := h.1.elim fun _ h => he.1.output_mem_of_pairMember h.2.2
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := ω)
    (by
      intro a ha
      by_cases haV : M.mem a V
      · by_cases hu : Buni_d I N F a
        · obtain ⟨j, hj⟩ := nj_exists_l I hZF he.1 ((bsem_union_l I hv ha hu.1 hu.2).mp haV)
          obtain ⟨v, hvj, _⟩ := hω.1.2 j (typed hj)
          exact ⟨v, (hp a v).mpr (Or.inr ⟨haV, Or.inr ⟨hu, j, hj, hvj⟩⟩)⟩
        · exact ⟨o, (hp a o).mpr (Or.inr ⟨haV, Or.inl ⟨hu, rfl⟩⟩)⟩
      · exact ⟨z, (hp a z).mpr (Or.inl ⟨haV, rfl⟩)⟩)
    (by
      intro a _ v u hv hu
      rcases (hp a v).mp hv with ⟨hn, rfl⟩ | ⟨ha, hv⟩ <;> rcases (hp a u).mp hu with ⟨hn', rfl⟩ | ⟨ha', hu⟩
      · rfl
      · exact (hn ha').elim
      · exact (hn' ha).elim
      · rcases hv with ⟨hn, rfl⟩ | ⟨hn, j, hj, hv⟩ <;> rcases hu with ⟨hn', rfl⟩ | ⟨hn', k, hk, hu⟩
        · rfl
        · exact (hn hn').elim
        · exact (hn' hn).elim
        · exact Structure.SuccessorOf.eq hZF.1 hv (nj_unique_l I hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) he.1 hk hj ▸ hu))
    (by
      intro a v _ hv
      rcases (hp a v).mp hv with ⟨_, e⟩ | ⟨_, ⟨_, e⟩ | ⟨_, j, hj, hv⟩⟩
      · exact e.symm ▸ hzω
      · exact e.symm ▸ hoω
      · obtain ⟨u, hu, huω⟩ := hω.1.2 j (typed hj)
        exact Structure.SuccessorOf.eq hZF.1 hu hv ▸ huω)
  obtain ⟨w, hw, ew⟩ := nv_encode_l I hZF he hg hzω
  have val a v (ha : M.mem a T) (hav : Nv_d I E w a v) := (hp a v).mp ((eg a v).mp ((ew a v ha).mp hav)).2
  refine ⟨w, hw, ?_, ?_⟩
  · intro a v ha hav
    rcases val a v ha hav with ⟨haV, e⟩ | ⟨haV, ⟨_, e⟩ | ⟨_, j, _, hj⟩⟩
    · exact iff_of_false haV (fun h => h e)
    · exact iff_of_true haV (fun h => hz z (e.symm.trans h ▸ ho.predecessor_mem))
    · exact iff_of_true haV (fun e => hz j (e ▸ hj.predecessor_mem))
  · intro a v ha hav haV hu
    rcases val a v ha hav with ⟨hn, _⟩ | ⟨_, ⟨hn, _⟩ | ⟨_, j, hj, hv⟩⟩
    · exact (hn haV).elim
    · exact (hn hu).elim
    · obtain ⟨b, hb, hba, hbj⟩ := hj.1
      exact ⟨b, j, he.1.input_mem_of_pairMember hbj, hba, hb, hbj, hv⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 真值产生无违规的闭证书 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem nb_complete_l (hZF : M.Models ZF) {ω A c T R N F E z x} (hω : M.IsOmega ω)
    (hc : Btree_d I ω A A T R N F) (hpack : Bpack_d I c T R N F)
    (he : M.IsSetInjectionFromTo I E T ω) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (h : Bsat_d I ω A A c x) :
    ∃ w, M.IsSetFunctionFromTo I w ω ω ∧ ¬ Nb_d I T R N F E z x w := by
  classical
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have root := (bsat_root_l I hZF hpack hc hv hz).mp h
  obtain ⟨w, hw, val, sel⟩ := nw_real_l I hZF hω he hz hzω hv
  have node {a v} (h : Nv_d I E w a v) := h.elim fun _ h => he.1.input_mem_of_pairMember h.1
  refine ⟨w, hw, fun h => ?_⟩
  rcases h with h | h | h | ⟨a, v, hu, hav, h⟩
  · exact (val z z (node h) h).mp root rfl
  · obtain ⟨a, s, v, hs, hav, hsx | ⟨hne, j, b, d, hjs, hjx, hbd⟩⟩ := h
    · have ha := (bsem_leaf_l I hv hc.leaf_fn (node hav) (hc.leaf a s hs).2.2.1 hs).mpr hsx.2
      exact (val a v (node hav) hav).mp ha hsx.1
    · have ha := (val a v (node hav) hav).mpr hne
      have hsub := (bsem_leaf_l I hv hc.leaf_fn (node hav) (hc.leaf a s hs).2.2.1 hs).mp ha
      exact hbd (hx.1.2 j b d (hjs.elim fun p hp => ⟨p, hp.1, hsub p hp.2⟩) hjx)
  · obtain ⟨a, b, v, u, haN, hba, hav, hbu, wrong⟩ := h
    obtain ⟨d, _, _, uniq⟩ := hc.neg a haN
    have hbT := ((hc.edges.2 a b).mp hba).2.1
    have hneg := bsem_neg_l I hv (node hav) haN
      (fun ⟨s, hs⟩ => (hc.leaf a s hs).2.2.1 haN) hbT hba
      (fun e heT hea => (uniq e heT hea).trans (uniq b hbT hba).symm)
    have eqv : M.mem a V ↔ M.mem b V := (val a v (node hav) hav).trans
      ((not_congr wrong).trans (val b u hbT hbu).symm)
    by_cases haV : M.mem a V
    · exact hneg.mp haV (eqv.mp haV)
    · exact haV (hneg.mpr (fun hbV => haV (eqv.mpr hbV)))
  · rcases h with ⟨e, b, u, hb, hba, hbu, hne⟩ | ⟨hne, hn⟩ | ⟨b, j, hb, hba, hbj, hj, hbz⟩
    · have haV := (bsem_union_l I hv (node hav) hu.1 hu.2).mpr ⟨b, hb, hba, (val b u hb hbu).mpr hne⟩
      exact (val a v (node hav) hav).mp haV e
    · obtain ⟨b, j, hb, hba, _, hbj, hj⟩ := sel a v (node hav) hav ((val a v (node hav) hav).mpr hne) hu
      exact hn ⟨b, j, hb, hba, hbj, hj⟩
    · have hne : v ≠ z := fun e => hz j (e ▸ hj.predecessor_mem)
      obtain ⟨d, k, _, _, hdV, hdk, hk⟩ := sel a v (node hav) hav ((val a v (node hav) hav).mpr hne) hu
      have ejk := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal (ZF.modelsKP hZF)).mem (he.1.output_mem_of_pairMember hbj)) hj hk
      have edb := he.2 d b j (ejk.symm ▸ hdk) hbj
      exact (val b z hb hbz).mp (edb ▸ hdV) rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 有限观察的合并

观察用一对相同内部长度的前缀给出，并在任何图延拓上保持成立。
合取取较长前缀；本层仅作证明组织，最终证书仍由原公式定义。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def No_d (ω x w : M.Domain) (P : M.Domain → M.Domain → Prop) : Prop := ∃ n s t,
  M.mem n ω ∧ M.IsRestrictionOf I s x n ∧ M.IsRestrictionOf I t w n ∧
    ∀ u v, M.MemberSubset s u → M.MemberSubset t v → P u v

theorem no_map_l {ω x w} {P Q : M.Domain → M.Domain → Prop} (h : No_d I ω x w P)
    (f : ∀ u v, P u v → Q u v) : No_d I ω x w Q := by
  obtain ⟨n, s, t, hn, hs, ht, h⟩ := h
  exact ⟨n, s, t, hn, hs, ht, fun u v hu hv => f u v (h u v hu hv)⟩

theorem no_and_l (hZF : M.Models ZF) {ω x w} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    {P Q : M.Domain → M.Domain → Prop} (h : No_d I ω x w P) (k : No_d I ω x w Q) :
    No_d I ω x w (fun u v => P u v ∧ Q u v) := by
  obtain ⟨n, s, t, hn, hs, ht, h⟩ := h
  obtain ⟨m, u, v, hm, hu, hv, k⟩ := k
  have inc {f n m s t} (hf : M.IsSetFunctionFromTo I f ω ω) (hn : M.mem n ω) (hm : M.mem m ω)
      (hs : M.IsRestrictionOf I s f n) (ht : M.IsRestrictionOf I t f m) (h : M.MemberSubset n m) :=
    ds_prefix_mono_l I (hs.isSetFunctionFromTo hf (hω.transitive (ZF.modelsKP hZF) n hn))
      (ht.isSetFunctionFromTo hf (hω.transitive (ZF.modelsKP hZF) m hm)).1 hs ht h
  have le : M.MemberSubset n m ∨ M.MemberSubset m n := by
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with e | h | h
    · exact Or.inl (fun a => (e a).mp)
    · exact Or.inl (((hω.isOrdinal (ZF.modelsKP hZF)).mem hm).transitive n h)
    · exact Or.inr (((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).transitive m h)
  rcases le with le | le
  · exact ⟨m, u, v, hm, hu, hv, fun a b ha hb =>
      ⟨h a b (fun p hp => ha p (inc hx hn hm hs hu le p hp)) (fun p hp => hb p (inc hw hn hm ht hv le p hp)), k a b ha hb⟩⟩
  · exact ⟨n, s, t, hn, hs, ht, fun a b ha hb =>
      ⟨h a b ha hb, k a b (fun p hp => ha p (inc hx hm hn hu hs le p hp)) (fun p hp => hb p (inc hw hm hn hv ht le p hp))⟩⟩

theorem no_pair_l (hZF : M.Models ZF) {ω x w i a} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (b : Bool) (h : M.PairMember I i a (if b then w else x)) :
    No_d I ω x w (fun u v => M.PairMember I i a (if b then v else u)) := by
  have hi : M.mem i ω := by cases b; exact hx.input_mem_of_pairMember h; exact hw.input_mem_of_pairMember h
  obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
  obtain ⟨s, _, hs, _⟩ := ds_prefix_l I hZF hω hx hnω
  obtain ⟨t, _, ht, _⟩ := ds_prefix_l I hZF hω hw hnω
  refine ⟨n, s, t, hnω, hs, ht, fun u v hu hv => ?_⟩
  cases b
  · exact ((hs.2 i a).mpr ⟨hn.predecessor_mem, h⟩).elim fun p hp => ⟨p, hp.1, hu p hp.2⟩
  · exact ((ht.2 i a).mpr ⟨hn.predecessor_mem, h⟩).elim fun p hp => ⟨p, hp.1, hv p hp.2⟩

theorem no_nv_l (hZF : M.Models ZF) {ω E x w a v} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω) (h : Nv_d I E w a v) :
    No_d I ω x w (fun _ t => Nv_d I E t a v) := by
  obtain ⟨i, hi, hv⟩ := h
  exact no_map_l I (no_pair_l I hZF hω hx hw true hv) (fun _ _ h => ⟨i, hi, h⟩)

theorem no_sub_l (hZF : M.Models ZF) {ω A x w s} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hx : M.IsSetFunctionFromTo I x ω ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (hs : M.mem s A) (h : M.MemberSubset s x) :
    No_d I ω x w (fun u _ => M.MemberSubset s u) := by
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨t, _, ht, _⟩ := ds_prefix_l I hZF hω hw hn
  exact ⟨n, s, t, hn, (ds_restrict_iff_l I hs hx.1).mpr h, ht, fun _ _ h _ => h⟩

theorem nb_observe_l (hZF : M.Models ZF) {ω A T R N F E z x w} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (h : Nb_d I T R N F E z x w) : No_d I ω x w (fun u v => Nb_d I T R N F E z u v) := by
  have read {a v} (h : Nv_d I E w a v) := no_nv_l I hZF hω hx hw h
  rcases h with h | h | h | ⟨a, v, hu, hav, h⟩
  · exact no_map_l I (read h) (fun _ _ h => Or.inl h)
  · obtain ⟨a, s, v, hs, hav, hsx | ⟨hne, j, b, c, hjs, hjx, hbc⟩⟩ := h
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav)
        (no_sub_l I hZF hω hA hx hw (hc.leaf a s hs).2.1 hsx.2))
        (fun _ _ h => Or.inr (Or.inl ⟨a, s, v, hs, h.1, Or.inl ⟨hsx.1, h.2⟩⟩))
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (no_pair_l I hZF hω hx hw false hjx))
        (fun _ _ h => Or.inr (Or.inl ⟨a, s, v, hs, h.1, Or.inr ⟨hne, j, b, c, hjs, h.2, hbc⟩⟩))
  · obtain ⟨a, b, v, u, haN, hba, hav, hbu, eqn⟩ := h
    exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbu))
      (fun _ _ h => Or.inr (Or.inr (Or.inl ⟨a, b, v, u, haN, hba, h.1, h.2, eqn⟩)))
  · rcases h with ⟨e, b, u, hb, hba, hbu, hne⟩ | ⟨hne, hn⟩ | ⟨b, j, hb, hba, hbj, hj, hbz⟩
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbu))
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h.1, Or.inl ⟨e, b, u, hb, hba, h.2, hne⟩⟩)))
    · exact no_map_l I (read hav)
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h, Or.inr (Or.inl ⟨hne, hn⟩)⟩)))
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbz))
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h.1, Or.inr (Or.inr ⟨b, j, hb, hba, hbj, hj, h.2⟩)⟩)))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 无违规证书组成实际闭集 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Nc_d (B J T R N F E z p : M.Domain) : Prop := ∃ x w,
  M.mem x B ∧ M.mem w B ∧ Rp_d I J x w p ∧ ¬ Nb_d I T R N F E z x w
def nc_m {d} (B J T R N F E z p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) B.weaken.weaken) (.conj (.mem .newest B.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken (.bound 1) .newest p.weaken.weaken)
  (.neg (nb_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken E.weaken.weaken z.weaken.weaken (.bound 1) .newest))))))
derive_free_closed nc_m
theorem nc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J T R N F E z p : Term d) :
    Formula.satisfies ρ (nc_m (𝒞 := 𝒞) B J T R N F E z p) ↔
      Nc_d I (B.eval ρ) (J.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (E.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [nc_m, Nc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rp_sat_l I, Formula.satisfies_neg_iff, nb_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem nc_closed_l (hZF : M.Models ZF) {ω A B J T R N F} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hc : Btree_d I ω A A T R N F) (E z : M.Domain) :
    ∃ C, Cl_d A B C ∧ ∀ p, M.mem p C ↔ M.mem p B ∧ Nc_d I B J T R N F E z p := by
  classical
  let ρ : Env M 8 := (((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push J).push T).push R).push N).push F).push E).push z
  let φ : UnarySchema 8 := { body := nc_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hC p : M.mem p C ↔ M.mem p B ∧ Nc_d I B J T R N F E z p :=
    (hC' p).trans (and_congr_right fun _ => nc_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _)
  obtain ⟨U, hU⟩ := cm_exists_l (ZF.modelsKP hZF) B C
  refine ⟨C, ⟨fun p hp => ((hC p).mp hp).1, U, hU, ⟨fun p hp => ((hU p).mp hp).1, ?_⟩⟩, hC⟩
  intro p hp
  obtain ⟨hpB, hpC⟩ := (hU p).mp hp
  obtain ⟨x, w, hx, hw, hpair⟩ := rp_decode_l I hZF hJ ((hB.2 p).mp hpB)
  have bad : Nb_d I T R N F E z x w := Classical.byContradiction
    (fun h => hpC ((hC p).mpr ⟨hpB, x, w, (hB.2 x).mpr hx, (hB.2 w).mpr hw, hpair, h⟩))
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := nb_observe_l I hZF hB.1 hA hc hx hw bad
  have hsf := hs.isSetFunctionFromTo hx (hB.1.transitive (ZF.modelsKP hZF) n hn)
  have htf := ht.isSetFunctionFromTo hw (hB.1.transitive (ZF.modelsKP hZF) n hn)
  obtain ⟨r, hrf, hr⟩ := rp_exists_l I hZF hJ hsf htf
  refine ⟨r, (hA r).mpr ⟨n, hn, hrf⟩, (rp_subset_l I hJ hsf htf hr hpair).mpr
    ⟨(ds_restrict_iff_l I hsf hx.1).mp hs, (ds_restrict_iff_l I htf hw.1).mp ht⟩, fun q hq hrq => ?_⟩
  apply (hU q).mpr
  refine ⟨hq, fun hqC => ?_⟩
  obtain ⟨_, y, v, hy, hv, hqpair, hn⟩ := (hC q).mp hqC
  obtain ⟨hsy, htv⟩ := (rp_subset_l I hJ hsf htf hr hqpair).mp hrq
  exact hn (obs y v hsy htv)

/-- 每个 Borel 解释都是一个实际闭证书集的投影。 -/
theorem borel_closed_proj_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : Borel_d I ω A A B K) : ∃ C, Cl_d A B C ∧ Pr_d I B J C K := by
  obtain ⟨c, hc, hk⟩ := hk
  obtain ⟨T, R, N, F, hpack, hc⟩ := hc
  obtain ⟨G, hg⟩ := ha
  obtain ⟨E, hE⟩ := ZF.exists_restriction hZF I G T
  have he : M.IsSetInjectionFromTo I E T ω := ⟨hE.isSetFunctionFromTo hg.1 hc.tree.1,
    fun a b i hai hbi => hg.2 a b i ((hE.2 a i).mp hai).2 ((hE.2 b i).mp hbi).2⟩
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨C, hC, eqn⟩ := nc_closed_l I hZF hB hA hJ hc E z
  refine ⟨C, hC, fun x => ⟨?_, ?_⟩⟩
  · intro hxK
    obtain ⟨hxB, hx⟩ := (hk x).mp hxK
    obtain ⟨w, hw, hn⟩ := nb_complete_l I hZF hB.1 hc hpack he hz hzω ((hB.2 x).mp hxB) hx
    obtain ⟨p, hp, hpair⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hxB) hw
    exact ⟨hxB, w, p, (hB.2 w).mpr hw, (hB.2 p).mpr hp, hpair,
      (eqn p).mpr ⟨(hB.2 p).mpr hp, x, w, hxB, (hB.2 w).mpr hw, hpair, hn⟩⟩
  · rintro ⟨hxB, w, p, hwB, _, hpair, hpC⟩
    obtain ⟨_, y, v, hyB, hvB, hp, hn⟩ := (eqn p).mp hpC
    obtain ⟨ex, ew⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hxB) ((hB.2 w).mp hwB)
      ((hB.2 y).mp hyB) ((hB.2 v).mp hvB) hpair hp
    subst y v
    exact (hk x).mpr ⟨hxB, nb_sound_l I hZF hB.1 hA hc hpack he.1 hz ((hB.2 x).mp hxB) ((hB.2 w).mp hwB) hn⟩

end YesMetaZFC.SetTheory.Descriptive
