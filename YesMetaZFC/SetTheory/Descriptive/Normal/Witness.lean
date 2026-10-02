import YesMetaZFC.SetTheory.Descriptive.Normal.Sound

/-! # 闭证书的实际存在性

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

/-- 任意已编号的可数值图都能无选择地编码为实数。 -/
theorem nv_encode_l (hZF : M.Models ZF) {ω T E G z} (he : M.IsSetInjectionFromTo I E T ω)
    (hg : M.IsSetFunctionFromTo I G T ω) (hz : M.mem z ω) :
    ∃ w, M.IsSetFunctionFromTo I w ω ω ∧ ∀ a v, M.mem a T → (Nv_d I E w a v ↔ M.PairMember I a v G) := by
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I he.1.1 he.1.2.1
  have hd : M.IsSetBijectionFromTo I E T D :=
    ⟨⟨⟨he.1.1, he.1.2.1, fun a ha => (he.1.2.2 a ha).elim fun i h => ⟨i, (hD i).mpr ⟨a, h.2⟩, h.2⟩⟩, he.2⟩,
      fun i hi => ((hD i).mp hi).elim fun a h => ⟨a, he.1.input_mem_of_pairMember h, h⟩⟩
  obtain ⟨K, hk, ek⟩ := ZF.exists_inverseBijectionWithPairs hZF I hd
  obtain ⟨P, hp, ep⟩ := ZF.exists_compositionFunction hZF I hk.1.1 hg
  obtain ⟨w, ew, hw⟩ := Internal.senv_fill_exists_l I hZF (ω := ω) hp hz
  refine ⟨w, hw, fun a v ha => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hai, hiv⟩
    have hi := (hD i).mpr ⟨a, hai⟩
    have hiv := ((ew.2 i v).mp hiv).2.elim And.right (fun h => (h.1 hi).elim)
    obtain ⟨_, b, hib, hbv⟩ := (ep i v).mp hiv
    exact he.2 b a i ((ek i b).mp hib) hai ▸ hbv
  · intro hav
    obtain ⟨i, hiω, hai⟩ := he.1.2.2 a ha
    have hi := (hD i).mpr ⟨a, hai⟩
    exact ⟨i, hai, (ew.2 i v).mpr ⟨hiω, Or.inl ⟨hi, (ep i v).mpr ⟨hi, a, (ek i a).mpr hai, hav⟩⟩⟩⟩

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
        · exact Structure.SuccessorOf.eq hZF.1 hv (nj_unique_l I hZF.1 (hω.isOrdinal hZF) he.1 hk hj ▸ hu))
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
