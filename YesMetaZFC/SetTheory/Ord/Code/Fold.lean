import YesMetaZFC.SetTheory.Ord.Code.Pair

/-! # 序数列的模型内部折叠递归

零处取零，后继处配对此前编码与下一项。无可读后继的历史统一取零，使算子
在全部超限历史上有定义；有限序数列的后继方程随后排除这一补全分支。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Oc_read_d (F H b a : M.Domain) : Prop := ∃ n i,
  M.IsDomainOf I n H ∧ M.SuccessorOf n i ∧ M.IsOrdinal i ∧ M.PairMember I i b H ∧
    M.PairMember I i a F ∧ M.IsOrdinal b ∧ M.IsOrdinal a

def oc_read_m {d} (F H b a : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (Formula.isDomain 𝒞 (.bound 1) H.weaken.weaken) (.conj (Formula.isSuccessor (.bound 1) .newest)
    (.conj (Formula.isOrdinal .newest) (.conj (Formula.orderedPairMem 𝒞 .newest b.weaken.weaken H.weaken.weaken)
      (.conj (Formula.orderedPairMem 𝒞 .newest a.weaken.weaken F.weaken.weaken)
        (.conj (Formula.isOrdinal b.weaken.weaken) (Formula.isOrdinal a.weaken.weaken))))))))
derive_free_closed oc_read_m

theorem oc_read_sat_l {d} (ρ : Env M d) (F H b a : Term d) :
    Formula.satisfies ρ (oc_read_m (𝒞 := 𝒞) F H b a) ↔ Oc_read_d I (F.eval ρ) (H.eval ρ) (b.eval ρ) (a.eval ρ) := by
  simp only [oc_read_m, Oc_read_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

def Oc_step_d (F H c : M.Domain) : Prop := (∃ b a, Oc_read_d I F H b a ∧ Oc_pair_d I b a c) ∨
  ((¬ ∃ b a, Oc_read_d I F H b a) ∧ ∀ z, ¬ M.mem z c)

def oc_step_m {d} (F H c : Term d) : Formula 1 d := .disj
  (.existsE (.existsE (.conj (oc_read_m (𝒞 := 𝒞) F.weaken.weaken H.weaken.weaken (.bound 1) .newest)
    (oc_pair_m (𝒞 := 𝒞) (.bound 1) .newest c.weaken.weaken))))
  (.conj (.neg (.existsE (.existsE (oc_read_m (𝒞 := 𝒞) F.weaken.weaken H.weaken.weaken (.bound 1) .newest))))
    (Formula.isEmpty c))
derive_free_closed oc_step_m

theorem oc_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F H c : Term d) :
    Formula.satisfies ρ (oc_step_m (𝒞 := 𝒞) F H c) ↔ Oc_step_d I (F.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [oc_step_m, Oc_step_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, oc_read_sat_l I, oc_pair_sat_l I hE, Formula.satisfies_neg_iff,
    Formula.satisfies_isEmpty_iff, Definitional.Term.eval_weaken]
  rfl

def oc_step_s : BinarySchema 1 := { body := oc_step_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
def oc_env_l (F : M.Domain) : Env M 1 := ⟨fun _ => F, fun _ => F⟩

theorem oc_step_op_l (hE : Extensional M) (ρ : Env M 1) :
    (oc_step_s (𝒞 := 𝒞)).denote ρ = Oc_step_d I (ρ.bound 0) := by
  funext H c
  exact propext (oc_step_sat_l I hE ((ρ.push H).push c) (.bound 2) (.bound 1) .newest)

def Oc_fold_d (F n c : M.Domain) : Prop := M.IsRecursionValue I (Oc_step_d I F) n c
def oc_fold_m {d} (F n c : Term d) : Formula 1 d :=
  Formula.isRecursionValue 𝒞 (oc_step_s (𝒞 := 𝒞)) (Definitional.TermVector.singleton F) n c
derive_free_closed oc_fold_m

theorem oc_fold_sat_l (hE : Extensional M) {d} (ρ : Env M d) (F n c : Term d) :
    Formula.satisfies ρ (oc_fold_m (𝒞 := 𝒞) F n c) ↔ Oc_fold_d I (F.eval ρ) (n.eval ρ) (c.eval ρ) := by
  rw [oc_fold_m, Formula.satisfies_isRecursionValue_iff I hE, oc_step_op_l I hE]
  rfl

theorem oc_read_unique_l (hE : Extensional M) {F H a b x y}
    (hf : M.IsSetFunction I F) (hh : M.IsSetFunction I H)
    (h : Oc_read_d I F H b a) (g : Oc_read_d I F H y x) : b = y ∧ a = x := by
  obtain ⟨n, i, hn, hs, hi, hb, ha, _⟩ := h
  obtain ⟨m, j, hm, ht, _, hy, hx, _⟩ := g
  have eq := hn.eq hE hm; subst m
  have eq := hs.predecessor_eq hE hi ht; subst j
  exact ⟨hh.2 i b y hb hy, hf.2 i a x ha hx⟩

theorem oc_step_total_l (hZF : M.Models ZF) {F} (hf : M.IsSetFunction I F) :
    M.IsClassFunctionOnTransfiniteSequences I (Oc_step_d I F) := by
  classical
  intro H hH
  obtain ⟨n, _, hh, _⟩ := hH
  by_cases hr : ∃ b a, Oc_read_d I F H b a
  · obtain ⟨b, a, hba⟩ := hr
    have ho := hba
    obtain ⟨_, _, _, _, _, _, _, hb, ha⟩ := ho
    obtain ⟨c, hc⟩ := oc_pair_exists_l I hZF hb ha
    refine ⟨c, Or.inl ⟨b, a, hba, hc⟩, fun d hd => ?_⟩
    rcases hd with ⟨y, x, hyx, hd⟩ | ⟨hn, _⟩
    · obtain ⟨rfl, rfl⟩ := oc_read_unique_l I hZF.1 hf hh hba hyx
      exact oc_pair_unique_l I hZF hd hc
    · exact (hn ⟨b, a, hba⟩).elim
  · obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact ⟨e, Or.inr ⟨hr, he⟩, fun c hc => hc.elim (fun ⟨b, a, h, _⟩ => (hr ⟨b, a, h⟩).elim)
      (fun h => hZF.1.eq_of_same_members c e (fun z => iff_of_false (h.2 z) (he z)))⟩

theorem oc_fold_exists_l (hZF : M.Models ZF) {F n} (hf : M.IsSetFunction I F) (hn : M.IsOrdinal n) :
    ∃ c, Oc_fold_d I F n c := by
  have he : (oc_step_s (𝒞 := 𝒞)).denote (oc_env_l F) = Oc_step_d I F := oc_step_op_l I hZF.1 (oc_env_l F)
  have ht : M.IsClassFunctionOnTransfiniteSequences I ((oc_step_s (𝒞 := 𝒞)).denote (oc_env_l F)) :=
    he.symm ▸ oc_step_total_l I hZF hf
  simpa only [he, Oc_fold_d] using ZF.recursionValue_exists hZF I (oc_env_l F) (oc_step_s (𝒞 := 𝒞)) ht hn

theorem oc_fold_unique_l (hZF : M.Models ZF) {F n c d} (hf : M.IsSetFunction I F)
    (h : Oc_fold_d I F n c) (g : Oc_fold_d I F n d) : c = d := by
  have he : (oc_step_s (𝒞 := 𝒞)).denote (oc_env_l F) = Oc_step_d I F := oc_step_op_l I hZF.1 (oc_env_l F)
  have ht : M.IsClassFunctionOnTransfiniteSequences I ((oc_step_s (𝒞 := 𝒞)).denote (oc_env_l F)) :=
    he.symm ▸ oc_step_total_l I hZF hf
  exact ZF.recursionValue_unique hZF I (oc_env_l F) (oc_step_s (𝒞 := 𝒞)) ht
    (by simpa only [he, Oc_fold_d] using h) (by simpa only [he, Oc_fold_d] using g)

theorem oc_fold_ordinal_l (hZF : M.Models ZF) {F n c} (h : Oc_fold_d I F n c) : M.IsOrdinal c := by
  obtain ⟨_, _, h⟩ := h
  exact h.elim (fun ⟨_, _, _, hc⟩ => (oc_pair_types_l I hZF hc).2.2)
    (fun h => Structure.IsOrdinal.of_no_members h.2)

theorem oc_fold_zero_l {F e c} (he : ∀ z, ¬ M.mem z e) (h : Oc_fold_d I F e c) : ∀ z, ¬ M.mem z c := by
  obtain ⟨H, hh, h⟩ := h
  rcases h with ⟨b, a, hr, _⟩ | h
  · obtain ⟨n, i, _, _, _, hib, _⟩ := hr
    exact (he i ((hh.1.2.2 i).mpr ⟨b, hib⟩)).elim
  · exact h.2

/-- 合法后继精确读取最后一项和前缀编码，补全分支不参与编码。 -/
theorem oc_fold_succ_l (hZF : M.Models ZF) {F n s c a} (hf : M.IsSetFunction I F)
    (hs : M.SuccessorOf s n) (ha : M.IsOrdinal a) (hna : M.PairMember I n a F)
    (h : Oc_fold_d I F s c) : ∃ b, Oc_fold_d I F n b ∧ Oc_pair_d I b a c := by
  obtain ⟨H, hh, hc⟩ := h
  obtain ⟨b, hb⟩ := (hh.1.2.2 n).mp hs.predecessor_mem
  have hbn : Oc_fold_d I F n b := hh.recursionValue_of_pairMember hs.predecessor_mem hb
  have hr : Oc_read_d I F H b a := ⟨s, n, hh.1.2.2, hs, hh.1.1.mem hs.predecessor_mem,
    hb, hna, oc_fold_ordinal_l I hZF hbn, ha⟩
  rcases hc with ⟨b', a', hr', hbc⟩ | hc
  · obtain ⟨rfl, rfl⟩ := oc_read_unique_l I hZF.1 hf hh.1.2.1 hr hr'
    exact ⟨b, hbn, hbc⟩
  · exact (hc.1 ⟨b, a, hr⟩).elim

end YesMetaZFC.SetTheory
