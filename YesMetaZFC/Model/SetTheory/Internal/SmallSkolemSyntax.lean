import YesMetaZFC.Model.SetTheory.Internal.FiniteWitness
import YesMetaZFC.SetTheory.FinitaryHullSyntax
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 小 Skolem 壳的有界结构数据

运算闭性只检查已有的有限参数空间与选择图。枚举是实际双射图；其
有界公式能在传递源与背景之间直接读取，不诉诸外部基数正确性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sh_product_m {d} (P A B : Term d) : Formula 1 d :=
  .conj (Formula.forallMem P (Formula.existsMem A.weaken (Formula.existsMem B.weaken.weaken
    (kpair0_m (.bound 2) (.bound 1) .newest))))
    (Formula.forallMem A (Formula.forallMem B.weaken (Formula.existsMem P.weaken.weaken
      (kpair0_m .newest (.bound 2) (.bound 1)))))
derive_free_closed sh_product_m

theorem sh_product_delta_l {d} (P A B : Term d) : (sh_product_m P A B).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.existsMem _ (kpair0_delta_l ..))))

theorem sh_product_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (P A B : Term d) :
    Formula.satisfies ρ (sh_product_m P A B) ↔
      M.IsCartesianProduct (kp_pair_l hKP) (P.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [sh_product_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]
  refine ⟨fun h p => ⟨h.1 p, ?_⟩, fun h => ⟨fun p hp => (h p).mp hp, ?_⟩⟩
  · rintro ⟨a, ha, b, hb, hp⟩
    obtain ⟨q, hq, code⟩ := h.2 a ha b hb
    exact kpair_unique_l M hKP.1 code hp ▸ hq
  · intro a ha b hb
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total a b
    exact ⟨p, (h p).mpr ⟨a, ha, b, hb, hp⟩, hp⟩

def sh_bijection_m {d} (f A B : Term d) : Formula 1 d := .conj (fn0_m A B f)
  (.conj (Formula.forallMem A (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken)
        (Formula.extensionalEq (.bound 2) (.bound 1)))))))
    (Formula.forallMem B (Formula.existsMem A.weaken (rd_entry0_m .newest (.bound 1) f.weaken.weaken))))
derive_free_closed sh_bijection_m

theorem sh_bijection_delta_l {d} (f A B : Term d) : (sh_bijection_m f A B).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom _ _ _))))))
    (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..))))

theorem sh_bijection_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (f A B : Term d) :
    Formula.satisfies ρ (sh_bijection_m f A B) ↔
      M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [sh_bijection_m, Formula.satisfies_conj_iff, fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hf, hi, ho⟩ => ⟨⟨fn0_function_l hKP hf,
    fun a b x ha hb => hi a (hf.bound_l ha).1 b (hf.bound_l hb).1 x (hf.bound_l ha).2 ha hb⟩, ho⟩,
    fun hf => ⟨fn0_of_function_l hKP hf.1.1, fun a _ b _ x _ => hf.1.2 a b x, hf.2⟩⟩

def sh_value_m {d} (ω J T D K B x : Term d) : Formula 1 d :=
  Formula.existsMem ω (Formula.existsMem J.weaken (Formula.existsMem T.weaken.weaken
    (Formula.existsMem D.weaken.weaken.weaken (.conj
      (fn0_m (.bound 3) B.weaken.weaken.weaken.weaken (.bound 2)) (.conj
      (kpair0_m .newest (.bound 1) (.bound 2))
      (rd_entry0_m .newest x.weaken.weaken.weaken.weaken K.weaken.weaken.weaken.weaken))))))
derive_free_closed sh_value_m

theorem sh_value_delta_l {d} (ω J T D K B x : Term d) : (sh_value_m ω J T D K B x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))))

theorem sh_value_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω J T D K B x : Term d) :
    Formula.satisfies ρ (sh_value_m ω J T D K B x) ↔
      ∃ n, M.mem n (ω.eval ρ) ∧ ∃ s, M.mem s (J.eval ρ) ∧ ∃ t, M.mem t (T.eval ρ) ∧
        ∃ p, M.mem p (D.eval ρ) ∧ Fn0_d n (B.eval ρ) s ∧ KPair_d M p t s ∧ Rd_entry_d p (x.eval ρ) (K.eval ρ) := by
  simp only [sh_value_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

def sh_closed_m {d} (ω A J T D K B : Term d) : Formula 1 d := Formula.forallMem A
  (.imp (sh_value_m ω.weaken J.weaken T.weaken D.weaken K.weaken B.weaken .newest) (.mem .newest B.weaken))
derive_free_closed sh_closed_m

theorem sh_closed_delta_l {d} (ω A J T D K B : Term d) : (sh_closed_m ω A J T D K B).IsDelta0 :=
  .forallMem _ (.imp (sh_value_delta_l ..) (.mem _ _))

theorem sh_closed_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A J T D K B : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (A.eval ρ) (J.eval ρ))
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ) (T.eval ρ) (J.eval ρ))
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ) (D.eval ρ) (A.eval ρ))
    (hB : M.MemberSubset (B.eval ρ) (A.eval ρ)) :
    Formula.satisfies ρ (sh_closed_m ω A J T D K B) ↔
      Fc_closed_d (kp_pair_l hKP) (ω.eval ρ) (T.eval ρ) (K.eval ρ) (B.eval ρ) := by
  simp only [sh_closed_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    sh_value_sat_l hKP, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  refine ⟨fun h x hx => ?_, fun h x _ ⟨n, hn, s, _, t, ht, p, _, hs, hp, hx⟩ =>
    h x ⟨n, s, t, p, hn, fn0_function_l hKP hs, ht, hp, hx⟩⟩
  obtain ⟨n, s, t, p, hn, hs, ht, hp, hx⟩ := hx
  have hsJ := (hJ s).mpr ⟨n, hn, hs.mono_target_l _ hB⟩
  exact h x (hK.output_mem_of_pairMember hx)
    ⟨n, hn, s, hsJ, t, ht, p, (hD p).mpr ⟨t, ht, s, hsJ, hp⟩, fn0_of_function_l hKP hs, hp, hx⟩

def sh_codes_m {d} (ω C : Term d) : Formula 1 d := .forallE (.iff (.mem .newest C.weaken)
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (fb_program_m ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.conj (.mem .newest (.bound 3)) (kpair0_m (.bound 5) (.bound 1) .newest)))))))))
derive_free_closed sh_codes_m

def sh_sequences_m {d} (ω A J : Term d) : Formula 1 d := .forallE (.iff (.mem .newest J.weaken)
  (Formula.existsMem ω.weaken (fn0_m .newest A.weaken.weaken (.bound 1))))
derive_free_closed sh_sequences_m

def sh_choice_m {d} (ω A R J u a i s x : Term d) : Formula 1 d :=
  .disj (fw_witness_m ω A R J u a i s x)
    (.conj (Formula.forallMem A (.neg (fw_witness_m ω.weaken A.weaken R.weaken J.weaken
      u.weaken a.weaken i.weaken s.weaken .newest))) (Formula.extensionalEq x u))
derive_free_closed sh_choice_m

def sh_select_m {d} (ω A R u C J T D K : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken
  Formula.forallMem C (Formula.forallMem ω.weaken (Formula.forallMem T.weaken.weaken
    (Formula.forallMem J.weaken.weaken.weaken (Formula.forallMem D.weaken.weaken.weaken.weaken
      (Formula.forallMem A.weaken.weaken.weaken.weaken.weaken
        (.imp (kpair0_m (.bound 3) (.bound 5) (.bound 4)) (.imp (kpair0_m (.bound 1) (.bound 3) (.bound 2))
          (.imp (rd_entry0_m (.bound 1) .newest (w K))
            (sh_choice_m (w ω) (w A) (w R) (w J) (w u) (.bound 5) (.bound 4) (.bound 2) .newest)))))))))
derive_free_closed sh_select_m

def sh_skolem_m {d} (ω A R u C J T D K : Term d) : Formula 1 d :=
  .conj (.mem u A) (.conj (sh_codes_m ω C) (.conj (sh_sequences_m ω A J)
    (.conj (sh_product_m T C ω) (.conj (sh_product_m D T J)
      (.conj (fn0_m D A K) (sh_select_m ω A R u C J T D K))))))
derive_free_closed sh_skolem_m

def Sh_hull_d (hKP : M.Models KP) (Z ω A T K U N : M.Domain) : Prop :=
  M.MemberSubset U N ∧ M.MemberSubset N A ∧ Fc_closed_d (kp_pair_l hKP) ω T K N ∧
    ∀ B, M.mem B Z → M.MemberSubset U B → M.MemberSubset B A →
      Fc_closed_d (kp_pair_l hKP) ω T K B → M.MemberSubset N B

def sh_hull_m {d} (ω A J T D K U N : Term d) : Formula 1 d :=
  .conj (Formula.subset U N) (.conj (Formula.subset N A) (.conj (sh_closed_m ω A J T D K N)
    (.forallE (.imp (Formula.subset U.weaken .newest) (.imp (Formula.subset .newest A.weaken)
      (.imp (sh_closed_m ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest)
        (Formula.subset N.weaken .newest)))))))
derive_free_closed sh_hull_m

def sh_input_m {d} (ω A R U κ f : Term d) : Formula 1 d :=
  .conj (KP.ord0_m κ) (.conj (Formula.subset ω κ) (.conj (Formula.subset U A)
    (.conj (sh_bijection_m f κ U) (Formula.forallMem R
      (Formula.existsMem A.weaken (Formula.existsMem A.weaken.weaken (kpair0_m (.bound 2) (.bound 1) .newest)))))))
derive_free_closed sh_input_m

theorem sh_input_delta_l {d} (ω A R U κ f : Term d) : (sh_input_m ω A R U κ f).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (.atom _ _ _) (.conj (.atom _ _ _)
    (.conj (sh_bijection_delta_l ..) (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))))))

theorem sh_input_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A R U κ f : Term d) :
    Formula.satisfies ρ (sh_input_m ω A R U κ f) ↔
      M.IsOrdinal (κ.eval ρ) ∧ M.MemberSubset (ω.eval ρ) (κ.eval ρ) ∧ M.MemberSubset (U.eval ρ) (A.eval ρ) ∧
        M.IsSetBijectionFromTo (kp_pair_l hKP) (f.eval ρ) (κ.eval ρ) (U.eval ρ) ∧
          M.IsSetRelationOn (kp_pair_l hKP) (R.eval ρ) (A.eval ρ) := by
  simp only [sh_input_m, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP,
    Formula.satisfies_subset_iff, sh_bijection_sat_l hKP, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]
  apply and_congr_right; intro _; apply and_congr_right; intro _
  apply and_congr_right; intro _; apply and_congr_right; intro _
  refine ⟨fun h => ⟨fun p hp => (h p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, b, hb.2⟩, ?_⟩, ?_⟩
  · rintro a b ⟨p, hp, hpr⟩
    obtain ⟨x, hx, y, hy, code⟩ := h p hpr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code hp
    exact ⟨hx, hy⟩
  · intro h p hp
    obtain ⟨a, b, code⟩ := h.1 p hp
    exact ⟨a, (h.2 a b ⟨p, code, hp⟩).1, b, (h.2 a b ⟨p, code, hp⟩).2, code⟩

def Sh_data_d (hKP : M.Models KP) (Z ω c A U κ : M.Domain) : Prop :=
  ∃ u C J T D K N f, M.mem u Z ∧ M.mem C Z ∧ M.mem J Z ∧ M.mem T Z ∧ M.mem D Z ∧ M.mem K Z ∧
    M.mem N Z ∧ M.mem f Z ∧ Ssk_d (kp_pair_l hKP) ω c A u C J T D K ∧
      Sh_hull_d hKP Z ω A T K U N ∧ M.IsSetBijectionFromTo (kp_pair_l hKP) f κ N

def Sh_source_d (hKP : M.Models KP) (ω Z : M.Domain) : Prop := ∀ c A R U κ f,
  M.mem A Z → M.mem R Z → M.mem U Z → M.mem κ Z → M.mem f Z → Smdl_d (kp_pair_l hKP) c A R →
    M.IsOrdinal κ → M.MemberSubset ω κ → M.MemberSubset U A →
      M.IsSetBijectionFromTo (kp_pair_l hKP) f κ U → Sh_data_d hKP Z ω c A U κ

def sh_output_m {d} (ω A R U κ : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (sh_skolem_m (w ω) (w A) (w R) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
      (.conj (sh_hull_m (w ω) (w A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (w U) (.bound 1))
        (sh_bijection_m .newest (w κ) (.bound 1)))))))))))
derive_free_closed sh_output_m

def sh_source_m {d} (ω : Term d) : Formula 1 d := .forallE (.forallE (.forallE (.forallE (.forallE
  (.imp (sh_input_m ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (sh_output_m ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1)))))))
derive_free_closed sh_source_m

end YesMetaZFC.SetTheory.Internal
