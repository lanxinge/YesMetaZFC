import YesMetaZFC.SetTheory.Descriptive.Perfect.Geometry

/-! # 由自由实数决定的规范分裂路径

若左子柱集包含该实数就走左边，否则走右边。每个输入都有实际后继函数和
沿内部 ω 的轨道，后续闭性由有限段轨道的局部稳定性给出。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Hit_d (ω J L a x : M.Domain) : Prop := ∃ b, M.PairMember I a b L ∧ Pre_d I ω J b x
def hit_m {d} (ω J L a x : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 a.weaken .newest L.weaken) (pre_m (𝒞 := 𝒞) ω.weaken J.weaken .newest x.weaken))
derive_free_closed hit_m
theorem hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J L a x : Term d) :
    Formula.satisfies ρ (hit_m (𝒞 := 𝒞) ω J L a x) ↔ Hit_d I (ω.eval ρ) (J.eval ρ) (L.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [hit_m, Hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, pre_sat_l I hE, Definitional.Term.eval_weaken]; rfl
def Ws_d (ω J L R a b x : M.Domain) : Prop :=
  (Hit_d I ω J L a x ∧ M.PairMember I a b L) ∨ (¬ Hit_d I ω J L a x ∧ M.PairMember I a b R)
def ws_m {d} (ω J L R a b x : Term d) : Formula 1 d := .disj
  (.conj (hit_m (𝒞 := 𝒞) ω J L a x) (Formula.orderedPairMem 𝒞 a b L))
  (.conj (.neg (hit_m (𝒞 := 𝒞) ω J L a x)) (Formula.orderedPairMem 𝒞 a b R))
derive_free_closed ws_m
theorem ws_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J L R a b x : Term d) :
    Formula.satisfies ρ (ws_m (𝒞 := 𝒞) ω J L R a b x) ↔
      Ws_d I (ω.eval ρ) (J.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (b.eval ρ) (x.eval ρ) := by
  simp only [ws_m, Ws_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    hit_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff]
def Sel_d (ω J U L R x F : M.Domain) : Prop := M.IsSetFunctionFromTo I F U U ∧
  ∀ a b, M.PairMember I a b F ↔ M.mem a U ∧ Ws_d I ω J L R a b x
def sel_m {d} (ω J U L R x F : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 F U U)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
  (.conj (.mem (.bound 1) U.weaken.weaken)
    (ws_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken L.weaken.weaken R.weaken.weaken (.bound 1) .newest x.weaken.weaken)))))
derive_free_closed sel_m
theorem sel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R x F : Term d) :
    Formula.satisfies ρ (sel_m (𝒞 := 𝒞) ω J U L R x F) ↔
      Sel_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (x.eval ρ) (F.eval ρ) := by
  simp only [sel_m, Sel_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, ws_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem sel_exists_l (hZF : M.Models ZF) {ω A J U L R} (hs : Split_d I ω A J U L R) (x : M.Domain) :
    ∃ F, Sel_d I ω J U L R x F := by
  classical
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push L).push R).push x
  let φ : BinarySchema 5 := { body := ws_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest (.bound 2) }
  have hp a b : φ.denote ρ a b ↔ Ws_d I ω J L R a b x := ws_sat_l I hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := U) (target := U) (by
    intro a ha
    by_cases h : Hit_d I ω J L a x
    · obtain ⟨b, _, hb⟩ := hs.2.1.2.2 a ha
      exact ⟨b, (hp a b).mpr (Or.inl ⟨h, hb⟩)⟩
    · obtain ⟨b, _, hb⟩ := hs.2.2.1.2.2 a ha
      exact ⟨b, (hp a b).mpr (Or.inr ⟨h, hb⟩)⟩) (by
    intro a _ b c hb hc
    rcases (hp a b).mp hb with ⟨h, hb⟩ | ⟨h, hb⟩ <;> rcases (hp a c).mp hc with ⟨k, hc⟩ | ⟨k, hc⟩
    · exact hs.2.1.1.2 a b c hb hc
    · exact (k h).elim
    · exact (h k).elim
    · exact hs.2.2.1.1.2 a b c hb hc) (fun a b _ h => ((hp a b).mp h).elim
      (fun h => hs.2.1.output_mem_of_pairMember h.2) (fun h => hs.2.2.1.output_mem_of_pairMember h.2))
  exact ⟨F, hf, fun a b => (ef a b).trans (and_congr_right fun _ => hp a b)⟩
theorem sel_unique_l (hE : Extensional M) {ω J U L R x F G}
    (h : Sel_d I ω J U L R x F) (k : Sel_d I ω J U L R x G) : F = G :=
  h.1.1.1.eq_of_pairMember_iff hE k.1.1.1 (fun a b => (h.2 a b).trans (k.2 a b).symm)

def Walk_d (ω J U L R a n b x : M.Domain) : Prop := ∃ F, Sel_d I ω J U L R x F ∧ Iv_d I ω U F a n b
def walk_m {d} (ω J U L R a n b x : Term d) : Formula 1 d := .existsE (.conj
  (sel_m (𝒞 := 𝒞) ω.weaken J.weaken U.weaken L.weaken R.weaken x.weaken .newest)
  (iv_m (𝒞 := 𝒞) ω.weaken U.weaken .newest a.weaken n.weaken b.weaken))
derive_free_closed walk_m
theorem walk_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R a n b x : Term d) :
    Formula.satisfies ρ (walk_m (𝒞 := 𝒞) ω J U L R a n b x) ↔
      Walk_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (n.eval ρ) (b.eval ρ) (x.eval ρ) := by
  simp only [walk_m, Walk_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sel_sat_l I hE, iv_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem walk_bound_l {ω J U L R a n b x} (h : Walk_d I ω J U L R a n b x) : M.mem b U :=
  h.elim fun _ h => iv_bound_l I h.2
theorem walk_fixed_l (hE : Extensional M) {ω J U L R a n b x F} (hf : Sel_d I ω J U L R x F) :
    Walk_d I ω J U L R a n b x ↔ Iv_d I ω U F a n b := by
  exact ⟨fun ⟨G, hg, h⟩ => sel_unique_l I hE hg hf ▸ h, fun h => ⟨F, hf, h⟩⟩
theorem walk_exists_l (hZF : M.Models ZF) {ω A J U L R a n} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (hn : M.mem n ω) (x : M.Domain) : ∃ b, Walk_d I ω J U L R a n b x := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  exact (iv_exists_l I hZF hω hf.1 ha hn).imp fun b h => ⟨F, hf, h⟩
theorem walk_zero_l (hZF : M.Models ZF) {ω A J U L R a z b x} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (hz : ∀ p, ¬ M.mem p z) :
    Walk_d I ω J U L R a z b x ↔ b = a := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  exact (walk_fixed_l I hZF.1 hf).trans (iv_zero_l I hZF hω hf.1 ha hz)
theorem walk_succ_l (hZF : M.Models ZF) {ω J U L R a n m b x} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Walk_d I ω J U L R a m b x ↔
      ∃ c, Walk_d I ω J U L R a n c x ∧ Ws_d I ω J L R c b x := by
  constructor
  · rintro ⟨F, hf, h⟩
    obtain ⟨c, hc, hb⟩ := (iv_succ_l I hZF hω hf.1.1 hn hm).mp h
    exact ⟨c, ⟨F, hf, hc⟩, ((hf.2 c b).mp hb).2⟩
  · rintro ⟨c, ⟨F, hf, hc⟩, hb⟩
    exact ⟨F, hf, (iv_succ_l I hZF hω hf.1.1 hn hm).mpr ⟨c, hc, (hf.2 c b).mpr ⟨iv_bound_l I hc, hb⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive
