import YesMetaZFC.SetTheory.Descriptive.Topology.Continuous

/-! # 内部函数迭代及首步交换

连续码替换要在每个量词下提升自由变量映射。迭代指标是内部 ω，
两种后继分解分别剥去最后一步和最初一步。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def It_d (ω X F a H : M.Domain) : Prop := M.IsSetFunctionFromTo I H ω X ∧
  (∀ z, (∀ x, ¬ M.mem x z) → M.PairMember I z a H) ∧
  ∀ n m x y, M.SuccessorOf m n → M.PairMember I n x H → M.PairMember I m y H → M.PairMember I x y F
def it_m {d} (ω X F a H : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 H ω X) (.conj
  (.forallE (.imp (Formula.isEmpty .newest) (Formula.orderedPairMem 𝒞 .newest a.weaken H.weaken)))
  (.forallE (.forallE (.forallE (.forallE (.imp (Formula.isSuccessor (.bound 2) (.bound 3))
    (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken.weaken)))))))))
derive_free_closed it_m
theorem it_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X F a H : Term d) :
    Formula.satisfies ρ (it_m (𝒞 := 𝒞) ω X F a H) ↔ It_d I (ω.eval ρ) (X.eval ρ) (F.eval ρ) (a.eval ρ) (H.eval ρ) := by
  simp only [it_m, It_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Iv_d (ω X F a n b : M.Domain) : Prop := ∃ H, It_d I ω X F a H ∧ M.PairMember I n b H
def iv_m {d} (ω X F a n b : Term d) : Formula 1 d := .existsE (.conj
  (it_m (𝒞 := 𝒞) ω.weaken X.weaken F.weaken a.weaken .newest)
  (Formula.orderedPairMem 𝒞 n.weaken b.weaken .newest))
derive_free_closed iv_m
theorem iv_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X F a n b : Term d) :
    Formula.satisfies ρ (iv_m (𝒞 := 𝒞) ω X F a n b) ↔
      Iv_d I (ω.eval ρ) (X.eval ρ) (F.eval ρ) (a.eval ρ) (n.eval ρ) (b.eval ρ) := by
  simp only [iv_m, Iv_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem iv_exists_l (hZF : M.Models ZF) {ω X F a n} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I F X X) (ha : M.mem a X) (hn : M.mem n ω) : ∃ b, Iv_d I ω X F a n b := by
  obtain ⟨H, hH, hz, hs⟩ := ZFC.iterate_l I hZF hω hf ha
  obtain ⟨b, _, hb⟩ := hH.2.2 n hn
  exact ⟨b, H, ⟨hH, hz, hs⟩, hb⟩

theorem iv_bound_l {ω X F a n b} (h : Iv_d I ω X F a n b) : M.mem b X :=
  h.elim fun _ h => h.1.1.output_mem_of_pairMember h.2

theorem iv_unique_l (hZF : M.Models ZF) {ω X F a n b c} (hω : M.IsOmega ω)
    (hf : M.IsSetFunction I F) (h : Iv_d I ω X F a n b) (k : Iv_d I ω X F a n c) : b = c := by
  obtain ⟨H, hH, hb⟩ := h
  obtain ⟨G, hG, hc⟩ := k
  let ρ : Env M 2 := (⟨fun _ => H, fun _ => H⟩ : Env M 1).push G
  let φ : UnarySchema 2 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.extensionalEq (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ x y, M.PairMember I n x H → M.PairMember I n y G → x = y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all : ∀ n, M.mem n ω → ∀ x y, M.PairMember I n x H → M.PairMember I n y G → x = y := by
    apply hω.induction
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
    · intro z hz x y hx hy
      exact (hH.1.1.2 z x a hx (hH.2.1 z hz)).trans (hG.1.1.2 z a y (hG.2.1 z hz) hy)
    · intro n hn ih m hm x y hx hy
      obtain ⟨u, _, hu⟩ := hH.1.2.2 n hn
      obtain ⟨v, _, hv⟩ := hG.1.2.2 n hn
      exact hf.2 u x y (hH.2.2 n m u x hm hu hx) (ih u v hu hv ▸ hG.2.2 n m v y hm hv hy)
  exact all n (hH.1.input_mem_of_pairMember hb) b c hb hc

theorem iv_zero_l (hZF : M.Models ZF) {ω X F a z b} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I F X X) (ha : M.mem a X) (hz : ∀ x, ¬ M.mem x z) :
    Iv_d I ω X F a z b ↔ b = a := by
  constructor
  · rintro ⟨H, hH, hb⟩
    exact hH.1.1.2 z b a hb (hH.2.1 z hz)
  · rintro rfl
    obtain ⟨H, hH, hz', hs⟩ := ZFC.iterate_l I hZF hω hf ha
    exact ⟨H, ⟨hH, hz', hs⟩, hz' z hz⟩

theorem iv_succ_l (hZF : M.Models ZF) {ω X F a n m b} (hω : M.IsOmega ω)
    (hf : M.IsSetFunction I F) (hn : M.mem n ω) (hm : M.SuccessorOf m n) :
    Iv_d I ω X F a m b ↔ ∃ c, Iv_d I ω X F a n c ∧ M.PairMember I c b F := by
  constructor
  · rintro ⟨H, hH, hb⟩
    obtain ⟨c, _, hc⟩ := hH.1.2.2 n hn
    exact ⟨c, ⟨H, hH, hc⟩, hH.2.2 n m c b hm hc hb⟩
  · rintro ⟨c, ⟨H, hH, hc⟩, hcb⟩
    obtain ⟨m', hm', hmω⟩ := hω.1.2 n hn
    have hmω := Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hmω
    obtain ⟨b', _, hb⟩ := hH.1.2.2 m hmω
    exact ⟨H, hH, hf.2 c b' b (hH.2.2 n m c b' hm hc hb) hcb ▸ hb⟩

/-- 用 F∘H 移动整个内部轨道，得到剥去首步的后继方程。 -/
theorem iv_shift_l (hZF : M.Models ZF) {ω X F a a' n m b} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I F X X) (hn : M.mem n ω) (hm : M.SuccessorOf m n)
    (haa : M.PairMember I a a' F) : Iv_d I ω X F a m b ↔ Iv_d I ω X F a' n b := by
  have shift {b} (h : Iv_d I ω X F a m b) : Iv_d I ω X F a' n b := by
    obtain ⟨H, hH, hb⟩ := h
    obtain ⟨G, hG, eg⟩ := ZF.exists_compositionFunction hZF I hH.1 hf
    have it : It_d I ω X F a' G := by
      refine ⟨hG, fun z hz => (eg z a').mpr ⟨hH.1.input_mem_of_pairMember (hH.2.1 z hz), a, hH.2.1 z hz, haa⟩, ?_⟩
      intro i j x y hij hx hy
      obtain ⟨_, u, hu, hux⟩ := (eg i x).mp hx
      obtain ⟨_, v, hv, hvy⟩ := (eg j y).mp hy
      exact (hf.1.2 u v x (hH.2.2 i j u v hij hu hv) hux) ▸ hvy
    obtain ⟨c, _, hc⟩ := hH.1.2.2 n hn
    exact ⟨G, it, (eg n b).mpr ⟨hn, c, hc, hH.2.2 n m c b hm hc hb⟩⟩
  refine ⟨shift, fun h => ?_⟩
  obtain ⟨m', hm', hmω⟩ := hω.1.2 n hn
  have hmω := Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hmω
  obtain ⟨c, hc⟩ := iv_exists_l I hZF hω hf (hf.input_mem_of_pairMember haa) hmω
  exact iv_unique_l I hZF hω hf.1 (shift hc) h ▸ hc

end YesMetaZFC.SetTheory.Descriptive
