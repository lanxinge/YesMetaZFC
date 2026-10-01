import YesMetaZFC.Model.SetTheory.Internal.Source

/-! # 内部公式程序的可组合构造

每次构造返回实际合法程序、旧程序的精确前缀及新根位置。布尔构造复用或非
指令，语义规格对任意模型与赋值同时成立；没有把预期真值作为构造假设。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sbuild_d (ω n F m G k : M.Domain) : Prop where
  program : Sfm_d I ω m G
  cut : M.IsRestrictionOf I F G n
  span : M.MemberSubset n m
  root : M.mem k m

theorem Sbuild_d.comp {ω n F m G k l H r} (h : Sbuild_d I ω n F m G k)
    (g : Sbuild_d I ω m G l H r) : Sbuild_d I ω n F l H r := by
  refine ⟨g.program, ⟨h.cut.1, fun i a => ?_⟩, fun i hi => g.span i (h.span i hi), g.root⟩
  exact (h.cut.2 i a).trans ⟨fun hi => ⟨hi.1, ((g.cut.2 i a).mp hi.2).2⟩,
    fun hi => ⟨hi.1, (g.cut.2 i a).mpr ⟨h.span i hi.1, hi.2⟩⟩⟩

theorem Sbuild_d.sat_l (hZF : M.Models ZF) {ω n F m G k i} (hF : Sfm_d I ω n F)
    (h : Sbuild_d I ω n F m G k) (hi : M.mem i n) (X R E f : M.Domain) :
    Ssat_d I X R E F n i f ↔ Ssat_d I X R E G m i f := ssat_prefix_l I hZF hF h.program h.cut hi f

theorem sfm_node_build_l (hZF : M.Models ZF) {ω n F c} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hc : Sfm_node_d I ω n c) :
    ∃ m G, Sbuild_d I ω n F m G n ∧ M.PairMember I n c G := by
  obtain ⟨m, G, hm, hG, he⟩ := sfm_append_l I hZF hω hF hc
  have hp := sfm_append_prefix_l I hZF hF he
  exact ⟨m, G, ⟨hG, hp, sfm_prefix_subset_l I hF hG hp, hm.predecessor_mem⟩,
    (he n c).mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem sfm_nor_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ¬ (Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f)) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 2 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inr (Or.inl ⟨i, j, hc, hi, hj⟩)))
  refine ⟨m, G, n, h, fun X R E f hf => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact (ssat_nor_l I hZF h.program hH he hc hf).trans
    (not_congr (or_congr (h.sat_l I hZF hF hi X R E f).symm (h.sat_l I hZF hF hj X R E f).symm))

theorem sfm_neg_l (hZF : M.Models ZF) {ω n F i} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ¬ Ssat_d I X R E F n i f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_nor_l I hZF hω hF hi hi
  exact ⟨m, G, k, h, fun X R E f hf => (he X R E f hf).trans (not_congr ⟨fun h => h.elim id id, Or.inl⟩)⟩

theorem sfm_or_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_nor_l I hZF hω hF hi hj
  obtain ⟨l, H, r, g, hg⟩ := sfm_neg_l I hZF hω h.program h.root
  refine ⟨l, H, r, h.comp I g, fun X R E f hf => ?_⟩
  exact (hg X R E f hf).trans ((not_congr (he X R E f hf)).trans Classical.not_not)

theorem sfm_and_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ Ssat_d I X R E F n i f ∧ Ssat_d I X R E F n j f) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_neg_l I hZF hω hF hi
  obtain ⟨l, H, r, g, hg⟩ := sfm_neg_l I hZF hω h.program (h.span j hj)
  obtain ⟨v, J, s, b, hb⟩ := sfm_nor_l I hZF hω g.program (g.span k h.root) g.root
  refine ⟨v, J, s, (h.comp I g).comp I b, fun X R E f hf => ?_⟩
  rw [hb X R E f hf, ← g.sat_l I hZF h.program h.root X R E f, he X R E f hf,
    hg X R E f hf, ← h.sat_l I hZF hF hj X R E f]
  classical
  simp only [not_or, Classical.not_not]

theorem sfm_imp_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ (Ssat_d I X R E F n i f → Ssat_d I X R E F n j f)) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_neg_l I hZF hω hF hi
  obtain ⟨l, H, r, g, hg⟩ := sfm_or_l I hZF hω h.program h.root (h.span j hj)
  refine ⟨l, H, r, h.comp I g, fun X R E f hf => ?_⟩
  rw [hg X R E f hf, he X R E f hf, ← h.sat_l I hZF hF hj X R E f]
  classical
  exact ⟨fun h hp => h.elim (fun hn => (hn hp).elim) id, fun h => by
    by_cases hp : Ssat_d I X R E F n i f
    · exact Or.inr (h hp)
    · exact Or.inl hp⟩

theorem sfm_iff_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i n) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ (Ssat_d I X R E F n i f ↔ Ssat_d I X R E F n j f)) := by
  obtain ⟨m, G, k, h, he⟩ := sfm_imp_l I hZF hω hF hi hj
  obtain ⟨l, H, r, g, hg⟩ := sfm_imp_l I hZF hω h.program (h.span j hj) (h.span i hi)
  obtain ⟨v, J, s, b, hb⟩ := sfm_and_l I hZF hω g.program (g.span k h.root) g.root
  refine ⟨v, J, s, (h.comp I g).comp I b, fun X R E f hf => ?_⟩
  rw [hb X R E f hf, ← g.sat_l I hZF h.program h.root X R E f, he X R E f hf,
    hg X R E f hf, ← h.sat_l I hZF hF hj X R E f, ← h.sat_l I hZF hF hi X R E f]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem sfm_ex_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j n) : ∃ m G k,
    Sbuild_d I ω n F m G k ∧ ∀ X R E f, M.mem f E →
      (Ssat_d I X R E G m k f ↔ ∃ x g,
        M.mem x X ∧ Senv_update_d I f i x g ∧ Ssat_d I X R E F n j g) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 3 i j
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inr (Or.inr ⟨i, j, hc, hi, hj⟩)))
  refine ⟨m, G, n, h, fun X R E f hf => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  exact (ssat_exists_l I hZF h.program hH he hc hf).trans (exists_congr fun x => exists_congr fun g =>
    and_congr_right fun _ => and_congr_right fun _ => (h.sat_l I hZF hF hj X R E g).symm)

end YesMetaZFC.SetTheory.Internal
