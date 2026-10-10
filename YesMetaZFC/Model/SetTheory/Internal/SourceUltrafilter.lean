import YesMetaZFC.Model.SetTheory.Internal.SourcePower
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter

/-! # 源内部极大滤子的实际子集二择

只在载体的相对幂集中作一次单元素扩张。所需交集和扩张滤子都由
源内有界分离构造，因而不假定整个相对模型满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sf_maximal_relative_l {ω c X R : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : Nonempty {x // M.mem x X}) (D U P : (rt_model_l X hn).Domain)
    (power : Source_d X D.val P.val) (maximal : Maximal_d (ℳ := rt_model_l X hn) D U) :
    Sf_ultra_d X D.val U.val := by
  let N := rt_model_l X hn
  have sub (A B : N.Domain) : Subset_d (ℳ := N) A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun h x hx => h ⟨x, hX A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩
  have inter (A B : N.Domain) : ∃ C : N.Domain, ∀ x : N.Domain, N.mem x C ↔ N.mem x A ∧ N.mem x B := by
    let ρ : Env M 1 := ⟨fun _ => B.val, fun _ => B.val⟩
    let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨C, hC, hc⟩ := sc_separate_source_l I hZF hω hX hm theory φ (.mem ..) ρ (fun _ => B.property) A.property
    exact ⟨⟨C, hC⟩, fun x => (hc x.val).trans (and_congr_right fun _ => Formula.satisfies_mem_iff _ _ _)⟩
  have adjoin (B : N.Domain) (hB : Subset_d (ℳ := N) B D) : ∃ G : N.Domain,
      IsFilter_d (ℳ := N) D G ∧ Subset_d (ℳ := N) U G ∧ N.mem B G ∧ ∀ t : N.Domain,
      N.mem t G ↔ Subset_d (ℳ := N) t D ∧ ∃ s, N.mem s U ∧ ∀ x, N.mem x s → N.mem x B → N.mem x t := by
    let ρ : Env M 2 := ⟨Fin.cases B.val (fun _ => U.val), fun _ => D.val⟩
    let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (Formula.forallMem .newest
      (.imp (.mem .newest (.bound 3)) (.mem .newest (.bound 2)))) }
    have sat t : φ.denote ρ t ↔ ∃ s, M.mem s U.val ∧ ∀ x, M.mem x s → M.mem x B.val → M.mem x t := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
        Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]; rfl
    obtain ⟨G, hG, spec⟩ := sc_separate_source_l I hZF hω hX hm theory φ
      (.existsMem _ (.forallMem _ (.imp (.mem ..) (.mem ..)))) ρ (Fin.cases B.property (fun _ => U.property)) P.property
    have k (t : N.Domain) : M.mem t.val G ↔ Subset_d (ℳ := N) t D ∧
        ∃ s : N.Domain, N.mem s U ∧ ∀ x : N.Domain, N.mem x s → N.mem x B → N.mem x t := by
      rw [spec t.val, sat t.val, power t.val]
      constructor
      · rintro ⟨⟨_, ht⟩, s, hs, h⟩
        exact ⟨(sub t D).mpr ht, ⟨s, hX U.val U.property s hs⟩, hs, fun x hx hb => h x.val hx hb⟩
      · rintro ⟨ht, s, hs, h⟩
        exact ⟨⟨t.property, (sub t D).mp ht⟩, s.val, hs, fun x hx hb =>
          h ⟨x, hX s.val s.property x hx⟩ hx hb⟩
    refine ⟨⟨G, hG⟩, ⟨fun t ht => ((k t).mp ht).1,
      (k D).mpr ⟨fun _ hx => hx, D, maximal.1.2.1, fun _ hx _ => hx⟩, ?_, ?_⟩,
      fun s hs => (k s).mpr ⟨maximal.1.1 s hs, s, hs, fun _ hx _ => hx⟩,
      (k B).mpr ⟨hB, D, maximal.1.2.1, fun _ _ hx => hx⟩, k⟩
    · intro s t hs hst ht
      obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
      exact (k t).mpr ⟨ht, r, hr, fun x hx hb => hst x (h x hx hb)⟩
    · intro s t hs ht
      obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
      obtain ⟨q, hq, h'⟩ := ((k t).mp ht).2
      obtain ⟨v, hv, vr, vq⟩ := maximal.1.2.2.2 r q hr hq
      obtain ⟨w, hw⟩ := inter v B
      exact ⟨w, (k w).mpr ⟨fun x hx => hB x ((hw x).mp hx).2, v, hv, fun x hx hb => (hw x).mpr ⟨hx, hb⟩⟩,
        fun x hx => h x (vr x ((hw x).mp hx).1) ((hw x).mp hx).2,
        fun x hx => h' x (vq x ((hw x).mp hx).1) ((hw x).mp hx).2⟩
  have decides (A B : N.Domain) (ha : Subset_d (ℳ := N) A D)
      (hb : ∀ x, N.mem x B ↔ N.mem x D ∧ ¬ N.mem x A) : N.mem A U ∨ N.mem B U := by
    rcases Classical.em (N.mem B U) with h | h
    · exact Or.inr h
    · obtain ⟨G, hg, ug, ag, spec⟩ := adjoin A ha
      exact Or.inl (maximal.2.2 G hg (adjoin_proper_d maximal.1 hb spec h) ug A ag)
  have base : Base_d (ℳ := M) D.val U.val := by
    refine ⟨fun A hA => (sub ⟨A, hX U.val U.property A hA⟩ D).mp (maximal.1.1 _ hA), maximal.1.2.1, ?_⟩
    intro A B ha hb
    obtain ⟨C, hc, ca, cb⟩ := maximal.1.2.2.2 ⟨A, hX U.val U.property A ha⟩ ⟨B, hX U.val U.property B hb⟩ ha hb
    exact ⟨C.val, hc, (sub C _).mp ca, (sub C _).mp cb⟩
  refine ⟨base, ?_, ?_, ?_⟩
  · intro A ha
    obtain ⟨x, hx⟩ := maximal.2.1 ⟨A, hX U.val U.property A ha⟩ ha
    exact ⟨x.val, hx⟩
  · intro A B ha hb bd ab
    exact maximal.1.2.2.1 ⟨A, hX U.val U.property A ha⟩ ⟨B, hb⟩ ha ((sub _ _).mpr ab) ((sub _ _).mpr bd)
  · intro A B ha ad hb spec
    exact decides ⟨A, ha⟩ ⟨B, hb⟩ ((sub _ _).mpr ad) (fun x => spec x.val)

end YesMetaZFC.SetTheory.Internal
