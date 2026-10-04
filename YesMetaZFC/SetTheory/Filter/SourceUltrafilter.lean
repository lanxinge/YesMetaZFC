import YesMetaZFC.SetTheory.Filter.Source

/-! # 在指定模型的子集上决定的滤基

允许原测度还包含模型外的集合；商只读取模型内真值集。完整超滤和
严格相对超滤均为实际实例，限制到源代数后保留原成员判定。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure Sf_ultra_d (X D U : M.Domain) : Prop where
  base : Base_d D U
  proper : ∀ A, M.mem A U → ∃ x, M.mem x A
  upward : ∀ A B, M.mem A U → M.mem B X → M.MemberSubset B D → M.MemberSubset A B → M.mem B U
  decides : ∀ A B, M.mem A X → M.MemberSubset A D → M.mem B X →
    (∀ x, M.mem x B ↔ M.mem x D ∧ ¬ M.mem x A) → M.mem A U ∨ M.mem B U

theorem Maximal_d.source_l (hZF : M.Models ZF) {D U : M.Domain}
    (h : Maximal_d (ℳ := M) D U) (X : M.Domain) : Sf_ultra_d X D U :=
  ⟨h.1.base_l, h.2.1, fun A B ha _ hb hab => h.1.2.2.1 A B ha hab hb,
    fun _ _ _ ha _ hc => maximal_decides_d hZF h ha hc⟩

theorem Rel_ultra_d.source_l {X D P U : M.Domain} (h : Rel_ultra_d D P U)
    (hp : Source_d X D P) : Sf_ultra_d X D U :=
  ⟨h.base, h.proper, fun A B ha hb sub hab => h.upward A B ha ((hp B).mpr ⟨hb, sub⟩) hab,
    fun A B ha sub hb hc => h.decides A B ((hp A).mpr ⟨ha, sub⟩)
      ((hp B).mpr ⟨hb, fun x hx => ((hc x).mp hx).1⟩) hc⟩

/-- 子集一致性足以让同一测度施加到另一模型；不传递背景完备性。 -/
theorem Sf_ultra_d.transfer_l {X Y D U : M.Domain} (h : Sf_ultra_d X D U)
    (agree : ∀ A, M.MemberSubset A D → (M.mem A X ↔ M.mem A Y)) : Sf_ultra_d Y D U :=
  ⟨h.base, h.proper, fun A B ha hb sub hab => h.upward A B ha ((agree B sub).mpr hb) sub hab,
    fun A B ha sub hb hc => h.decides A B ((agree A sub).mpr ha) sub
      ((agree B (fun x hx => ((hc x).mp hx).1)).mpr hb) hc⟩

theorem Sf_ultra_d.restrict_l (hKP : M.Models KP) {X D P U : M.Domain} (h : Sf_ultra_d X D U)
    (hp : Source_d X D P) (field : Field_d D P) :
    ∃ V, Rel_ultra_d D P V ∧ ∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U := by
  obtain ⟨V, hv⟩ := KP.intersection_exists_d hKP P U
  have top := (hv D).mpr ⟨field.top, h.base.top⟩
  have meet A B (ha : M.mem A V) (hb : M.mem B V) :
      ∃ C, M.mem C V ∧ M.MemberSubset C A ∧ M.MemberSubset C B := by
    obtain ⟨C, hc, spec⟩ := field.inter A B ((hv A).mp ha).1 ((hv B).mp hb).1
    obtain ⟨W, hw, wa, wb⟩ := h.base.meet A B ((hv A).mp ha).2 ((hv B).mp hb).2
    exact ⟨C, (hv C).mpr ⟨hc, h.upward W C hw ((hp C).mp hc).1 (field.bounds C hc)
      (fun x hx => (spec x).mpr ⟨wa x hx, wb x hx⟩)⟩,
      fun x hx => ((spec x).mp hx).1, fun x hx => ((spec x).mp hx).2⟩
  refine ⟨V, ⟨field, ⟨fun A ha => h.base.bounds A ((hv A).mp ha).2, top, meet⟩,
    fun A ha => ((hv A).mp ha).1, ?_, fun A ha => h.proper A ((hv A).mp ha).2, ?_⟩, hv⟩
  · exact fun A B ha hb hab => (hv B).mpr ⟨hb, h.upward A B ((hv A).mp ha).2 ((hp B).mp hb).1 (field.bounds B hb) hab⟩
  · intro A B ha hb hc
    exact (h.decides A B ((hp A).mp ha).1 (field.bounds A ha) ((hp B).mp hb).1 hc).imp
      (fun h => (hv A).mpr ⟨ha, h⟩) (fun h => (hv B).mpr ⟨hb, h⟩)

end YesMetaZFC.SetTheory.FilterZF
