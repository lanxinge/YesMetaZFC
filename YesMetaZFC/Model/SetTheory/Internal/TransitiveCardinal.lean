import YesMetaZFC.Model.SetTheory.Internal.TransitiveSource
import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.Composition

/-! # 传递源中的基数和共尾序列

基数性向下读取；共尾序列的图与值域向上读取。反向解释只要求给定的
实际值域属于源，不假定源满足整个 ZF，也不使用外部选择函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
include hX
local notation "N" => rt_model_l X nx

theorem rt_limit_l (hKP : M.Models KP) (a : (N).Domain) : (N).IsLimitOrdinal a ↔ M.IsLimitOrdinal a.val := by
  refine and_congr (rt_ordinal_iff_l hX nx hKP a) ?_
  constructor
  · rintro ⟨⟨x, hx⟩, next⟩
    exact ⟨⟨x.val, hx⟩, fun x hx => (next ⟨x, hX a.val a.property x hx⟩ hx).elim
      fun y hy => ⟨y.val, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, next⟩
    exact ⟨⟨⟨x, hX a.val a.property x hx⟩, hx⟩, fun x hx => (next x.val hx).elim
      fun y hy => ⟨⟨y, hX a.val a.property y hy.1⟩, hy⟩⟩

theorem rt_union_l (a b : (N).Domain) : (N).IsUnionOf a b ↔ M.IsUnionOf a.val b.val := by
  constructor
  · intro h x
    refine ⟨fun hx => ?_, fun ⟨y, hy, hxy⟩ => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := (h ⟨x, hX a.val a.property x hx⟩).mp hx
      exact ⟨y.val, hy, hxy⟩
    · exact (h ⟨x, hX y (hX b.val b.property y hy) x hxy⟩).mpr ⟨⟨y, hX b.val b.property y hy⟩, hy, hxy⟩
  · intro h x
    exact (h x.val).trans ⟨fun ⟨y, hy, hxy⟩ => ⟨⟨y, hX b.val b.property y hy⟩, hy, hxy⟩,
      fun ⟨y, hy, hxy⟩ => ⟨y.val, hy, hxy⟩⟩

variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hX nx hE hp

theorem rt_cardinal_l (κ : (N).Domain) (h : M.IsCardinal I κ.val) : (N).IsCardinal J κ := by
  refine ⟨rt_ordinal_l hX nx κ h.1, ?_⟩
  rintro α hα ⟨f, hf⟩
  exact h.2 α.val hα ⟨f.val, (rt_bijection_l hX nx hE hP hp f α κ).mp hf⟩

/-- 原模型的基数性限制到传递子源；两源只需各自实际的配对闭包。 -/
theorem rt_cardinal_restrict_l (hKP : M.Models KP) {Y : M.Domain} (hY : M.TransitiveSet Y)
    (ny : Nonempty {x // M.mem x Y}) (pq : ∀ a b, M.mem a Y → M.mem b Y → ∃ p, M.mem p Y ∧ Pair_d M p a b)
    (sub : M.MemberSubset Y X) (κ : (rt_model_l Y ny).Domain)
    (h : (N).IsCardinal J ⟨κ.val, sub κ.val κ.property⟩) :
    (rt_model_l Y ny).IsCardinal (rt_pair_l hY ny hE pq) κ := by
  refine ⟨rt_ordinal_l hY ny κ ((rt_ordinal_iff_l hX nx hKP _).mp h.1), ?_⟩
  rintro a ha ⟨f, hf⟩
  exact h.2 ⟨a.val, sub a.val a.property⟩ ha ⟨⟨f.val, sub f.val f.property⟩,
    (rt_bijection_l hX nx hE (KP.exists_pair hKP) hp _ _ _).mpr
      ((rt_bijection_l hY ny hE (KP.exists_pair hKP) pq f a κ).mp hf)⟩

theorem rt_range_l (R f : (N).Domain) : (N).IsRangeOf J R f ↔ M.IsRangeOf I R.val f.val := by
  have entry := rt_entry_l hX nx hE
  constructor
  · intro h y
    refine ⟨fun hy => ?_, fun ⟨x, hxy⟩ => ?_⟩
    · obtain ⟨x, hxy⟩ := (h ⟨y, hX R.val R.property y hy⟩).mp hy
      exact ⟨x.val, (entry ..).mp hxy⟩
    · have xy := rd_entry_transitive_l hX f.property hxy
      exact (h ⟨y, xy.2⟩).mpr ⟨⟨x, xy.1⟩, (entry ..).mpr hxy⟩
  · intro h y
    exact (h y.val).trans ⟨fun ⟨x, hxy⟩ => ⟨⟨x, (rd_entry_transitive_l hX f.property hxy).1⟩, (entry ..).mpr hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x.val, (entry ..).mp hxy⟩⟩

/-- 共尾性中的值域见证也是源中的实际集合，因而向上恢复全部共尾性。 -/
theorem rt_cofinal_up_l (hKP : M.Models KP) (f μ κ : (N).Domain)
    (h : (N).IsCofinalOrdinalSequence J f μ κ) : M.IsCofinalOrdinalSequence I f.val μ.val κ.val := by
  have hk := (rt_limit_l hX nx hKP κ).mp h.1
  have ff := (rt_function_from_l hX nx hE hP hp f μ κ).mp h.isSetFunctionFromTo
  have values : M.IsOrdinalValuedSequence I f.val μ.val :=
    ⟨⟨(rt_ordinal_iff_l hX nx hKP μ).mp h.2.1.1.1.1, ff.1, ff.2.1⟩,
      fun _ _ _ hv => hk.1.mem (ff.output_mem_of_pairMember hv)⟩
  refine ⟨hk, ⟨values, ?_⟩, ⟨hk.1, values, ?_⟩, fun _ _ _ hv => ff.output_mem_of_pairMember hv⟩
  · intro a ha b hb hab x y hx hy
    have ax := rd_entry_transitive_l hX f.property hx
    have by' := rd_entry_transitive_l hX f.property hy
    exact h.2.1.2 ⟨a, ax.1⟩ ha ⟨b, by'.1⟩ hb hab ⟨x, ax.2⟩ ⟨y, by'.2⟩
      ((rt_entry_l hX nx hE ..).mpr hx) ((rt_entry_l hX nx hE ..).mpr hy)
  · obtain ⟨R, range, union⟩ := h.2.2.1.2.2
    exact ⟨R.val, (rt_range_l hX nx hE hP hp R f).mp range, (rt_union_l hX nx κ R).mp union⟩

/-- 给定实际值域的所有权后，同一图在传递源中保持共尾性。 -/
theorem rt_cofinal_down_l (f μ κ R : (N).Domain) (range : M.IsRangeOf I R.val f.val)
    (h : M.IsCofinalOrdinalSequence I f.val μ.val κ.val) : (N).IsCofinalOrdinalSequence J f μ κ := by
  have ff := (rt_function_from_l hX nx hE hP hp f μ κ).mpr h.isSetFunctionFromTo
  have hk : (N).IsLimitOrdinal κ := by
    refine ⟨rt_ordinal_l hX nx κ h.1.1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := h.1.2.1
      exact ⟨⟨x, hX κ.val κ.property x hx⟩, hx⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := h.1.2.2 x.val hx
      exact ⟨⟨y, hX κ.val κ.property y hy⟩, hy, hxy⟩
  have values : (N).IsOrdinalValuedSequence J f μ :=
    ⟨⟨rt_ordinal_l hX nx μ h.2.1.1.1.1, ff.1, ff.2.1⟩,
      fun _ _ v hv => rt_ordinal_l hX nx v (h.1.1.mem (h.isSetFunctionFromTo.output_mem_of_pairMember
        ((rt_entry_l hX nx hE ..).mp hv)))⟩
  refine ⟨hk, ⟨values, ?_⟩, ⟨hk.1, values, R, (rt_range_l hX nx hE hP hp R f).mpr range,
    (rt_union_l hX nx κ R).mpr (h.range_isCofinalSubset hE range).2.2⟩, fun _ _ _ hv => ff.output_mem_of_pairMember hv⟩
  intro a ha b hb hab x y hx hy
  exact h.2.1.2 a.val ha b.val hb hab x.val y.val
    ((rt_entry_l hX nx hE ..).mp hx) ((rt_entry_l hX nx hE ..).mp hy)

end YesMetaZFC.SetTheory.Internal
