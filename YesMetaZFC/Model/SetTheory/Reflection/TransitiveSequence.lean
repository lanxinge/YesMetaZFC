import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Card.Syntax
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Collapse.RelationSyntax
import YesMetaZFC.SetTheory.Ord.OrderType
import YesMetaZFC.SetTheory.Ord.Normal

/-! # 传递源的原始序数、自然数与函数解释

原有序对解释只用源内配对构造。所有图与其坐标均由传递性回收；不假定
整个相对模型满足 KP 或 ZF。基数性只从大源向小源传递，不提升为背景基数性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (hn : Nonempty {x // M.mem x X})
include hX

theorem rt_fn_l (hE : Extensional M) (A B f : (rt_model_l X hn).Domain) :
    Fn0_d A B f ↔ Fn0_d A.val B.val f.val := by
  let ρ : Env (rt_model_l X hn) 3 := ⟨Fin.cases f (Fin.cases B (fun _ => A)), fun _ => A⟩
  exact (fn0_sat_l (rt_model_ext_l hE hX hn) ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hX hn (fn0_delta_l ..) ρ).trans (fn0_sat_l hE _ _ _ _))

theorem rt_entry_l (hE : Extensional M) (a b f : (rt_model_l X hn).Domain) :
    Rd_entry_d a b f ↔ Rd_entry_d a.val b.val f.val := by
  let ρ : Env (rt_model_l X hn) 3 := ⟨Fin.cases f (Fin.cases b (fun _ => a)), fun _ => a⟩
  exact (rd_entry0_sat_l (rt_model_ext_l hE hX hn) ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hX hn (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l hE _ _ _ _))

theorem rt_cp_l (hE : Extensional M) (m n K q s t : (rt_model_l X hn).Domain) :
    Cp0_d m n K q s t ↔ Cp0_d m.val n.val K.val q.val s.val t.val := by
  let ρ : Env (rt_model_l X hn) 6 := ⟨Fin.cases t (Fin.cases s (Fin.cases q (Fin.cases K (Fin.cases n (fun _ => m))))), fun _ => m⟩
  exact (cp0_sat_l (rt_model_ext_l hE hX hn) ρ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hX hn (cp0_delta_l ..) ρ).trans (cp0_sat_l hE _ _ _ _ _ _ _))

theorem rt_successor_l (hE : Extensional M) (s a : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).SuccessorOf s a ↔ M.SuccessorOf s.val a.val := by
  let ρ : Env (rt_model_l X hn) 2 := ⟨Fin.cases s (fun _ => a), fun _ => a⟩
  exact (KP.succ0_sat_l (rt_model_ext_l hE hX hn) ρ .newest (.bound 1)).symm.trans
    ((rt_model_delta_l hX hn (KP.succ0_delta_l ..) ρ).trans (KP.succ0_sat_l hE _ _ _))

theorem rt_ordinal_l (a : (rt_model_l X hn).Domain) (h : M.IsOrdinal a.val) : (rt_model_l X hn).IsOrdinal a := by
  refine ⟨fun x hx y hy => h.transitive x.val hx y.val hy, ⟨?_, ?_⟩⟩
  · exact ⟨fun x hx => h.wellOrder.linear.irrefl x.val hx,
      fun x hx y hy z hz => h.wellOrder.linear.trans x.val hx y.val hy z.val hz,
      fun x hx y hy => (h.wellOrder.linear.compare x.val hx y.val hy).imp
        (fun eq z => eq z.val) id⟩
  · intro B sub ne
    obtain ⟨x, hx⟩ := ne
    obtain ⟨z, hz, least⟩ := h.wellOrder.least B.val (fun t ht => sub ⟨t, hX B.val B.property t ht⟩ ht) ⟨x.val, hx⟩
    exact ⟨⟨z, hX B.val B.property z hz⟩, hz, fun y hy => (least y.val hy).imp (fun eq t => eq t.val) id⟩

theorem rt_ordinal_iff_l (hKP : M.Models KP) (a : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsOrdinal a ↔ M.IsOrdinal a.val := by
  refine ⟨fun h => ?_, rt_ordinal_l hX hn a⟩
  have trans (b : (rt_model_l X hn).Domain) (hb : (rt_model_l X hn).TransitiveSet b) : M.TransitiveSet b.val :=
    fun x hx y hy => hb ⟨x, hX b.val b.property x hx⟩ hx ⟨y, hX x (hX b.val b.property x hx) y hy⟩ hy
  refine (KP.ord0_iff_l hKP).mp ⟨trans a h.transitive, fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact trans ⟨x, hX a.val a.property x hx⟩
      (Structure.IsOrdinal.mem (ℳ := rt_model_l X hn) (α := a) (β := ⟨x, hX a.val a.property x hx⟩) h hx).transitive
  · rcases h.wellOrder.linear.compare ⟨x, hX a.val a.property x hx⟩ hx ⟨y, hX a.val a.property y hy⟩ hy with eq | lt | gt
    · exact Or.inl (congrArg Subtype.val ((rt_model_ext_l hKP.1 hX hn).eq_of_same_members _ _ eq))
    · exact Or.inr (Or.inl lt)
    · exact Or.inr (Or.inr gt)

/-- 传递载体中的归纳集与背景归纳集逐项一致。 -/
theorem rt_inductive_l (hE : Extensional M) (A : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsInductive A ↔ M.IsInductive A.val := by
  constructor
  · rintro ⟨⟨z, hz, hzA⟩, hs⟩
    exact ⟨⟨z.val, fun x hx => hz ⟨x, hX z.val z.property x hx⟩ hx, hzA⟩, fun a ha => by
      obtain ⟨s, hs, hsA⟩ := hs ⟨a, hX A.val A.property a ha⟩ ha
      exact ⟨s.val, (rt_successor_l hX hn hE ..).mp hs, hsA⟩⟩
  · rintro ⟨⟨z, hz, hzA⟩, hs⟩
    exact ⟨⟨⟨z, hX A.val A.property z hzA⟩, fun x => hz x.val, hzA⟩, fun a ha => by
      obtain ⟨s, hs, hsA⟩ := hs a.val ha
      exact ⟨⟨s, hX A.val A.property s hsA⟩, (rt_successor_l hX hn hE ..).mpr hs, hsA⟩⟩

theorem rt_omega_l (hE : Extensional M) (ω : (rt_model_l X hn).Domain) (hω : M.IsOmega ω.val) :
    (rt_model_l X hn).IsOmega ω :=
  ⟨(rt_inductive_l hX hn hE ω).mpr hω.1,
    fun A hA x hx => hω.2 A.val ((rt_inductive_l hX hn hE A).mp hA) x.val hx⟩

/-- 序数性加内部最小归纳性识别背景 ω；传递源无需满足 KP 或分离。 -/
theorem rt_omega_eq_l (hKP : M.Models KP) {ω : M.Domain} (hω : M.IsOmega ω)
    (w : (rt_model_l X hn).Domain) (ho : (rt_model_l X hn).IsOrdinal w)
    (hw : (rt_model_l X hn).IsOmega w) : w.val = ω := by
  have sub := hω.2 w.val ((rt_inductive_l hX hn hKP.1 w).mp hw.1)
  rcases Structure.IsOrdinal.trichotomy hKP.1 ((rt_ordinal_iff_l hX hn hKP w).mp ho)
    (hω.isOrdinal hKP) (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP w.val ω) with eq | lt | gt
  · exact hKP.1.eq_of_same_members _ _ eq
  · exact (KP.mem_irrefl_d hKP w.val (sub w.val lt)).elim
  · let v : (rt_model_l X hn).Domain := ⟨ω,hX w.val w.property ω gt⟩
    have back := hw.2 v ((rt_inductive_l hX hn hKP.1 v).mpr hω.1)
    exact hKP.1.eq_of_same_members w.val ω fun a =>
      ⟨fun ha => back ⟨a,hX w.val w.property a ha⟩ ha,sub a⟩

/-- 只使用源内实际配对闭包，解释本身不作选择。 -/
def rt_pair_l (hE : Extensional M) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b) :
    kpair_convention_l.Interpretation (rt_model_l X hn) :=
  kpair_interpretation_l _ (rt_model_ext_l hE hX hn) (fun a b => by
    obtain ⟨p, hp, pair⟩ := hp a.val b.val a.property b.property
    exact ⟨⟨p, hp⟩, fun x => (pair x.val).trans
      (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)⟩)

variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "J" => rt_pair_l hX hn hE hp
local notation "I" => kpair_interpretation_l M hE hP

theorem rt_function_l (f : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsSetFunction J f ↔ M.IsSetFunction I f.val := by
  have pair (p a b : (rt_model_l X hn).Domain) : KPair_d (rt_model_l X hn) p a b ↔ KPair_d M p.val a.val b.val := by
    let ρ : Env (rt_model_l X hn) 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => p⟩
    exact (kpair0_sat_l (rt_model_ext_l hE hX hn) ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l hX hn (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hE _ _ _ _))
  have entry := rt_entry_l hX hn hE
  constructor
  · rintro ⟨relation, functional⟩
    refine ⟨fun p hp => ?_, fun a b c hab hac => ?_⟩
    · obtain ⟨a, b, hp'⟩ := relation ⟨p, hX f.val f.property p hp⟩ hp
      exact ⟨a.val, b.val, (pair _ a b).mp hp'⟩
    · have ab := rd_entry_transitive_l hX f.property hab
      have ac := rd_entry_transitive_l hX f.property hac
      exact congrArg Subtype.val (functional ⟨a, ab.1⟩ ⟨b, ab.2⟩ ⟨c, ac.2⟩
        ((entry _ _ f).mpr hab) ((entry _ _ f).mpr hac))
  · rintro ⟨relation, functional⟩
    refine ⟨fun p hp => ?_, fun a b c hab hac => ?_⟩
    · obtain ⟨a, b, hp'⟩ := relation p.val hp
      have ab := hp'.mem_l M hX p.property
      exact ⟨⟨a, ab.1⟩, ⟨b, ab.2⟩, (pair p _ _).mpr hp'⟩
    · exact Subtype.ext (functional a.val b.val c.val ((entry a b f).mp hab) ((entry a c f).mp hac))

theorem rt_function_from_l (f A B : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsSetFunctionFromTo J f A B ↔ M.IsSetFunctionFromTo I f.val A.val B.val := by
  have entry := rt_entry_l hX hn hE
  constructor
  · rintro ⟨hf, domain, total⟩
    refine ⟨(rt_function_l hX hn hE hP hp f).mp hf, fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
    · intro hx
      obtain ⟨y, hxy⟩ := (domain ⟨x, hX A.val A.property x hx⟩).mp hx
      exact ⟨y.val, (entry _ y f).mp hxy⟩
    · rintro ⟨y, hxy⟩
      have xy := rd_entry_transitive_l hX f.property hxy
      exact (domain ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, (entry _ _ f).mpr hxy⟩
    · obtain ⟨y, hy, hxy⟩ := total ⟨x, hX A.val A.property x hx⟩ hx
      exact ⟨y.val, hy, (entry _ _ f).mp hxy⟩
  · rintro ⟨hf, domain, total⟩
    refine ⟨(rt_function_l hX hn hE hP hp f).mpr hf, fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
    · intro hx
      obtain ⟨y, hxy⟩ := (domain x.val).mp hx
      exact ⟨⟨y, (rd_entry_transitive_l hX f.property hxy).2⟩, (entry _ _ f).mpr hxy⟩
    · rintro ⟨y, hxy⟩
      exact (domain x.val).mpr ⟨y.val, (entry _ _ f).mp hxy⟩
    · obtain ⟨y, hy, hxy⟩ := total x.val hx
      exact ⟨⟨y, hX B.val B.property y hy⟩, hy, (entry _ _ f).mpr hxy⟩

theorem rt_injection_l (f A B : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsSetInjectionFromTo J f A B ↔ M.IsSetInjectionFromTo I f.val A.val B.val := by
  have entry := rt_entry_l hX hn hE
  constructor
  · rintro ⟨hf, inj⟩
    refine ⟨(rt_function_from_l hX hn hE hP hp f A B).mp hf, fun a b x ha hb => ?_⟩
    have ax := rd_entry_transitive_l hX f.property ha
    have bx := rd_entry_transitive_l hX f.property hb
    exact congrArg Subtype.val (inj ⟨a, ax.1⟩ ⟨b, bx.1⟩ ⟨x, ax.2⟩ ((entry _ _ f).mpr ha) ((entry _ _ f).mpr hb))
  · rintro ⟨hf, inj⟩
    exact ⟨(rt_function_from_l hX hn hE hP hp f A B).mpr hf, fun a b x ha hb =>
      Subtype.ext (inj a.val b.val x.val ((entry _ _ f).mp ha) ((entry _ _ f).mp hb))⟩

theorem rt_bijection_l (f A B : (rt_model_l X hn).Domain) :
    (rt_model_l X hn).IsSetBijectionFromTo J f A B ↔ M.IsSetBijectionFromTo I f.val A.val B.val := by
  have entry := rt_entry_l hX hn hE
  constructor
  · rintro ⟨hf, onto⟩
    refine ⟨(rt_injection_l hX hn hE hP hp f A B).mp hf, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := onto ⟨y, hX B.val B.property y hy⟩ hy
    exact ⟨x.val, hx, (entry _ _ f).mp hxy⟩
  · rintro ⟨hf, onto⟩
    refine ⟨(rt_injection_l hX hn hE hP hp f A B).mpr hf, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := onto y.val hy
    exact ⟨⟨x, hX A.val A.property x hx⟩, hx, (entry _ _ f).mpr hxy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 传递源中的基数和共尾序列

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

/-! ## 任意传递集合中的原函数公式

已有图的坐标由传递性回收；读取公式不需要子模型对配对封闭。
这使原函数、单射与双射语法也能直接用于后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X}) (hE : Extensional M)
include hX hE
local notation "N" => rt_model_l X nx

theorem rt_kpair_formula_l {d} (ρ : Env N d) (p a b : Term d) :
    Formula.satisfies ρ (kpair_convention_l.code p a b) ↔ KPair_d M (p.eval ρ).val (a.eval ρ).val (b.eval ρ).val := by
  exact (kpair_sat_l N (rt_model_ext_l hE hX nx) ρ p a b).trans
    ((kpair0_sat_l (rt_model_ext_l hE hX nx) ρ p a b).symm.trans
      ((rt_model_delta_l hX nx (kpair0_delta_l ..) ρ).trans (by
        simpa only [@eval_image_env_l (rt_model_l X nx) M Subtype.val] using kpair0_sat_l hE (image_env_l Subtype.val ρ) p a b)))

theorem rt_entry_formula_l {d} (ρ : Env N d) (a b f : Term d) :
    Formula.satisfies ρ (Formula.orderedPairMem kpair_convention_l a b f) ↔
      Rd_entry_d (a.eval ρ).val (b.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.orderedPairMem, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, rt_kpair_formula_l hX nx hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨p, hp, hf⟩ => ⟨p.val, hp, hf⟩,
    fun ⟨p, hp, hf⟩ => ⟨⟨p, hX _ (f.eval ρ).property p hf⟩, hp, hf⟩⟩

variable (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
local notation "I" => kpair_interpretation_l M hE hP

theorem rt_function_formula_l {d} (ρ : Env N d) (f : Term d) :
    Formula.satisfies ρ (Formula.isFunction kpair_convention_l f) ↔ M.IsSetFunction I (f.eval ρ).val := by
  simp only [Formula.isFunction, Formula.isRelation,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rt_kpair_formula_l hX nx hE,
    rt_entry_formula_l hX nx hE, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE hX nx),
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]
  constructor
  · rintro ⟨rel, func⟩
    refine ⟨fun p hp => ?_, fun a b c hab hac => ?_⟩
    · obtain ⟨a, b, hp'⟩ := rel ⟨p, hX _ (f.eval ρ).property p hp⟩ hp
      exact ⟨a.val, b.val, hp'⟩
    · have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
      have ac := rd_entry_transitive_l hX (f.eval ρ).property hac
      exact congrArg Subtype.val (func ⟨a, ab.1⟩ ⟨b, ab.2⟩ ⟨c, ac.2⟩ ⟨hab, hac⟩)
  · rintro ⟨rel, func⟩
    refine ⟨fun p hp => ?_, fun a b c h => ?_⟩
    · obtain ⟨a, b, pair⟩ := rel p.val hp
      have ab := pair.mem_l M hX p.property
      exact ⟨⟨a, ab.1⟩, ⟨b, ab.2⟩, pair⟩
    · exact Subtype.ext (func a.val b.val c.val h.1 h.2)

theorem rt_domain_formula_l {d} (ρ : Env N d) (A f : Term d) :
    Formula.satisfies ρ (Formula.isDomain kpair_convention_l A f) ↔ M.IsDomainOf I (A.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.isDomain, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rt_entry_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · intro h x
    refine ⟨fun hx => ?_, fun ⟨y, hxy⟩ => ?_⟩
    · obtain ⟨y, hxy⟩ := (h ⟨x, hX _ (A.eval ρ).property x hx⟩).mp hx
      exact ⟨y.val, hxy⟩
    · have xy := rd_entry_transitive_l hX (f.eval ρ).property hxy
      exact (h ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, hxy⟩
  · intro h x
    exact (h x.val).trans ⟨fun ⟨y, hxy⟩ => ⟨⟨y, (rd_entry_transitive_l hX (f.eval ρ).property hxy).2⟩, hxy⟩,
      fun ⟨y, hxy⟩ => ⟨y.val, hxy⟩⟩

theorem rt_range_formula_l {d} (ρ : Env N d) (A f : Term d) :
    Formula.satisfies ρ (Formula.isRange kpair_convention_l A f) ↔ M.IsRangeOf I (A.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.isRange, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rt_entry_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · intro h y
    refine ⟨fun hy => ?_, fun ⟨x, hxy⟩ => ?_⟩
    · obtain ⟨x, hxy⟩ := (h ⟨y, hX _ (A.eval ρ).property y hy⟩).mp hy
      exact ⟨x.val, hxy⟩
    · have xy := rd_entry_transitive_l hX (f.eval ρ).property hxy
      exact (h ⟨y, xy.2⟩).mpr ⟨⟨x, xy.1⟩, hxy⟩
  · intro h y
    exact (h y.val).trans ⟨fun ⟨x, hxy⟩ => ⟨⟨x, (rd_entry_transitive_l hX (f.eval ρ).property hxy).1⟩, hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x.val, hxy⟩⟩

theorem rt_function_from_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isFunctionFromTo kpair_convention_l f A B) ↔
      M.IsSetFunctionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isFunctionFromTo, Formula.satisfies_conj_iff, rt_function_formula_l hX nx hE hP,
    rt_domain_formula_l hX nx hE hP, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rt_entry_formula_l hX nx hE, Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h a ha => ?_, fun h a ha => ?_⟩)
  · obtain ⟨b, hb, hab⟩ := h ⟨a, hX _ (A.eval ρ).property a ha⟩ ha
    exact ⟨b.val, hb, hab⟩
  · obtain ⟨b, hb, hab⟩ := h a.val ha
    exact ⟨⟨b, hX _ (B.eval ρ).property b hb⟩, hb, hab⟩

theorem rt_injection_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isInjectionFromTo kpair_convention_l f A B) ↔
      M.IsSetInjectionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isInjectionFromTo, Formula.isInjective, Formula.satisfies_conj_iff,
    rt_function_from_formula_l hX nx hE hP, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hE, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE hX nx),
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]
  refine and_congr Iff.rfl ⟨fun h a b x ha hb => ?_, fun h a b x hh => ?_⟩
  · have ax := rd_entry_transitive_l hX (f.eval ρ).property ha
    have bx := rd_entry_transitive_l hX (f.eval ρ).property hb
    exact congrArg Subtype.val (h ⟨a, ax.1⟩ ⟨b, bx.1⟩ ⟨x, ax.2⟩ ⟨ha, hb⟩)
  · exact Subtype.ext (h a.val b.val x.val hh.1 hh.2)

theorem rt_bijection_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isBijectionFromTo kpair_convention_l f A B) ↔
      M.IsSetBijectionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isBijectionFromTo, Formula.isSurjectiveOnto, Formula.satisfies_conj_iff,
    rt_injection_formula_l hX nx hE hP, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rt_entry_formula_l hX nx hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl ⟨fun h b hb => ?_, fun h b hb => ?_⟩
  · obtain ⟨a, ha, hab⟩ := h ⟨b, hX _ (B.eval ρ).property b hb⟩ hb
    exact ⟨a.val, ha, hab⟩
  · obtain ⟨a, ha, hab⟩ := h b.val hb
    exact ⟨⟨a, hX _ (A.eval ρ).property a ha⟩, ha, hab⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 共尾公式在传递集合中的精确读取

函数与坐标无需额外闭包。原共尾公式唯一额外的存在见证是值域集合；
将其所有权显式列出，便可同时处理任意后继秩层及极限秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
include hKP hX
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l hKP

theorem rt_ordinal_sequence_formula_l {d} (ρ : Env N d) (f n : Term d) :
    Formula.satisfies ρ (Formula.isOrdinalValuedSequence kpair_convention_l f n) ↔
      M.IsOrdinalValuedSequence I (f.eval ρ).val (n.eval ρ).val := by
  simp only [Formula.isOrdinalValuedSequence, Formula.isSequenceOfLength, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP,
    rt_function_formula_l hX nx hKP.1 (KP.exists_pair hKP), rt_domain_formula_l hX nx hKP.1 (KP.exists_pair hKP),
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl ⟨fun h a ha b hab => ?_, fun h a ha b hab => ?_⟩
  · have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
    exact h ⟨a, ab.1⟩ ha ⟨b, ab.2⟩ hab
  · exact h a.val ha b.val hab

theorem rt_increasing_formula_l {d} (ρ : Env N d) (f n : Term d) :
    Formula.satisfies ρ (Formula.isIncreasingOrdinalSequence kpair_convention_l f n) ↔
      M.IsIncreasingOrdinalSequence I (f.eval ρ).val (n.eval ρ).val := by
  simp only [Formula.isIncreasingOrdinalSequence, Formula.satisfies_conj_iff,
    rt_ordinal_sequence_formula_l hKP hX nx, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    rt_entry_formula_l hX nx hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_three_push]
  refine and_congr Iff.rfl ⟨fun h a ha b hb hab x y hx hy => ?_, fun h a ha b hb hab x y hh => ?_⟩
  · have ax := rd_entry_transitive_l hX (f.eval ρ).property hx
    have by' := rd_entry_transitive_l hX (f.eval ρ).property hy
    exact h ⟨a, ax.1⟩ ha ⟨b, by'.1⟩ hb hab ⟨x, ax.2⟩ ⟨y, by'.2⟩ ⟨hx, hy⟩
  · exact h a.val ha b.val hb hab x.val y.val hh.1 hh.2

theorem rt_cofinal_formula_l {d} (ρ : Env N d) (f n k : Term d) :
    Formula.satisfies ρ (Formula.isCofinalOrdinalSequence kpair_convention_l f n k) ↔
      M.IsCofinalOrdinalSequence I (f.eval ρ).val (n.eval ρ).val (k.eval ρ).val ∧
        ∃ R, M.mem R X ∧ M.IsRangeOf I R (f.eval ρ).val := by
  simp only [Formula.isCofinalOrdinalSequence, Formula.isOrdinalSequenceLimit, Formula.satisfies_conj_iff,
    Formula.satisfies_isLimitOrdinal_iff, rt_limit_l hX nx hKP,
    rt_increasing_formula_l hKP hX nx, rt_ordinal_sequence_formula_l hKP hX nx,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP, Formula.satisfies_exists_iff,
    rt_range_formula_l hX nx hKP.1 (KP.exists_pair hKP), Formula.satisfies_isUnion_iff, rt_union_l hX nx,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hKP.1, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · rintro ⟨hk, inc, ⟨ord, vals, R, range, union⟩, bound⟩
    refine ⟨⟨hk, inc, ⟨ord, vals, R.val, range, union⟩, fun a ha b hab => ?_⟩, R.val, R.property, range⟩
    have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
    exact bound ⟨a, ab.1⟩ ha ⟨b, ab.2⟩ hab
  · rintro ⟨h, R, hR, range⟩
    exact ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.1, ⟨R, hR⟩, range,
      (h.range_isCofinalSubset hKP.1 range).2.2⟩, fun a ha b hab => h.2.2.2 a.val ha b.val hab⟩

/-- 基数性向下成立；被子模型量化的任何反例图均可原样读回。 -/
theorem rt_cardinal_formula_l {d} (ρ : Env N d) (k : Term d) (h : M.IsCardinal I (k.eval ρ).val) :
    Formula.satisfies ρ (Formula.isCardinal kpair_convention_l k) := by
  simp only [Formula.isCardinal, Formula.equinumerous, Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinal_iff, rt_ordinal_iff_l hX nx hKP, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
    rt_bijection_formula_l hX nx hKP.1 (KP.exists_pair hKP), Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  exact ⟨h.1, fun a ha ⟨f, hf⟩ => h.2 a.val ha ⟨f.val, hf⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 传递子源中实际结构码的绝对性

只需配对闭包。图的坐标由传递性回收，既不假设子源满足 ZF，也不要求
子源包含所有背景子集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hE hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_kpair_l (p a b : (N).Domain) : (J).Codes p a b ↔ (I).Codes p.val a.val b.val := by
  let ρ : Env N 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => p⟩
  exact (kpair0_sat_l (rt_model_ext_l hE hZ nz) ρ .newest (.bound 1) (.bound 2)).symm.trans
    ((rt_model_delta_l hZ nz (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hE ..))

theorem rt_relation_l (R : (N).Domain) : (N).IsSetRelation J R ↔ M.IsSetRelation I R.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, code⟩ := h ⟨p, hZ R.val R.property p hp⟩ hp
    exact ⟨a.val, b.val, (rt_kpair_l hE hP hZ nz pair ..).mp code⟩
  · intro h p hp
    obtain ⟨a, b, code⟩ := h p.val hp
    have mem := code.mem_l M hZ p.property
    exact ⟨⟨a, mem.1⟩, ⟨b, mem.2⟩, (rt_kpair_l hE hP hZ nz pair ..).mpr code⟩

theorem rt_smdl_l (c A R : (N).Domain) : Smdl_d J c A R ↔ Smdl_d I c.val A.val R.val := by
  refine and_congr (rt_kpair_l hE hP hZ nz pair c A R) (and_congr ?_ ?_)
  · exact ⟨fun ⟨x, hx⟩ => ⟨x.val, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, hZ A.val A.property x hx⟩, hx⟩⟩
  · refine and_congr (rt_relation_l hE hP hZ nz pair R) ?_
    constructor
    · intro h x y hxy
      have xy := rd_entry_transitive_l hZ R.property hxy
      exact h ⟨x, xy.1⟩ ⟨y, xy.2⟩ ((rt_entry_l hZ nz hE ..).mpr hxy)
    · intro h x y hxy
      exact h x.val y.val ((rt_entry_l hZ nz hE ..).mp hxy)

theorem rt_smem_l (c A R : (N).Domain) : Smem_d J c A R ↔ Smem_d I c.val A.val R.val := by
  refine and_congr (rt_smdl_l hE hP hZ nz pair c A R) ?_
  constructor
  · intro h x y
    constructor
    · intro hxy
      have xy := rd_entry_transitive_l hZ R.property hxy
      exact (h ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((rt_entry_l hZ nz hE ..).mpr hxy)
    · intro hxy
      exact (rt_entry_l hZ nz hE ..).mp ((h ⟨x, hZ A.val A.property x hxy.1⟩
        ⟨y, hZ A.val A.property y hxy.2.1⟩).mpr hxy)
  · intro h x y
    exact (rt_entry_l hZ nz hE ..).trans (h x.val y.val)

end YesMetaZFC.SetTheory.Internal

/-! ## 指定坍塌图在传递子源中的读取

每个坍塌值恰为原前驱值之集；不以背景良基性或另一张坍塌图代替原方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_wc_graph_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z})
    (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
    (X R F : (rt_model_l Z nz).Domain) (h : Wc_graph_d X R F) : Wc_graph_d X.val R.val F.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨(rt_relation_l hKP.1 (KP.exists_pair hKP) hZ nz pair F).mp h.1, fun a x hax => ?_⟩
  have ax := rd_entry_transitive_l hZ F.property hax
  obtain ⟨ha, total, values⟩ := h.2 ⟨a, ax.1⟩ ⟨x, ax.2⟩ ((ent ..).mpr hax)
  refine ⟨ha, (fun b hb hba => ?_), fun y => ⟨?_, ?_⟩⟩
  · obtain ⟨y, hby⟩ := total ⟨b, hZ X.val X.property b hb⟩ hb ((ent ..).mpr hba)
    exact ⟨y.val, (ent ..).mp hby⟩
  · intro hy
    obtain ⟨b, hb, hba, hby⟩ := (values ⟨y, hZ x ax.2 y hy⟩).mp hy
    exact ⟨b.val, hb, (ent ..).mp hba, (ent ..).mp hby⟩
  · rintro ⟨b, hb, hba, hby⟩
    exact (values ⟨y, (rd_entry_transitive_l hZ F.property hby).2⟩).mpr
      ⟨⟨b, hZ X.val X.property b hb⟩, hb, (ent ..).mpr hba, (ent ..).mpr hby⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 传递子源中的笛卡尔积与递归图

只用外延性和实际配对闭包；所有量词的见证由已有集合的传递性回收。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_member_subset_l (A B : (N).Domain) :
    (N).MemberSubset A B ↔ M.MemberSubset A.val B.val :=
  ⟨fun h x hx => h ⟨x, hZ A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩

theorem rt_domain_l (A F : (N).Domain) :
    (N).IsDomainOf J A F ↔ M.IsDomainOf I A.val F.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨y, hxy⟩ := (h ⟨x, hZ A.val A.property x hx⟩).mp hx
      exact ⟨y.val, (entry ..).mp hxy⟩
    · rintro ⟨y, hxy⟩
      have xy := rd_entry_transitive_l hZ F.property hxy
      exact (h ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, (entry ..).mpr hxy⟩
  · intro h x
    exact (h x.val).trans ⟨fun ⟨y, hxy⟩ =>
      ⟨⟨y, (rd_entry_transitive_l hZ F.property hxy).2⟩, (entry ..).mpr hxy⟩,
      fun ⟨y, hxy⟩ => ⟨y.val, (entry ..).mp hxy⟩⟩

theorem rt_restriction_l (P F A : (N).Domain) :
    (N).IsRestrictionOf J P F A ↔ M.IsRestrictionOf I P.val F.val A.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · rintro ⟨rel, cut⟩
    refine ⟨(rt_relation_l hE hP hZ nz pair P).mp rel, fun x y => ⟨?_, ?_⟩⟩
    · intro hxy
      have xy := rd_entry_transitive_l hZ P.property hxy
      obtain ⟨hx, he⟩ := (cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((entry ..).mpr hxy)
      exact ⟨hx, (entry ..).mp he⟩
    · rintro ⟨hx, hxy⟩
      have xy := rd_entry_transitive_l hZ F.property hxy
      exact (entry ..).mp ((cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mpr ⟨hx, (entry ..).mpr hxy⟩)
  · rintro ⟨rel, cut⟩
    exact ⟨(rt_relation_l hE hP hZ nz pair P).mpr rel, fun x y =>
      (entry x y P).trans ((cut x.val y.val).trans (and_congr_right fun _ => (entry x y F).symm))⟩

theorem rt_cartesian_l (P A B : (N).Domain) :
    (N).IsCartesianProduct J P A B ↔ M.IsCartesianProduct I P.val A.val B.val := by
  have code := rt_kpair_l hE hP hZ nz pair
  constructor
  · intro h p
    constructor
    · intro hp
      obtain ⟨a, ha, b, hb, hp⟩ := (h ⟨p, hZ P.val P.property p hp⟩).mp hp
      exact ⟨a.val, ha, b.val, hb, (code ..).mp hp⟩
    · rintro ⟨a, ha, b, hb, hp⟩
      let a' : (N).Domain := ⟨a, hZ A.val A.property a ha⟩
      let b' : (N).Domain := ⟨b, hZ B.val B.property b hb⟩
      obtain ⟨q, hq⟩ := (J).total a' b'
      have eq := (I).unique hp ((code ..).mp hq)
      exact eq ▸ (h q).mpr ⟨a', ha, b', hb, hq⟩
  · intro h p
    constructor
    · intro hp
      obtain ⟨a, ha, b, hb, hp⟩ := (h p.val).mp hp
      exact ⟨⟨a, hZ A.val A.property a ha⟩, ha, ⟨b, hZ B.val B.property b hb⟩, hb, (code ..).mpr hp⟩
    · rintro ⟨a, ha, b, hb, hp⟩
      exact (h p.val).mpr ⟨a.val, ha, b.val, hb, (code ..).mp hp⟩

theorem rt_relation_on_l (R A : (N).Domain) :
    (N).IsSetRelationOn J R A ↔ M.IsSetRelationOn I R.val A.val := by
  refine and_congr (rt_relation_l hE hP hZ nz pair R) ?_
  constructor
  · intro h x y hxy
    have xy := rd_entry_transitive_l hZ R.property hxy
    exact h ⟨x, xy.1⟩ ⟨y, xy.2⟩ ((rt_entry_l hZ nz hE ..).mpr hxy)
  · intro h x y hxy
    exact h x.val y.val ((rt_entry_l hZ nz hE ..).mp hxy)

end YesMetaZFC.SetTheory.Internal

/-! ## 传递子源中良序坍缩方程的绝对性

坍缩图已经在源内时，其前驱集与每个值的全部成员均可回收。
因此这里不需要源的替代公理，也不以外部良基性代替内部方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_predecessor_l (P R A p : (N).Domain) :
    (N).IsPredecessorSet J P R A p ↔ M.IsPredecessorSet I P.val R.val A.val p.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨ha, hr⟩ := (h ⟨x, hZ P.val P.property x hx⟩).mp hx
      exact ⟨ha, (entry ..).mp hr⟩
    · rintro ⟨ha, hr⟩
      exact (h ⟨x, hZ A.val A.property x ha⟩).mpr ⟨ha, (entry ..).mpr hr⟩
  · intro h x
    exact (h x.val).trans (and_congr_right fun _ => (entry x p R).symm)

theorem rt_initial_segment_l (P R A : (N).Domain) :
    (N).IsRelationInitialSegment J P R A ↔ M.IsRelationInitialSegment I P.val R.val A.val := by
  refine and_congr (rt_member_subset_l hZ nz P A) ?_
  constructor
  · intro h x hx y hy hyx
    exact h ⟨x, hZ P.val P.property x hx⟩ hx ⟨y, hZ A.val A.property y hy⟩ hy
      ((rt_entry_l hZ nz hE ..).mpr hyx)
  · intro h x hx y hy hyx
    exact h x.val hx y.val hy ((rt_entry_l hZ nz hE ..).mp hyx)

theorem rt_order_collapse_l (F R A P : (N).Domain) :
    (N).IsWellOrderCollapseFunction J F R A P ↔
      M.IsWellOrderCollapseFunction I F.val R.val A.val P.val := by
  have entry := rt_entry_l hZ nz hE
  refine and_congr (rt_function_l hZ nz hE hP pair F)
    (and_congr (rt_domain_l hE hP hZ nz pair P F)
      (and_congr (rt_initial_segment_l hE hP hZ nz pair P R A) ?_))
  constructor
  · intro h x hx y hxy z
    have xy := rd_entry_transitive_l hZ F.property hxy
    have values := h ⟨x, hZ P.val P.property x hx⟩ hx ⟨y, xy.2⟩ ((entry ..).mpr hxy)
    constructor
    · intro hz
      obtain ⟨a, ha, hax, haz⟩ := (values ⟨z, hZ y xy.2 z hz⟩).mp hz
      exact ⟨a.val, ha, (entry ..).mp hax, (entry ..).mp haz⟩
    · rintro ⟨a, ha, hax, haz⟩
      exact (values ⟨z, (rd_entry_transitive_l hZ F.property haz).2⟩).mpr
        ⟨⟨a, hZ P.val P.property a ha⟩, ha, (entry ..).mpr hax, (entry ..).mpr haz⟩
  · intro h x hx y hxy z
    constructor
    · intro hz
      obtain ⟨a, ha, hax, haz⟩ := (h x.val hx y.val ((entry ..).mp hxy) z.val).mp hz
      exact ⟨⟨a, hZ P.val P.property a ha⟩, ha, (entry ..).mpr hax, (entry ..).mpr haz⟩
    · rintro ⟨a, ha, hax, haz⟩
      exact (h x.val hx y.val ((entry ..).mp hxy) z.val).mpr
        ⟨a.val, ha, (entry ..).mp hax, (entry ..).mp haz⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 传递子源中序数列的绝对性 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_sequence_l (F n : (N).Domain) :
    (N).IsSequenceOfLength J F n ↔ M.IsSequenceOfLength I F.val n.val :=
  and_congr (rt_ordinal_iff_l hZ nz hKP n)
    (and_congr (rt_function_l hZ nz hKP.1 (KP.exists_pair hKP) pair F)
      (rt_domain_l hKP.1 (KP.exists_pair hKP) hZ nz pair n F))

theorem rt_ordinal_sequence_l (F n : (N).Domain) :
    (N).IsOrdinalValuedSequence J F n ↔ M.IsOrdinalValuedSequence I F.val n.val := by
  refine and_congr (rt_sequence_l hKP hZ nz pair F n) ?_
  constructor
  · intro h i hi x hix
    have ix := rd_entry_transitive_l hZ F.property hix
    exact (rt_ordinal_iff_l hZ nz hKP ⟨x, ix.2⟩).mp
      (h ⟨i, ix.1⟩ hi ⟨x, ix.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hix))
  · intro h i hi x hix
    exact rt_ordinal_l hZ nz x (h i.val hi x.val ((rt_entry_l hZ nz hKP.1 ..).mp hix))

end YesMetaZFC.SetTheory.Internal
