import YesMetaZFC.Model.SetTheory.Internal.SourceAlgebra
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

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

theorem rt_omega_l (hE : Extensional M) (ω : (rt_model_l X hn).Domain) (hω : M.IsOmega ω.val) :
    (rt_model_l X hn).IsOmega ω := by
  have induct (A : (rt_model_l X hn).Domain) : (rt_model_l X hn).IsInductive A ↔ M.IsInductive A.val := by
    constructor
    · rintro ⟨⟨z, hz, hzA⟩, hs⟩
      exact ⟨⟨z.val, fun x hx => hz ⟨x, hX z.val z.property x hx⟩ hx, hzA⟩, fun a ha => by
        obtain ⟨s, hs, hsA⟩ := hs ⟨a, hX A.val A.property a ha⟩ ha
        exact ⟨s.val, (rt_successor_l hX hn hE ..).mp hs, hsA⟩⟩
    · rintro ⟨⟨z, hz, hzA⟩, hs⟩
      exact ⟨⟨⟨z, hX A.val A.property z hzA⟩, fun x => hz x.val, hzA⟩, fun a ha => by
        obtain ⟨s, hs, hsA⟩ := hs a.val ha
        exact ⟨⟨s, hX A.val A.property s hsA⟩, (rt_successor_l hX hn hE ..).mpr hs, hsA⟩⟩
  exact ⟨(induct ω).mpr hω.1, fun A hA x hx => hω.2 A.val ((induct A).mp hA) x.val hx⟩

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
