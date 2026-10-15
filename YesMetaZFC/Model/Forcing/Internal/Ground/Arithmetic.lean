import YesMetaZFC.Model.Forcing.Internal.Ground.LegalMove
import YesMetaZFC.SetTheory.Descriptive.Game

/-! # 地嵌入保持内部有限算术与奇偶

直接搬运原递归图及其限制；自然数长度排除极限分支。证明不在地模型中
对目标模型的外部谓词作归纳，也不要求内部自然数在外部标准。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN hi he

omit hM hN in
theorem image_subset_iff_l {a b : M.Domain} : N.MemberSubset (e a) (e b) ↔ M.MemberSubset a b :=
  ⟨fun h x hx => (image_member_l e hi he).mp (h (e x) ((image_member_l e hi he).mpr hx)),
    fun h y hy => (he a y).mp hy |>.elim fun x hx => hx.2 ▸ (image_member_l e hi he).mpr (h x hx.1)⟩

theorem image_ord_l {α : M.Domain} (hα : M.IsOrdinal α) : N.IsOrdinal (e α) := by
  let ρ : Env M 1 := ⟨fun _ => α, fun _ => α⟩
  exact (KP.ord0_sat_l (ZF.modelsKP hN) (image_env_l e ρ) .newest).mp
    ((delta0_image_l e hi he (KP.ord0_delta_l .newest) ρ).mp ((KP.ord0_sat_l (ZF.modelsKP hM) ρ .newest).mpr hα))

theorem image_sequence_l {f n : M.Domain} (seq : M.IsSequenceOfLength I f n) :
    N.IsSequenceOfLength J (e f) (e n) := by
  obtain ⟨R, range⟩ := ZF.exists_range_of_setFunction hM I seq.2.1 seq.2.2
  have fn : M.IsSetFunctionFromTo I f n R := ⟨seq.2.1, seq.2.2, fun i hi => by
    obtain ⟨x, ix⟩ := (seq.2.2 i).mp hi
    exact ⟨x, (range x).mpr ⟨i, ix⟩, ix⟩⟩
  have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fn
  exact ⟨image_ord_l hM hN e hi he seq.1, fn'.1, fn'.2.1⟩

theorem image_restriction_l {g f n : M.Domain} (rel : M.IsSetRelation I f) (cut : M.IsRestrictionOf I g f n) :
    N.IsRestrictionOf J (e g) (e f) (e n) := by
  refine ⟨?_, fun x y => ?_⟩
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := (he g z).mp hz
    obtain ⟨a, b, code⟩ := cut.1 p hp
    exact ⟨e a, e b, image_kpair_l e he code⟩
  · constructor
    · intro ent
      obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he cut.1 x y).mp ent
      exact ⟨(image_member_l e hi he).mpr ((cut.2 a b).mp ab).1,
        (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 a b f).mp ((cut.2 a b).mp ab).2⟩
    · rintro ⟨xn, ent⟩
      obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he rel x y).mp ent
      exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 a b g).mp
        ((cut.2 a b).mpr ⟨(image_member_l e hi he).mp xn, ab⟩)

theorem image_last_sequence_l {f x : M.Domain} (last : M.IsSuccessorLengthSequenceWithLast I f x) :
    N.IsSuccessorLengthSequenceWithLast J (e f) (e x) := by
  obtain ⟨i, oi, n, succ, seq, ent⟩ := last
  exact ⟨e i, image_ord_l hM hN e hi he oi, e n, image_successor_l (hEN := hN.1) e hi he hM.1 succ,
    image_sequence_l hM hN e hi he seq, (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x f).mp ent⟩

/-- 已实现的加法、乘法阶段共用同一次有限递归图搬运。 -/
theorem image_finite_recursion_l {ω n x : M.Domain} {P : M.Domain → M.Domain → Prop} {Q : N.Domain → N.Domain → Prop}
    (hw : M.IsOmega ω) (hn : M.mem n ω)
    (step : ∀ f x i, M.mem i ω → M.IsSequenceOfLength I f i → P f x → Q (e f) (e x))
    (val : M.IsRecursionValue I P n x) : N.IsRecursionValue J Q (e n) (e x) := by
  obtain ⟨f, run, last⟩ := val
  refine ⟨e f, ⟨image_sequence_l hM hN e hi he run.1, ?_⟩, step f x n hn run.1 last⟩
  intro i hin y iy
  obtain ⟨i₀, hi₀, rfl⟩ := (he n i).mp hin
  obtain ⟨j, y₀, jy, ej, ey⟩ := (image_entries_l e he run.1.2.1.1 (e i₀) y).mp iy
  have eq := hi ej; subst j y
  obtain ⟨g, cut, value⟩ := run.2 i₀ hi₀ y₀ jy
  have sub := run.1.1.transitive i₀ hi₀
  exact ⟨e g, image_restriction_l hM hN e hi he run.1.2.1.1 cut,
    step g y₀ i₀ (hw.transitive hM n hn i₀ hi₀)
      ⟨run.1.1.mem hi₀, cut.isSetFunction run.1.2.1, cut.isDomainOf run.1.2.2 sub⟩ value⟩

theorem image_nat_add_l {ω a b x : M.Domain} (hw : M.IsOmega ω) (hb : M.mem b ω)
    (sum : M.IsOrdinalAddition I x a b) : N.IsOrdinalAddition J (e x) (e a) (e b) := by
  apply image_finite_recursion_l hM hN e hi he hw hb ?_ sum
  intro f x i hiω seq step
  rcases step with ⟨⟨z, fz, hz⟩, rfl⟩ | ⟨v, last, succ⟩ | ⟨k, limit, fk, _⟩
  · exact Or.inl ⟨⟨e z, image_sequence_l hM hN e hi he fz,
      fun y hy => (he z y).mp hy |>.elim fun v hv => hz v hv.1⟩, rfl⟩
  · exact Or.inr (Or.inl ⟨e v, image_last_sequence_l hM hN e hi he last,
      image_successor_l (hEN := hN.1) e hi he hM.1 succ⟩)
  · have eq := fk.2.2.eq hM.1 seq.2.2
    exact (KP.mem_irrefl_d (ZF.modelsKP hM) i (hw.subset_limitOrdinal hM (eq ▸ limit) i hiω)).elim

theorem image_even_l {ω n : M.Domain} (hw : M.IsOmega ω) :
    Gm_even_d I ω n ↔ Gm_even_d J (e ω) (e n) := by
  constructor
  · rintro ⟨k, hk, sum⟩
    exact ⟨e k, (image_member_l e hi he).mpr hk, image_nat_add_l hM hN e hi he hw hk sum⟩
  · rintro ⟨k, hk, sum⟩
    obtain ⟨k₀, hk₀, rfl⟩ := (he ω k).mp hk
    obtain ⟨s, hs, _⟩ := ZF.ordinalAddition_existsUnique hM I k₀ (hw.members_areOrdinals hM k₀ hk₀)
    obtain ⟨t, _, unique⟩ := ZF.ordinalAddition_existsUnique hN J (e k₀)
      (image_ord_l hM hN e hi he (hw.members_areOrdinals hM k₀ hk₀))
    have eq := hi ((unique (e s) (image_nat_add_l hM hN e hi he hw hk₀ hs)).trans (unique (e n) sum).symm)
    exact ⟨k₀, hk₀, eq ▸ hs⟩

theorem image_nat_mul_l {ω a b x : M.Domain} (hw : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω)
    (mul : M.IsOrdinalMultiplication I x a b) : N.IsOrdinalMultiplication J (e x) (e a) (e b) := by
  apply image_finite_recursion_l hM hN e hi he hw hb ?_ mul
  intro f x i hiω seq step
  have oa := hw.members_areOrdinals hM a ha
  rcases step with ⟨no, _⟩ | ⟨_, step⟩
  · exact (no oa).elim
  apply Or.inr ∘ And.intro (image_ord_l hM hN e hi he oa)
  rcases step with ⟨⟨z, fz, hz⟩, hx⟩ | ⟨v, last, sum⟩ | ⟨k, limit, fk, _⟩
  · exact Or.inl ⟨⟨e z, image_sequence_l hM hN e hi he fz,
      fun y hy => (he z y).mp hy |>.elim fun v hv => hz v hv.1⟩,
      fun y hy => (he x y).mp hy |>.elim fun v hv => hx v hv.1⟩
  · exact Or.inr (Or.inl ⟨e v, image_last_sequence_l hM hN e hi he last, image_nat_add_l hM hN e hi he hw ha sum⟩)
  · have eq := fk.2.2.eq hM.1 seq.2.2
    exact (KP.mem_irrefl_d (ZF.modelsKP hM) i (hw.subset_limitOrdinal hM (eq ▸ limit) i hiω)).elim

theorem image_nat_div_l {ω i c n r : M.Domain} (hw : M.IsOmega ω) (hc : M.mem c ω) (hn : M.mem n ω)
    (div : M.IsOrdinalDivision I i c n r) : N.IsOrdinalDivision J (e i) (e c) (e n) (e r) := by
  obtain ⟨on, rc, p, mul, sum⟩ := div
  exact ⟨image_ord_l hM hN e hi he on, (image_member_l e hi he).mpr rc, e p,
    image_nat_mul_l hM hN e hi he hw hc hn mul, image_nat_add_l hM hN e hi he hw (hw.transitive hM c hc r rc) sum⟩

end YesMetaZFC.Model.Forcing.Internal
