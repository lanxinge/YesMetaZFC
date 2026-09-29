import YesMetaZFC.Model.Forcing.GroundTransfer
import YesMetaZFC.SetTheory.PartialFunction

/-! # 部分函数条件的泛型函数名称

把条件中的有序对赋以该条件为权重，构造泛型并图的实际内部名称。
这里只消费图的边界、共同加强及逐坐标全定义，供塌缩和参数化 Cohen 添加共同使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

theorem check_image_l (hZF : M.Models ZF) {b} (hb : M.mem b B) (A : M.Domain) :
    ∃ S, (∀ t, M.mem t S ↔ ∃ a, M.mem a A ∧ Check_d M b a t) ∧
      ∀ t, M.mem t S → Name_d M B t := by
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : BinarySchema 1 := { body := check_m (.bound 2) (.bound 1) .newest }
  have hφ a t : φ.denote ρ a t ↔ Check_d M b a t := check_sat_l M hZF.1 ((ρ.push a).push t) (.bound 2) (.bound 1) .newest
  obtain ⟨S, hS⟩ := ZF.exists_functionalImageOn hZF φ ρ A (fun a _ => by
    obtain ⟨t, ht, _, _⟩ := zf_check_l M hZF hb a
    exact ⟨t, (hφ a t).mpr ht⟩) (fun a _ s t hs ht =>
      check_unique_l M hZF.1 (check_ind_l M hZF) b a s t ((hφ a s).mp hs) ((hφ a t).mp ht))
  have hs t : M.mem t S ↔ ∃ a, M.mem a A ∧ Check_d M b a t :=
    (hS t).trans (exists_congr fun a => and_congr_right fun _ => hφ a t)
  refine ⟨S, hs, fun t ht => ?_⟩
  obtain ⟨a, _, hat⟩ := (hs t).mp ht
  obtain ⟨s, has, hsn, _⟩ := zf_check_l M hZF hb a
  exact check_unique_l M hZF.1 (check_ind_l M hZF) b a s t has hat ▸ hsn

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
variable {hEN : Extensional (extension_l M hZF B R z U)}
  {hPN : ∀ a b, ∃ p, Pair_d (extension_l M hZF B R z U) p a b}
include O hZF hU hEN hPN

/-- 泛型并图自动成为扩张内的集合函数，并给出每个有序对的精确来源。 -/
theorem generic_function_l {X Y b} (hb : U b)
    (hp : ∀ {p}, U p → Pfn_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) X Y p)
    (hR : ∀ p q, Entry_d M p q R → M.MemberSubset q p)
    (input : ∀ a, M.mem a X → ∃ p, U p ∧ ∃ c, Entry_d M a c p)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, (E).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a)) :
    ∃ F : (E).Domain, (E).IsSetFunctionFromTo (kpair_interpretation_l E hEN hPN) F (e X) (e Y) ∧
      ∀ x y, Entry_d E x y F ↔ ∃ p, U p ∧ ∃ a c, Entry_d M a c p ∧ e a = x ∧ e c = y := by
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF J X Y
  obtain ⟨S, hS, hs⟩ := check_image_l hZF (hU.proper b hb).1 P
  let φ : BinarySchema 1 := {
    body := .existsE (.conj (check_m (.bound 3) .newest (.bound 2)) (.mem .newest (.bound 1))) }
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  have hφ s p : φ.denote ρ s p ↔ ∃ a, Check_d M b a s ∧ M.mem a p := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      check_sat_l M hZF.1, Formula.satisfies_mem_iff]
    rfl
  obtain ⟨t, ht, _, hte⟩ := name_comp_l M hZF φ ρ B S hs
  obtain ⟨F, hF⟩ := name_value_l (R := R) (z := z) (U := U) ht
  have hm (x : (E).Domain) : (E).mem x F ↔ ∃ p, U p ∧ ∃ a, M.mem a p ∧ e a = x := by
    constructor
    · intro hx
      obtain ⟨s, p, hsp, hp, hsx⟩ := (qval_mem_l O hZF hU hF).mp hx
      obtain ⟨a, has, hap⟩ := (hφ s p).mp ((hte s p).mp hsp).2.2
      exact ⟨p, hp, a, hap, qval_unique_l (hv a s has) hsx⟩
    · rintro ⟨p, hp', a, hap, rfl⟩
      obtain ⟨i, c, hac⟩ := (hp hp').1.1 a hap
      have hic := (hp hp').2 i c ⟨a, hac, hap⟩
      obtain ⟨s, has, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 a
      exact (qval_mem_l O hZF hU hF).mpr ⟨s, p, (hte s p).mpr
        ⟨(hS s).mpr ⟨a, (hP a).mpr ⟨i, hic.1, c, hic.2, hac⟩, has⟩,
          (hU.proper p hp').1, (hφ s p).mpr ⟨a, has, hap⟩⟩, hp', hv a s has⟩
  have hf (x y : (E).Domain) : Entry_d E x y F ↔
      ∃ p, U p ∧ ∃ a c, Entry_d M a c p ∧ e a = x ∧ e c = y := by
    constructor
    · rintro ⟨q, hq, hqF⟩
      obtain ⟨p, hp', a, hap, rfl⟩ := (hm q).mp hqF
      obtain ⟨i, c, hic⟩ := (hp hp').1.1 a hap
      obtain ⟨hx, hy⟩ := kpair_injective_l E (image_kpair_l e he hic) hq
      exact ⟨p, hp', i, c, ⟨a, hic, hap⟩, hx, hy⟩
    · rintro ⟨p, hp', a, c, ⟨q, hq, hqp⟩, rfl, rfl⟩
      exact ⟨e q, image_kpair_l e he hq, (hm (e q)).mpr ⟨p, hp', q, hqp, rfl⟩⟩
  refine ⟨F, ⟨⟨?_, ?_⟩, ?_, ?_⟩, hf⟩
  · intro q hq
    obtain ⟨p, hp', a, hap, rfl⟩ := (hm q).mp hq
    obtain ⟨i, c, hic⟩ := (hp hp').1.1 a hap
    exact ⟨e i, e c, image_kpair_l e he hic⟩
  · intro x y z hxy hxz
    obtain ⟨p, hp', a, c, hac, hax, hcy⟩ := (hf x y).mp hxy
    obtain ⟨q, hq', d, f, hdf, hdx, hfz⟩ := (hf x z).mp hxz
    have had := hi (hax.trans hdx.symm)
    subst d
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp' hq'
    have sub {s} (hrs : Entry_d M r s R) {i j} (hij : Entry_d M i j s) : Entry_d M i j r := by
      obtain ⟨v, hv, hvs⟩ := hij
      exact ⟨v, hv, hR r s hrs v hvs⟩
    have hcf := (hp hr).1.2 a c f (sub hrp hac) (sub hrq hdf)
    exact hcy.symm.trans ((congrArg e hcf).trans hfz)
  · intro x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
      obtain ⟨p, hp', c, hac⟩ := input a ha
      exact ⟨e c, (hf (e a) (e c)).mpr ⟨p, hp', a, c, hac, rfl, rfl⟩⟩
    · rintro ⟨y, hxy⟩
      obtain ⟨p, hp', a, c, hac, rfl, _⟩ := (hf x y).mp hxy
      exact (image_member_l e hi he).mpr ((hp hp').2 a c hac).1
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
    obtain ⟨p, hp', c, hac⟩ := input a ha
    exact ⟨e c, (image_member_l e hi he).mpr ((hp hp').2 a c hac).2,
      (hf (e a) (e c)).mpr ⟨p, hp', a, c, hac, rfl, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal
