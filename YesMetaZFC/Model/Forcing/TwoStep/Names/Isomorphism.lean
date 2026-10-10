import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Pull
import YesMetaZFC.Model.Forcing.TwoStep.Flatten.Value
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Composition

/-! # 单次二步扩张与双重泛型扩张的同构

二步等号与嵌套等号精确对应，给出商类上的求值单射。任意第二阶段名称经实际
内部摊平取得原二步名称代表，因此映射满射，且两个成员结构精确对应。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
local notation "E" => extension_l M hZF B R z U
variable {Q D J : (extension_l M hZF B R z U).Domain}
variable {H : (extension_l M hZF B R z U).Domain → Prop}
variable (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
variable (hJ : ∀ p q, (extension_l M hZF B R z U).mem p Q → (extension_l M hZF B R z U).mem q Q →
  (Entry_d (extension_l M hZF B R z U) p q D ↔ Entry_d (extension_l M hZF B R z U) p q J))
variable (K : Cond_order_d (extension_l M hZF B R z U) Q J Q)
variable (hH : Generic_d (extension_l M hZF B R z U) Q J Q H)
local notation "V" => Compose_generic_d M B R z C U H
local notation "N" => extension_l E (preserves_zf_l O hZF hU) Q J Q H
local notation "F" => extension_l M hZF C S C V
include O hZF hU h L hA hT hJ K hH

/-- 组合泛型接受的原名称等号决定唯一双重值；第二阶段允许先规范化关系。 -/
theorem curry_value_congr_l {x y} (hx : Name_d M C x) (hy : Name_d M C y)
    (he : ∃ c, V c ∧ Eq_force_d M C S C c x y) {a d : (N).Domain}
    (ha : Curry_val_d M hZF B R z C U Q J H x a) (hd : Curry_val_d M hZF B R z C U Q J H y d) : a = d := by
  obtain ⟨c, ⟨_, p, s, q, hcp, hp, hsq, hq⟩, hxy⟩ := he
  obtain ⟨u, v, hxu, hu, hva⟩ := ha
  obtain ⟨t, w, hyt, ht, hwd⟩ := hd
  have hEq := curry_eq_push_l O hZF h L hU hA hT hx hy hxy hcp hp hxu hyt hsq hu ht
  have hEq' := (eq_force_order_l hJ (preserves_zf_l O hZF hU) (qval_name_l hva) (qval_name_l hwd)).mp hEq
  exact (qval_eq_l K (preserves_zf_l O hZF hU) hH hva hwd).mp ⟨q, hq, hEq'⟩

/-- 双重值相等恰好等于原二步名称被组合泛型迫使相等。 -/
theorem curry_value_eq_l (hb : U b) {x y} (hx : Name_d M C x) (hy : Name_d M C y) {a d : (N).Domain}
    (ha : Curry_val_d M hZF B R z C U Q J H x a) (hd : Curry_val_d M hZF B R z C U Q J H y d) :
    (∃ c, V c ∧ Eq_force_d M C S C c x y) ↔ a = d := by
  refine ⟨fun he => curry_value_congr_l O hZF hU h L hA hT hJ K hH hx hy he ha hd, fun he => ?_⟩
  obtain ⟨u, v, hxu, hu, hva⟩ := ha
  obtain ⟨t, w, hyt, ht, hwd⟩ := hd
  obtain ⟨q, hq, hvw⟩ := (qval_eq_l K (preserves_zf_l O hZF hU) hH hva hwd).mpr he
  have hvw' := (eq_force_order_l hJ (preserves_zf_l O hZF hU) (qval_name_l hva) (qval_name_l hwd)).mpr hvw
  obtain ⟨c, p, s, hc, hp, hcp, hsq⟩ := (two_step_fiber_l O hZF hU h hb hA q).mp (hH.proper q hq).1
  obtain ⟨r, l, hrc, hrl, hl, hxy⟩ := curry_eq_pull_l O hZF h L hU hA hT hx hy hc hcp hp hxu hyt hsq hu ht hvw'
  exact ⟨r, ⟨hrc.1, l, s, q, hrl, hl, hsq, hq⟩, hxy⟩

/-- 自动装配两个泛型扩张的成员结构同构，并保留逐名称的双重求值对应。 -/
theorem two_step_iso_l (hb : U b) : ∃ e : (F).Domain → (N).Domain,
    (∀ a t, Qval_d M C S C V t a → Curry_val_d M hZF B R z C U Q J H t (e a)) ∧
    (∀ a d, a ∈ d ↔ e a ∈ e d) ∧ Function.Injective e ∧ Function.Surjective e := by
  have hV := (two_step_compose_l O hZF hU h L hb hA hT ((generic_order_l hJ H).mpr hH)).1
  have total (a : (F).Domain) : ∃ w : (N).Domain, ∃ t,
      Qval_d M C S C V t a ∧ Curry_val_d M hZF B R z C U Q J H t w := by
    obtain ⟨t, ht, hta⟩ := value_name_l a
    obtain ⟨w, hw, _⟩ := curry_value_l O hZF hU h hA ht
    exact ⟨w, t, hta, hw⟩
  obtain ⟨e, he⟩ := Classical.axiomOfChoice total
  have val a t (ht : Qval_d M C S C V t a) : Curry_val_d M hZF B R z C U Q J H t (e a) := by
    obtain ⟨s, hs, hv⟩ := he a
    obtain ⟨w, hw, _⟩ := curry_value_l O hZF hU h hA (qval_name_l ht)
    have hst := (qval_eq_l L hZF hV hs ht).mpr rfl
    have heq := curry_value_congr_l O hZF hU h L hA hT hJ K hH (qval_name_l hs) (qval_name_l ht) hst hv hw
    exact heq.symm ▸ hw
  have mem a w : w ∈ e a ↔ ∃ d, d ∈ a ∧ e d = w := by
    obtain ⟨t, ht, hv⟩ := he a
    constructor
    · intro hw
      obtain ⟨s, c, hsc, hc, hsw⟩ := (curry_value_mem_l O hZF hU K hH h hv).mp hw
      obtain ⟨d, hd⟩ := name_value_l (R := S) (z := C) (U := V) (name_entry_l M (qval_name_l ht) hsc).1
      exact ⟨d, (qval_mem_l L hZF hV ht).mpr ⟨s, c, hsc, hc, hd⟩,
        curry_value_unique_l hZF (val d s hd) hsw⟩
    · rintro ⟨d, hd, heq⟩
      obtain ⟨s, c, hsc, hc, hsd⟩ := (qval_mem_l L hZF hV ht).mp hd
      exact (curry_value_mem_l O hZF hU K hH h hv).mpr ⟨s, c, hsc, hc, heq ▸ val d s hsd⟩
  have inj : Function.Injective e := by
    intro a d had
    obtain ⟨s, hs, ha⟩ := he a
    obtain ⟨t, ht, hd⟩ := he d
    exact (qval_eq_l L hZF hV hs ht).mp
      ((curry_value_eq_l O hZF hU h L hA hT hJ K hH hb (qval_name_l hs) (qval_name_l ht) ha hd).mpr had)
  have surj : Function.Surjective e := by
    intro w
    obtain ⟨a, _, haw⟩ := value_name_l w
    obtain ⟨x, _, hxa⟩ := value_name_l a
    obtain ⟨f, hf⟩ := flat_exists_l M hZF B R z C x
    obtain ⟨v, hfv⟩ := name_value_l (R := S) (z := C) (U := V) (flat_name_l M hZF hf)
    exact ⟨v, curry_value_unique_l hZF (val v f hfv)
      (flat_value_l O hZF hU h L hb hA hT hJ K hH hf hxa haw)⟩
  refine ⟨e, val, fun a d => ?_, inj, surj⟩
  constructor
  · intro had
    exact (mem d (e a)).mpr ⟨a, had, rfl⟩
  · intro had
    obtain ⟨c, hc, hec⟩ := (mem d (e a)).mp had
    exact inj hec ▸ hc

end YesMetaZFC.Model.Forcing.Internal
