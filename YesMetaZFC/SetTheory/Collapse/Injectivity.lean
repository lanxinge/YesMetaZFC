import YesMetaZFC.SetTheory.Collapse.Recursion

/-! # 外延子结构的坍塌单射性及固定点

单射性对源对象作一次内部成员归纳。固定传递子集的结论供后续基数参数及
其子集的保持使用；归纳谓词均为实际原公式。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Mc_ext_d (X : M.Domain) : Prop := ∀ a, M.mem a X → ∀ b, M.mem b X →
  (∀ z, M.mem z X → (M.mem z a ↔ M.mem z b)) → a = b

theorem mc_value_injective_l (hM : M.Models KPi) {X a b y : M.Domain} (he : Mc_ext_d X)
    (ha : M.mem a X) (hb : M.mem b X) (h : Mc_value_d X a y) (g : Mc_value_d X b y) : a = b := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  let φ : UnarySchema 1 := { body := (.forallE <| .forallE <| .imp (.mem (.bound 2) (.bound 3)) <|
    .imp (.mem (.bound 1) (.bound 3)) <| .imp (mc_value_m (.bound 3) (.bound 2) .newest) <|
      .imp (mc_value_m (.bound 3) (.bound 1) .newest) (Formula.extensionalEq (.bound 2) (.bound 1))) }
  have sat a : φ.denote (mc_env_l X) a ↔ (∀ b y, M.mem a X → M.mem b X → Mc_value_d X a y → Mc_value_d X b y → a = b) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, mc_value_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ (mc_env_l X) ?_ a) b y ha hb h g
  intro a ih
  apply (sat a).mpr
  intro b y ha hb h g
  apply he a ha b hb
  intro z hz
  constructor
  · intro hza
    obtain ⟨v, hv⟩ := mc_value_exists_l hM X z
    obtain ⟨w, hwb, hw, hwv⟩ := (mc_value_equation_l hM g v).mp ((mc_value_equation_l hM h v).mpr ⟨z, hza, hz, hv⟩)
    have eq := (sat z).mp (ih z hza) w v hz hw hv hwv
    exact eq.symm ▸ hwb
  · intro hzb
    obtain ⟨v, hv⟩ := mc_value_exists_l hM X z
    obtain ⟨w, hwa, hw, hwv⟩ := (mc_value_equation_l hM h v).mp ((mc_value_equation_l hM g v).mpr ⟨z, hzb, hz, hv⟩)
    have eq := (sat w).mp (ih w hwa) z v hw hz hwv hv
    exact eq ▸ hwa

theorem mc_fixed_transitive_l (hM : M.Models KPi) {X A a y : M.Domain} (ht : M.TransitiveSet A)
    (hAX : M.MemberSubset A X) (ha : M.mem a A) (h : Mc_value_d X a y) : a = y := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  let ρ := (mc_env_l X).push A
  let φ : UnarySchema 2 := { body := (.forallE <| .imp (.mem (.bound 1) (.bound 2)) <|
    .imp (mc_value_m (.bound 3) (.bound 1) .newest) (Formula.extensionalEq (.bound 1) .newest)) }
  have sat a : φ.denote ρ a ↔ (∀ y, M.mem a A → Mc_value_d X a y → a = y) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, mc_value_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ ρ ?_ a) y ha h
  intro a ih
  apply (sat a).mpr
  intro y ha h
  apply hE.eq_of_same_members; intro z
  rw [mc_value_equation_l hM h z]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := mc_value_exists_l hM X z
    have eq := (sat z).mp (ih z hz) v (ht a ha z hz) hv
    subst v
    exact ⟨z, hz, hAX z (ht a ha z hz), hv⟩
  · rintro ⟨b, hb, _, hv⟩
    exact (sat b).mp (ih b hb) z (ht a ha b hb) hv ▸ hb

/-- X 包含传递参数 A 的所有成员时，X 中的任意 A 子集均被坍塌固定。 -/
theorem mc_fixed_subset_l (hM : M.Models KPi) {X A a y : M.Domain} (ht : M.TransitiveSet A)
    (hAX : M.MemberSubset A X) (ha : M.MemberSubset a A) (h : Mc_value_d X a y) : a = y := by
  apply (KPi.models_iff_l.mp hM).1.1.eq_of_same_members; intro z
  rw [mc_value_equation_l hM h z]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := mc_value_exists_l hM X z
    have eq := mc_fixed_transitive_l hM ht hAX (ha z hz) hv; subst v
    exact ⟨z, hz, hAX z (ha z hz), hv⟩
  · rintro ⟨b, hb, _, hv⟩
    exact mc_fixed_transitive_l hM ht hAX (ha b hb) hv ▸ hb

end YesMetaZFC.SetTheory
