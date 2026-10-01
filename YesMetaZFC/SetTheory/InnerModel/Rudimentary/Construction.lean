import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Syntax
import YesMetaZFC.SetTheory.KP.Kuratowski

/-! # 在 KP 中实际构造 rudimentary 运算

首先处理任意关系的纤维及纤维族：输入可以含非有序对对象，坐标由两次并集
统一界住。F₈ 使用已经证明的 Δ₀ 替换，不假定输出集合或其函数图预先存在。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def rd_entry0_m {n} (x y R : Term n) : Formula 1 n :=
  Formula.existsMem R (kpair0_m .newest x.weaken y.weaken)
derive_free_closed rd_entry0_m

theorem rd_entry0_delta_l {n} (x y R : Term n) : (rd_entry0_m x y R).IsDelta0 :=
  .existsMem _ (kpair0_delta_l ..)

theorem rd_entry0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x y R : Term n) :
    Formula.satisfies ρ (rd_entry0_m x y R) ↔ Rd_entry_d (x.eval ρ) (y.eval ρ) (R.eval ρ) := by
  simp only [rd_entry0_m, Rd_entry_d, Formula.satisfies_existsMem_iff, kpair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact exists_congr fun _ => and_comm

theorem rd_entry_bound_l {R S T x y : M.Domain} (hS : M.IsUnionOf S R) (hT : M.IsUnionOf T S)
    (h : Rd_entry_d x y R) : M.mem x T ∧ M.mem y T := by
  obtain ⟨p, hp, hpR⟩ := h
  have bound z (hz : z = x ∨ z = y) : M.mem z T := by
    obtain ⟨q, hq, hz⟩ := (kpair_union_l M hp z).mpr hz
    exact (hT z).mpr ⟨q, (hS q).mpr ⟨p, hpR, hq⟩, hz⟩
  exact ⟨bound x (Or.inl rfl), bound y (Or.inr rfl)⟩

theorem rd_entry_transitive_l {T F a b : M.Domain} (hT : M.TransitiveSet T) (hF : M.mem F T)
    (h : Rd_entry_d a b F) : M.mem a T ∧ M.mem b T := by
  obtain ⟨p, hp, hpf⟩ := h
  have lift z (hz : z = a ∨ z = b) : M.mem z T := by
    obtain ⟨s, hs, hz⟩ := (kpair_union_l M hp z).mpr hz
    exact hT s (hT p (hT F hF p hpf) s hs) z hz
  exact ⟨lift a (Or.inl rfl), lift b (Or.inr rfl)⟩

def rd_triple0_m {n} (p x y z : Term n) : Formula 1 n :=
  Formula.existsMem p (Formula.existsMem .newest
    (.conj (kpair0_m .newest y.weaken.weaken z.weaken.weaken) (kpair0_m p.weaken.weaken x.weaken.weaken .newest)))
derive_free_closed rd_triple0_m

theorem rd_triple0_delta_l {n} (p x y z : Term n) : (rd_triple0_m p x y z).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (kpair0_delta_l ..)))

theorem rd_triple0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p x y z : Term n) :
    Formula.satisfies ρ (rd_triple0_m p x y z) ↔ Rd_triple_d (p.eval ρ) (x.eval ρ) (y.eval ρ) (z.eval ρ) := by
  simp only [rd_triple0_m, Rd_triple_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨s, _, q, _, hq, hp⟩; exact ⟨q, hq, hp⟩
  · rintro ⟨q, hq, hp⟩
    obtain ⟨s, hs, hqs⟩ := (kpair_union_l M hp q).mpr (Or.inr rfl)
    exact ⟨s, hs, q, hqs, hq, hp⟩

/-- 纤维图的反向包含只量化关系码内的实际坐标。 -/
def rd_fiber0_m {n} (R y D : Term n) : Formula 1 n :=
  .conj (Formula.forallMem D (rd_entry0_m .newest y.weaken R.weaken))
    (Formula.forallMem R (Formula.forallMem .newest (Formula.forallMem .newest
      (.imp (kpair0_m (.bound 2) .newest y.weaken.weaken.weaken) (.mem .newest D.weaken.weaken.weaken)))))
derive_free_closed rd_fiber0_m

theorem rd_fiber0_delta_l {n} (R y D : Term n) : (rd_fiber0_m R y D).IsDelta0 :=
  .conj (.forallMem _ (rd_entry0_delta_l ..))
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.mem _ _)))))

theorem rd_fiber0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R y D : Term n) :
    Formula.satisfies ρ (rd_fiber0_m R y D) ↔ Rd_fiber_d (R.eval ρ) (y.eval ρ) (D.eval ρ) := by
  simp only [rd_fiber0_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hE, kpair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g⟩ x
    refine ⟨h x, fun ⟨p, hp, hpR⟩ => ?_⟩
    obtain ⟨s, hs, hxs⟩ := (kpair_union_l M hp x).mpr (Or.inl rfl)
    exact g p hpR s hs x hxs hp
  · intro h
    exact ⟨fun x => (h x).mp, fun p hp _ _ x _ hx => (h x).mpr ⟨p, hx, hp⟩⟩

theorem rd_fiber_exists_l (hKP : M.Models KP) (R y : M.Domain) : ∃ D, Rd_fiber_d R y D := by
  obtain ⟨S, hS⟩ := KP.exists_union hKP R
  obtain ⟨T, hT⟩ := KP.exists_union hKP S
  let ρ : Env M 2 := (⟨fun _ => R, fun _ => R⟩ : Env M 1).push y
  let φ : Delta0UnarySchema 2 := {
    body := rd_entry0_m .newest (.bound 1) (.bound 2)
    delta0 := rd_entry0_delta_l .. }
  obtain ⟨D, hD⟩ := KP.separation_exists_d hKP φ ρ T
  refine ⟨D, fun x => (hD x).trans ?_⟩
  rw [show Formula.satisfies (ρ.push x) φ.body ↔ Rd_entry_d x y R from rd_entry0_sat_l hKP.1 _ _ _ _]
  exact ⟨And.right, fun h => ⟨(rd_entry_bound_l hS hT h).1, h⟩⟩

/-- Jensen 的 F₈：全部第二坐标纤维组成实际集合，且包含空纤维。 -/
theorem rd_fibers_exists_l (hKP : M.Models KP) (R Y : M.Domain) :
    ∃ W, ∀ D, M.mem D W ↔ ∃ y, M.mem y Y ∧ Rd_fiber_d R y D := by
  let ρ : Env M 1 := ⟨fun _ => R, fun _ => R⟩
  let φ : Delta0BinarySchema 1 := {
    body := rd_fiber0_m (.bound 2) (.bound 1) .newest
    delta0 := rd_fiber0_delta_l .. }
  have hφ y D : φ.toBinarySchema.denote ρ y D ↔ Rd_fiber_d R y D := rd_fiber0_sat_l hKP.1 _ _ _ _
  simpa only [hφ] using KP.d0_image_l hKP φ ρ Y
    (fun y _ => (rd_fiber_exists_l hKP R y).imp (fun D hD => (hφ y D).mpr hD))
    (fun y _ D E hD hE => hKP.1.eq_of_same_members D E
      (fun x => ((hφ y D).mp hD x).trans ((hφ y E).mp hE x).symm))

theorem rd_triples_exists_l (hKP : M.Models KP) (A B C : M.Domain) :
    ∃ W, ∀ t, M.mem t W ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ ∃ c, M.mem c C ∧ Rd_triple_d t a b c := by
  obtain ⟨P, hP⟩ := KP.kprod_exists_l hKP B C
  obtain ⟨W, hW⟩ := KP.kprod_exists_l hKP A P
  refine ⟨W, fun t => (hW t).trans ?_⟩
  constructor
  · rintro ⟨a, ha, p, hp, ht⟩
    obtain ⟨b, hb, c, hc, hp⟩ := (hP p).mp hp
    exact ⟨a, ha, b, hb, c, hc, p, hp, ht⟩
  · rintro ⟨a, ha, b, hb, c, hc, p, hp, ht⟩
    exact ⟨a, ha, p, (hP p).mpr ⟨b, hb, c, hc, hp⟩, ht⟩

private theorem mixed_exists_l (hKP : M.Models KP) (k : Bool) (X R z : M.Domain) :
    ∃ W, Rd_fun_d (if k then .last else .mid) X R z W := by
  obtain ⟨S, hS⟩ := KP.exists_union hKP R
  obtain ⟨T, hT⟩ := KP.exists_union hKP S
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo hKP X T
  obtain ⟨B, hB⟩ := rd_triples_exists_l hKP U U U
  let ρ : Env M 3 := ((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push U
  let φ : Delta0UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
      (.conj (if k then .conj (.mem .newest (.bound 6)) (rd_entry0_m (.bound 2) (.bound 1) (.bound 5))
        else .conj (.mem (.bound 1) (.bound 6)) (rd_entry0_m (.bound 2) .newest (.bound 5)))
        (rd_triple0_m (.bound 3) (.bound 2) (.bound 1) .newest))))
    freeClosed := by cases k <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj
      (by cases k <;> exact .conj (.mem _ _) (rd_entry0_delta_l ..)) (rd_triple0_delta_l ..)))) }
  have hφ t : φ.toUnarySchema.denote ρ t ↔ ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧
      (if k then M.mem c X ∧ Rd_entry_d a b R else M.mem b X ∧ Rd_entry_d a c R) ∧ Rd_triple_d t a b c := by
    cases k <;> simp only [UnarySchema.denote, φ, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_existsMem_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hKP.1, rd_triple0_sat_l hKP.1] <;> rfl
  obtain ⟨W, hW⟩ := KP.separation_exists_d hKP φ ρ B
  refine ⟨W, fun t => (hW t).trans ?_⟩
  change (M.mem t B ∧ φ.toUnarySchema.denote ρ t) ↔ _
  rw [hφ t]
  constructor
  · rintro ⟨_, a, _, b, _, c, _, h, ht⟩
    cases k <;> exact ⟨a, b, c, h.1, h.2, ht⟩
  · intro h
    have pack a b c (ha : M.mem a U) (hb : M.mem b U) (hc : M.mem c U)
        (h : if k then M.mem c X ∧ Rd_entry_d a b R else M.mem b X ∧ Rd_entry_d a c R)
        (ht : Rd_triple_d t a b c) : M.mem t B ∧ ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧
          (if k then M.mem c X ∧ Rd_entry_d a b R else M.mem b X ∧ Rd_entry_d a c R) ∧ Rd_triple_d t a b c :=
      And.intro ((hB t).mpr ⟨a, ha, b, hb, c, hc, ht⟩) ⟨a, ha, b, hb, c, hc, h, ht⟩
    cases k with
    | false =>
      obtain ⟨a, b, c, hb, hr, ht⟩ := h
      have ha := rd_entry_bound_l hS hT hr
      exact pack a b c ((hU a).mpr (Or.inr ha.1)) ((hU b).mpr (Or.inl hb))
        ((hU c).mpr (Or.inr ha.2)) ⟨hb, hr⟩ ht
    | true =>
      obtain ⟨a, b, c, hc, hr, ht⟩ := h
      have ha := rd_entry_bound_l hS hT hr
      exact pack a b c ((hU a).mpr (Or.inr ha.1)) ((hU b).mpr (Or.inr ha.2))
        ((hU c).mpr (Or.inl hc)) ⟨hc, hr⟩ ht

theorem rd_opair_value_l (hE : Extensional M) {p x y z : M.Domain} (h : KPair_d M p x y) :
    Rd_fun_d .opair x y z p := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  intro v
  refine (hp v).trans (or_congr ?_ ?_)
  · exact ⟨fun h => h.symm ▸ hs, fun hv => hv.eq hE hs⟩
  · exact ⟨fun h => h.symm ▸ ht, fun hv => hE.eq_of_same_members v t (fun a => (hv a).trans (ht a).symm)⟩

theorem rd_triple_value_l (hE : Extensional M) {p x y z : M.Domain} (h : Rd_triple_d p x y z) :
    Rd_fun_d .triple x y z p := by
  obtain ⟨q, hq, hp⟩ := h
  intro t
  refine (rd_opair_value_l (z := z) hE hp t).trans (or_congr Iff.rfl ?_)
  exact ⟨fun ht => ⟨q, hq, ht⟩, fun ⟨r, hr, ht⟩ => (kpair_unique_l M hE hr hq) ▸ ht⟩

theorem rd_adj_value_l (hE : Extensional M) {p q x y z : M.Domain}
    (hq : KPair_d M q y z) (hp : Pair_d M p x q) : Rd_fun_d .adj x y z p := by
  intro t
  refine (hp t).trans (or_congr Iff.rfl ?_)
  exact ⟨fun ht => ht.symm ▸ hq, fun ht => kpair_unique_l M hE ht hq⟩

/-- 九项基础运算及四项传递性辅助运算在每个 KP 模型内全定义。 -/
theorem rd_fun_exists_l (hKP : M.Models KP) (k : Rd_sym) (x y z : M.Domain) :
    ∃ w, Rd_fun_d k x y z w := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  cases k with
  | pair => exact KP.exists_pair hKP x y
  | diff => exact KP.difference_exists_d hKP y x
  | prod =>
    obtain ⟨w, hw⟩ := KP.kprod_exists_l hKP x y
    exact ⟨w, fun t => (hw t).trans ⟨fun ⟨a, ha, b, hb, ht⟩ => ⟨a, b, ha, hb, ht⟩,
      fun ⟨a, b, ha, hb, ht⟩ => ⟨a, ha, b, hb, ht⟩⟩⟩
  | mid => exact mixed_exists_l hKP false x y z
  | last => exact mixed_exists_l hKP true x y z
  | union => exact KP.exists_union hKP x
  | range =>
    obtain ⟨S, hS⟩ := KP.exists_union hKP x
    obtain ⟨T, hT⟩ := KP.exists_union hKP S
    let ρ : Env M 2 := (⟨fun _ => x, fun _ => x⟩ : Env M 1).push T
    let φ : Delta0UnarySchema 2 := {
      body := Formula.existsMem (.bound 1) (rd_entry0_m .newest (.bound 1) (.bound 3))
      delta0 := .existsMem _ (rd_entry0_delta_l ..) }
    have hφ t : φ.toUnarySchema.denote ρ t ↔ ∃ a, M.mem a T ∧ Rd_entry_d a t x := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hKP.1]
      rfl
    obtain ⟨w, hw⟩ := KP.separation_exists_d hKP φ ρ T
    refine ⟨w, fun t => (hw t).trans ?_⟩
    change (M.mem t T ∧ φ.toUnarySchema.denote ρ t) ↔ _
    rw [hφ t]
    exact ⟨fun ⟨_, a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ =>
      ⟨(rd_entry_bound_l hS hT h).2, a, (rd_entry_bound_l hS hT h).1, h⟩⟩
  | mem =>
    obtain ⟨B, hB⟩ := KP.kprod_exists_l hKP x x
    let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
    let φ : Delta0UnarySchema 1 := {
      body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
        (.conj (.mem (.bound 1) .newest) (kpair0_m (.bound 2) (.bound 1) .newest)))
      delta0 := .existsMem _ (.existsMem _ (.conj (.mem _ _) (kpair0_delta_l ..))) }
    have hφ t : φ.toUnarySchema.denote ρ t ↔
        ∃ a, M.mem a x ∧ ∃ b, M.mem b x ∧ M.mem a b ∧ KPair_d M t a b := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff, kpair0_sat_l hKP.1]
      rfl
    obtain ⟨w, hw⟩ := KP.separation_exists_d hKP φ ρ B
    refine ⟨w, fun t => (hw t).trans ?_⟩
    change (M.mem t B ∧ φ.toUnarySchema.denote ρ t) ↔ _
    rw [hφ t]
    exact ⟨fun ⟨_, a, ha, b, hb, h, ht⟩ => ⟨a, b, ha, hb, h, ht⟩,
      fun ⟨a, b, ha, hb, h, ht⟩ => ⟨(hB t).mpr ⟨a, ha, b, hb, ht⟩, a, ha, b, hb, h, ht⟩⟩
  | fibers => exact rd_fibers_exists_l hKP x y
  | opair => exact (I.total x y).imp (fun p hp => rd_opair_value_l hKP.1 hp)
  | triple =>
    obtain ⟨q, hq⟩ := I.total y z
    obtain ⟨p, hp⟩ := I.total x q
    exact ⟨p, rd_triple_value_l hKP.1 ⟨q, hq, hp⟩⟩
  | adj =>
    obtain ⟨q, hq⟩ := I.total y z
    obtain ⟨p, hp⟩ := KP.exists_pair hKP x q
    exact ⟨p, rd_adj_value_l hKP.1 hq hp⟩
  | fiber => exact rd_fiber_exists_l hKP x y

end YesMetaZFC.SetTheory.InnerModel
