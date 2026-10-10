import YesMetaZFC.SetTheory.InnerModel.Jensen.Collection

/-! # Jensen 类的实际隶属结构及 KP 模型性 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def l_model_l (hM : M.Models KPi) : Structure.{u} where
  Domain := {x : M.Domain // L_d x}
  nonempty := by
    obtain ⟨e, he⟩ := KP.exists_empty (KPi.models_iff_l.mp hM).1
    exact ⟨⟨e, l_ordinal_l hM (Structure.IsOrdinal.of_no_members he)⟩⟩
  mem x y := M.mem x.val y.val

theorem l_model_ext_l (hM : M.Models KPi) : Extensional (l_model_l hM) := by
  refine ⟨fun a b h => Subtype.ext ((KPi.models_iff_l.mp hM).1.1.eq_of_same_members a.val b.val (fun x => ?_))⟩
  exact ⟨fun hx => (h ⟨x, l_transitive_l hM a.property hx⟩).mp hx,
    fun hx => (h ⟨x, l_transitive_l hM b.property hx⟩).mpr hx⟩

theorem l_model_delta_l (hM : M.Models KPi) {n} {φ : Formula 1 n} (hφ : φ.IsDelta0)
    (ρ : Env (l_model_l hM) n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) φ :=
  delta0_image_l (M := l_model_l hM) (N := M) Subtype.val (fun _ _ h => Subtype.ext h)
    (fun a y => ⟨fun h => ⟨⟨y, l_transitive_l hM a.property h⟩, h, rfl⟩, fun ⟨_, hx, he⟩ => he ▸ hx⟩) hφ ρ

theorem l_closed_l (hM : M.Models KPi) (k : Rd_sym) {a b c t : M.Domain}
    (ha : L_d a) (hb : L_d b) (hc : L_d c) (ht : Rd_fun_d k a b c t) : L_d t := by
  let e : Fin 3 → M.Domain := Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))
  have he : ∀ i, L_d (e i) := Fin.cases ha (Fin.cases hb (Fin.cases hc (fun i => Fin.elim0 i)))
  obtain ⟨i, U, hi, hU⟩ := l_finite_bound_l hM e he
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l (KPi.models_iff_l.mp hM).1 hi.1
  obtain ⟨V, hv⟩ := jh_value_exists_l hM s
  have h := jh_step_spec_l hM (jh_successor_l hM hi.1 hs hi.2 hv)
  exact ⟨s, V, ⟨ho, hv⟩, h.1 k a b c (h.2.1 a (hU 0)) (h.2.1 b (hU 1)) (h.2.1 c (hU 2)) t ht⟩

theorem l_model_separation_l (hM : M.Models KPi) {n} (φ : Delta0UnarySchema n)
    (ρ : Env (l_model_l hM) n) (X : (l_model_l hM).Domain) :
    ∃ Y : (l_model_l hM).Domain, ∀ x, (l_model_l hM).mem x Y ↔
      (l_model_l hM).mem x X ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨Y, hy, hY⟩ := l_separation_l (M := M) hM φ (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ)
    (fun i => by exact (ρ.bound i).property) X.property
  refine ⟨⟨Y, hy⟩, fun x => (hY x.val).trans (and_congr_right fun _ => ?_)⟩
  symm
  have h := l_model_delta_l hM φ.delta0 (ρ.push x)
  rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
  exact h

theorem l_model_collection_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n)
    (ρ : Env (l_model_l hM) n) (X : (l_model_l hM).Domain)
    (ht : ∀ x, (l_model_l hM).mem x X → ∃ y, φ.toBinarySchema.denote ρ x y) :
    ∃ Y : (l_model_l hM).Domain, ∀ x, (l_model_l hM).mem x X →
      ∃ y, (l_model_l hM).mem y Y ∧ φ.toBinarySchema.denote ρ x y := by
  have tr x y : φ.toBinarySchema.denote ρ x y ↔
      φ.toBinarySchema.denote (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) x.val y.val := by
    have h := l_model_delta_l hM φ.delta0 ((ρ.push x).push y)
    rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val (ρ.push x) y,
      image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
    exact h
  obtain ⟨Y, hy, hY⟩ := l_collection_l (M := M) hM φ (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) X.val (by
    intro x hx
    let z : (l_model_l hM).Domain := ⟨x, l_transitive_l hM X.property hx⟩
    obtain ⟨y, hp⟩ := ht z hx
    exact ⟨y.val, y.property, (tr z y).mp hp⟩)
  refine ⟨⟨Y, hy⟩, fun x hx => ?_⟩
  obtain ⟨y, hyY, hp⟩ := hY x.val hx
  let z : (l_model_l hM).Domain := ⟨y, l_transitive_l hM hy hyY⟩
  exact ⟨z, hyY, (tr x z).mpr hp⟩

theorem l_model_kp_l (hM : M.Models KPi) : (l_model_l hM).Models KP := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let N := l_model_l hM
  have hE := l_model_ext_l hM
  have same (x y : N.Domain) : (∀ z, N.mem z x ↔ N.mem z y) ↔ x.val = y.val := by
    change (∀ z : N.Domain, M.mem z.val x.val ↔ M.mem z.val y.val) ↔ _
    exact ⟨fun h => congrArg Subtype.val (hE.eq_of_same_members x y h), fun h => h ▸ (fun _ => Iff.rfl)⟩
  refine ⟨hE, fun s hs => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  cases hs with
  | extensionality =>
    simp only [Axioms.extensionality, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hE]
    exact hE.eq_of_same_members
  | emptySet =>
    obtain ⟨e, he⟩ := KP.exists_empty hKP
    exact (Axioms.satisfies_emptySet_iff f).mpr
      ⟨⟨e, l_ordinal_l hM (Structure.IsOrdinal.of_no_members he)⟩, fun z => he z.val⟩
  | pairing =>
    apply (Axioms.satisfies_pairing_iff f).mpr
    intro x y
    obtain ⟨p, hp⟩ := KP.exists_pair hKP x.val y.val
    refine ⟨⟨p, l_closed_l hM .pair x.property y.property y.property hp⟩, fun z => ?_⟩
    exact (hp z.val).trans (or_congr (same z x).symm (same z y).symm)
  | union =>
    apply (Axioms.satisfies_union_iff f).mpr
    intro x
    obtain ⟨y, hy⟩ := KP.exists_union hKP x.val
    refine ⟨⟨y, l_closed_l hM .union x.property x.property x.property hy⟩, fun z => (hy z.val).trans ?_⟩
    exact ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, l_transitive_l hM x.property ha⟩, ha, hz⟩,
      fun ⟨a, ha, hz⟩ => ⟨a.val, ha, hz⟩⟩
  | foundation =>
    apply (Axioms.foundation_sat_iff_d f).mpr
    intro x hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d hKP ⟨z.val, hz⟩
    exact ⟨⟨a, l_transitive_l hM x.property ha⟩, ha, fun z hz => hm z.val hz⟩
  | infinity =>
    apply (Axioms.satisfies_infinity_iff f).mpr
    obtain ⟨ω, hω, hn⟩ := KPi.exists_omega_l hM
    have ht : M.TransitiveSet ω := fun a ha b hb => (hn b).mpr (((hn a).mp ha).mem_l hb)
    have ho := KP.ordinal_of_transitive_l hKP ht (fun a ha => KPi.n0_ordinal_l hM ((hn a).mp ha))
    have hL := l_ordinal_l hM ho
    refine ⟨⟨ω, hL⟩, ?_, fun x hx => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, l_transitive_l hM hL heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
      refine ⟨⟨s, l_transitive_l hM hL hsω⟩, fun z => (hs z.val).trans (or_congr_right ?_), hsω⟩
      exact ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩
  | separation φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ.toUnarySchema)).mpr
    intro b
    exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ.toUnarySchema).mpr (l_model_separation_l hM φ ⟨b, f⟩)
  | collection φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ.toBinarySchema)).mpr
    intro b
    exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ.toBinarySchema).mpr (l_model_collection_l hM φ ⟨b, f⟩)

end YesMetaZFC.SetTheory.InnerModel
