import YesMetaZFC.Model.Forcing.Proper.Elementary.Membership
import YesMetaZFC.Model.Forcing.Proper.Hereditary.NameBound
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 内部初等模型的可数集合闭包

内部 ω 的全部元素由实际成员公式归纳进入 N；随后反射小单射图，利用图条目的
见证回拉，证明 N 中每个内部可数集合都是 N 的子集。两步均不使用外部枚举。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X R : M.Domain} (hM : Smdl_d I c X R)
  (hR : ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
  (hX : M.TransitiveSet X)
local notation "L" => smdl_structure_l I (R := R) (And.left (And.right hM))
include hR hX

theorem smem_subset_l (a b : (L).Domain) : (L).MemberSubset a b ↔ M.MemberSubset a.val b.val := by
  refine ⟨fun h x hx => ?_, fun h x hx => (smem_member_l I hM hR x b).mpr (h x.val ((smem_member_l I hM hR x a).mp hx))⟩
  let x' : (L).Domain := ⟨x, hX a.val a.property x hx⟩
  exact (smem_member_l I hM hR x' b).mp (h x' ((smem_member_l I hM hR x' a).mpr hx))

theorem smem_successor_l (hE : Extensional M) (s a : (L).Domain) :
    (L).SuccessorOf s a ↔ M.SuccessorOf s.val a.val := by
  have hEL := smem_ext_l I hM hR hX hE
  constructor
  · intro h x
    constructor
    · intro hx
      let x' : (L).Domain := ⟨x, hX s.val s.property x hx⟩
      rcases (h x').mp ((smem_member_l I hM hR x' s).mpr hx) with hx | hx
      · exact Or.inl ((smem_member_l I hM hR x' a).mp hx)
      · exact Or.inr (congrArg Subtype.val (hEL.eq_of_same_members x' a hx) ▸ fun _ => Iff.rfl)
    · rintro (hx | hx)
      · let x' : (L).Domain := ⟨x, hX a.val a.property x hx⟩
        exact (smem_member_l I hM hR x' s).mp ((h x').mpr (Or.inl ((smem_member_l I hM hR x' a).mpr hx)))
      · have he := hE.eq_of_same_members x a.val hx
        exact he.symm ▸ (smem_member_l I hM hR a s).mp h.predecessor_mem
  · intro h x
    rw [smem_member_l I hM hR x s, h x.val, smem_member_l I hM hR x a]
    exact or_congr Iff.rfl ⟨fun he => (Subtype.ext (hE.eq_of_same_members x.val a.val he)) ▸ fun _ => Iff.rfl,
      fun he => (congrArg Subtype.val (hEL.eq_of_same_members x a he)) ▸ fun _ => Iff.rfl⟩

/-- 传递集合中的函数图绝对；源与目标只需要各自实际的 Kuratowski 配对。 -/
theorem smem_function_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hL : ∀ a b : (L).Domain, ∃ p, Pair_d L p a b) (F A B : (L).Domain) :
    (L).IsSetFunctionFromTo (kpair_interpretation_l L (smem_ext_l I hM hR hX hE) hL) F A B ↔
      M.IsSetFunctionFromTo (kpair_interpretation_l M hE hP) F.val A.val B.val := by
  have hm (a : (L).Domain) y : M.mem y a.val ↔ ∃ s : (L).Domain, (L).mem s a ∧ s.val = y := by
    refine ⟨fun h => ⟨⟨y, hX a.val a.property y h⟩, (smem_member_l I hM hR _ a).mpr h, rfl⟩, ?_⟩
    rintro ⟨s, hs, rfl⟩
    exact (smem_member_l I hM hR s a).mp hs
  refine ⟨fun hf => image_function_l (M := L) (N := M) (hEN := hE) (hPN := hP)
    Subtype.val (fun _ _ he => Subtype.ext he) hm hf, fun hf => ?_⟩
  have coords {a b} (hab : Entry_d M a b F.val) : M.mem a X ∧ M.mem b X := by
    obtain ⟨p, hp, hpF⟩ := hab
    have hc x (hx : x = a ∨ x = b) : M.mem x X := by
      obtain ⟨v, hv, hxv⟩ := (kpair_union_l M hp x).mpr hx
      exact hX v (hX p (hX F.val F.property p hpF) v hv) x hxv
    exact ⟨hc a (Or.inl rfl), hc b (Or.inr rfl)⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    have hp' := (smem_member_l I hM hR p F).mp hp
    obtain ⟨a, b, hpab⟩ := hf.1.1 p.val hp'
    have hc := coords ⟨p.val, hpab, hp'⟩
    exact ⟨⟨a, hc.1⟩, ⟨b, hc.2⟩, (smem_kpair_l I hM hR hX p _ _).mpr hpab⟩
  · intro a b c hab hac
    exact Subtype.ext (hf.1.2 a.val b.val c.val
      ((smem_entry_l I hM hR hX a b F).mp hab) ((smem_entry_l I hM hR hX a c F).mp hac))
  · intro a
    rw [smem_member_l I hM hR a A, hf.2.1 a.val]
    refine ⟨fun ⟨b, hb⟩ => ⟨⟨b, (coords hb).2⟩, (smem_entry_l I hM hR hX a _ F).mpr hb⟩, ?_⟩
    rintro ⟨b, hb⟩
    exact ⟨b.val, (smem_entry_l I hM hR hX a b F).mp hb⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hf.2.2 a.val ((smem_member_l I hM hR a A).mp ha)
    exact ⟨⟨b, hX B.val B.property b hb⟩, (smem_member_l I hM hR _ B).mpr hb,
      (smem_entry_l I hM hR hX a _ F).mpr hab⟩

theorem smem_injection_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hL : ∀ a b : (L).Domain, ∃ p, Pair_d L p a b) (F A B : (L).Domain) :
    (L).IsSetInjectionFromTo (kpair_interpretation_l L (smem_ext_l I hM hR hX hE) hL) F A B ↔
      M.IsSetInjectionFromTo (kpair_interpretation_l M hE hP) F.val A.val B.val := by
  constructor
  · intro hf
    have hm (a : (L).Domain) y : M.mem y a.val ↔ ∃ s : (L).Domain, (L).mem s a ∧ s.val = y := by
      refine ⟨fun h => ⟨⟨y, hX a.val a.property y h⟩, (smem_member_l I hM hR _ a).mpr h, rfl⟩, ?_⟩
      rintro ⟨s, hs, rfl⟩
      exact (smem_member_l I hM hR s a).mp hs
    exact image_injection_l (M := L) (N := M) (hEN := hE) (hPN := hP)
      Subtype.val (fun _ _ he => Subtype.ext he) hm hf
  · intro hf
    exact ⟨(smem_function_l I hM hR hX hE hP hL F A B).mpr hf.1, fun a b c hac hbc =>
      Subtype.ext (hf.2 a.val b.val c.val ((smem_entry_l I hM hR hX a c F).mp hac)
        ((smem_entry_l I hM hR hX b c F).mp hbc))⟩

omit hM in
/-- N 包含内部 ω 时，它包含全部内部自然数，包括外部看来非标准的自然数。 -/
theorem selem_omega_subset_l (hZF : M.Models ZF) {ω d N S} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (he : Selem_d I ω c d) (hωN : M.mem ω N) : M.MemberSubset ω N := by
  let A := smdl_structure_l I (R := R) hS.source.2.1
  let K := smdl_structure_l I (R := S) hS.target.2.1
  have hzN e (he₀ : ∀ x, ¬ M.mem x e) (heω : M.mem e ω) : M.mem e N := by
    let φ : UnarySchema 0 := { body := Formula.isEmpty .newest }
    let ρ : Env A 0 := ⟨Fin.elim0, fun _ => ⟨ω, hS.subset ω hωN⟩⟩
    let η : Env K 0 := ⟨Fin.elim0, fun _ => ⟨ω, hωN⟩⟩
    let e' : A.Domain := ⟨e, hX ω (hS.subset ω hωN) e heω⟩
    obtain ⟨a, ha⟩ := selem_witness_l I hZF hω hS he φ ρ η (fun i => Fin.elim0 i)
      ⟨e', (Formula.satisfies_isEmpty_iff _ _).mpr (fun x hx => he₀ x.val ((smem_member_l I hS.source hR x e').mp hx))⟩
    have hem : a.val = e := hZF.1.eq_of_same_members _ _ (fun x => iff_of_false (fun hx =>
      (Formula.satisfies_isEmpty_iff _ _).mp ha ⟨x, hX a.val (hS.subset a.val a.property) x hx⟩
        ((smem_member_l I hS.source hR _ _).mpr hx)) (he₀ x))
    exact hem ▸ a.property
  apply hω.induction (fun n => M.mem n N)
  · let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ (⟨fun _ => N, fun _ => N⟩ : Env M 1) ω
    exact ⟨D, fun n => by simpa only [φ, Formula.satisfies_mem_iff] using! hD n⟩
  · intro e he₀
    obtain ⟨e', he', heω⟩ := hω.1.1
    have heq := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he₀ x))
    exact hzN e he₀ (heq ▸ heω)
  · intro n hn hnN s hs
    let φ : UnarySchema 1 := { body := Formula.isSuccessor .newest (.bound 1) }
    let ρ : Env A 1 := ⟨fun _ => ⟨n, hS.subset n hnN⟩, fun _ => ⟨n, hS.subset n hnN⟩⟩
    let η : Env K 1 := ⟨fun _ => ⟨n, hnN⟩, fun _ => ⟨n, hnN⟩⟩
    obtain ⟨s₀, hs₀, hs₀ω⟩ := hω.1.2 n hn
    have hsω : M.mem s ω := (hZF.1.eq_of_same_members s₀ s (fun x => (hs₀ x).trans (hs x).symm)) ▸ hs₀ω
    let s' : A.Domain := ⟨s, hX ω (hS.subset ω hωN) s hsω⟩
    obtain ⟨a, ha⟩ := selem_witness_l I hZF hω hS he φ ρ η (fun _ => rfl)
      ⟨s', (Formula.satisfies_isSuccessor_iff _ _ _).mpr ((smem_successor_l I hS.source hR hX hZF.1 s' _).mpr hs)⟩
    have has := (smem_successor_l I hS.source hR hX hZF.1 _ _).mp ((Formula.satisfies_isSuccessor_iff _ _ _).mp ha)
    exact (hZF.1.eq_of_same_members a.val s (fun x => (has x).trans (hs x).symm)) ▸ a.property

omit hM hX in
/-- 初等 N 中的内部可数集合 A 包含于 N；小单射图在 H(χ) 中实际存在。 -/
theorem selem_countable_subset_l (hZFC : M.Models ZFC) {ω χ d N S A}
    (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
    (hωχ : M.mem ω χ)
    (hH : H_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ X)
    (hS : Ssub_d I c d X R N S) (he : Selem_d I ω c d) (hωN : M.mem ω N) (hAN : M.mem A N)
    (hA : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) A ω) : M.MemberSubset A N := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hX := ZF.h_transitive_l J hZF hH
  let Q := smdl_structure_l I (R := R) hS.source.2.1
  let K := smdl_structure_l I (R := S) hS.target.2.1
  have hEL := smem_ext_l I hS.source hR hX hZF.1
  have hPL : ∀ a b : Q.Domain, ∃ p, Pair_d Q p a b := by
    intro a b
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) a.val b.val
    exact ⟨⟨p, h_pair_l hZFC hω hχ hωχ hH hp a.property b.property⟩,
      (smem_pair_l I hS.source hR hX _ a b).mpr hp⟩
  let JL := kpair_interpretation_l Q hEL hPL
  let ρ : Env Q 2 := (⟨fun _ => ⟨ω, hS.subset ω hωN⟩, fun _ => ⟨ω, hS.subset ω hωN⟩⟩ : Env Q 1).push ⟨A, hS.subset A hAN⟩
  let η : Env K 2 := (⟨fun _ => ⟨ω, hωN⟩, fun _ => ⟨ω, hωN⟩⟩ : Env K 1).push ⟨A, hAN⟩
  let φ : UnarySchema 2 := { body := Formula.isInjectionFromTo kpair_convention_l .newest (.bound 1) (.bound 2) }
  have hφ (f : Q.Domain) : φ.denote ρ f ↔ M.IsSetInjectionFromTo J f.val A ω :=
    (Formula.satisfies_isInjectionFromTo_iff JL hEL _ _ _ _).trans
      (smem_injection_l I hS.source hR hX hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hPL f _ _)
  obtain ⟨F, hF⟩ := hA
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF J A ω
  have hPH := h_product_l hZFC hω hχ hωχ hH (hS.subset A hAN) (hS.subset ω hωN) hP
  have hFH := ZF.h_subsets_l J hZF hχ.isLimitOrdinal hH hPH F (fun v hv => by
    obtain ⟨a, b, hv⟩ := hF.1.1.1 v hv
    have hab : Entry_d M a b F := ⟨v, hv, ‹M.mem v F›⟩
    exact (hP v).mpr ⟨a, hF.1.input_mem_of_pairMember hab, b, hF.1.output_mem_of_pairMember hab, hv⟩)
  obtain ⟨f, hf⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (fun _ => rfl))
    ⟨⟨F, hFH⟩, (hφ ⟨F, hFH⟩).mpr hF⟩
  have hf' := (hφ ⟨f.val, hS.subset f.val f.property⟩).mp hf
  intro a ha
  obtain ⟨n, hn, han⟩ := hf'.1.2.2 a ha
  obtain ⟨a', ha'N, ha'n⟩ := selem_entry_witness_l I hR hX hZF hω hS he f.property
    (selem_omega_subset_l I hR hX hZF hω hS he hωN n hn) ⟨a, han⟩
  exact hf'.2 a' a n ha'n han ▸ ha'N

omit hM in
/-- N 中后继序数的前驱仍属于 N；只需传递环境中的内部初等性。 -/
theorem selem_predecessor_l (hZF : M.Models ZF) {ω d N S α β} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (he : Selem_d I ω c d) (hβN : M.mem β N)
    (hα : M.IsOrdinal α) (hs : M.SuccessorOf β α) : M.mem α N := by
  let A := smdl_structure_l I (R := R) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env A 1 := ⟨fun _ => ⟨β, hS.subset β hβN⟩, fun _ => ⟨β, hS.subset β hβN⟩⟩
  let η : Env Q 1 := ⟨fun _ => ⟨β, hβN⟩, fun _ => ⟨β, hβN⟩⟩
  let φ : UnarySchema 1 := { body := Formula.isSuccessor (.bound 1) .newest }
  let a : A.Domain := ⟨α, hX β (hS.subset β hβN) α hs.predecessor_mem⟩
  obtain ⟨t, ht⟩ := selem_witness_l I hZF hω hS he φ ρ η (fun _ => rfl)
    ⟨a, (Formula.satisfies_isSuccessor_iff _ _ _).mpr ((smem_successor_l I hS.source hR hX hZF.1 _ a).mpr hs)⟩
  have ht' := (smem_successor_l I hS.source hR hX hZF.1 _ _).mp ((Formula.satisfies_isSuccessor_iff _ _ _).mp ht)
  exact (Structure.SuccessorOf.predecessor_eq hZF.1 hα hs ht').symm ▸ t.property

end YesMetaZFC.Model.Forcing.Internal
