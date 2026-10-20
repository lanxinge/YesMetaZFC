import YesMetaZFC.Model.SetTheory.Internal.RelationLow
import YesMetaZFC.Model.SetTheory.Internal.RelationSeparationSource
import YesMetaZFC.Model.SetTheory.Internal.RelationTraceFamily
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter

/-! # 原关系源中的截集与低层子集回收

分离与低层对子集的封闭均沿全内部初等图搬运。原关系中的子集先截到
实际定义域，再由低层实现的完整前驱方程识别；不要求整个关系源传递或良基。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 同一分离构造同时给出原关系内部的交集与差集。 -/
theorem sc_cut_raw_l (hZF : M.Models ZF) {ω c X R c' Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (k : Bool) {D B : M.Domain} (hD : M.mem D Y) (hB : M.mem B Y) :
    ∃ Q, M.mem Q Y ∧ ∀ x, M.mem x Y →
      (M.PairMember I x Q S ↔ M.PairMember I x D S ∧
        if k then M.PairMember I x B S else ¬ M.PairMember I x B S) := by
  let φ : UnarySchema 1 := {
    body := if k then .mem .newest (.bound 1) else .neg (.mem .newest (.bound 1))
    freeClosed := by cases k <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  obtain ⟨Q, hQ, cut⟩ := sc_separate_raw_l I hZF hω hX hm theory model hq φ
    ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩ ⟨D, hD⟩
  refine ⟨Q, hQ, fun x hx => ?_⟩
  cases k <;> simpa only [φ, Bool.false_eq_true, ↓reduceIte, UnarySchema.denote,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval, Definitional.Term.newest, Env.push, fin_cases, smdl_structure_l] using cut ⟨x, hx⟩

/-- 源内低层对子集的封闭传到原关系的全部新参数。 -/
theorem Smap_d.subsets_raw_l (hZF : M.Models ZF) {ω c X R c' Y S q B H : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q) (hBH : M.PairMember I B H q)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B) :
    ∀ a b, M.mem a Y → M.mem b Y → M.PairMember I a H S →
      (∀ x, M.mem x Y → M.PairMember I x b S → M.PairMember I x a S) → M.PairMember I b H S := by
  have hB := hq.1.1.input_mem_of_pairMember hBH
  have hH := hq.1.1.output_mem_of_pairMember hBH
  let φ : Formula 1 1 := Formula.forallMem .newest (.forallE
    (.imp (Formula.subset .newest (.bound 1)) (.mem .newest (.bound 2))))
  let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 1 := ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 1 := ⟨fun _ => ⟨H, hH⟩, fun _ => ⟨H, hH⟩⟩
  have valid : Formula.satisfies ρ φ := by
    apply (smem_formula_l I hm ⟨⟨B, hB⟩⟩ φ ⟨ρ.bound, ρ.free⟩).mp
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff]
    intro a ha b sub
    exact closed a.val b.val ha b.property (fun x hx => sub ⟨x, hX b.val b.property x hx⟩ hx)
  have moved := (smap_source_l I hZF hω hm.1 model hq φ
    (by simp -implicitDefEqProofs [φ, Formula.forallMem, Definitional.Formula.FreeClosed])
    ρ η (fun _ => hBH)).mp valid
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff] at moved
  exact fun a b ha hb h sub => moved ⟨a, ha⟩ h ⟨b, hb⟩ (fun x => sub x.val x.property)

theorem rr_capture_l {Y S H Γ k D d Z : M.Domain}
    (closed : Rr_closed_d I Y S H)
    (hΓ : M.TransitiveSet Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ a, M.PairMember I a H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x a k)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    (hDd : M.PairMember I D d k) (hZ : M.mem Z Y)
    (sub : ∀ x, M.mem x Y → M.PairMember I x Z S → M.PairMember I x d S) :
    ∃ A, M.mem A Γ ∧ M.PairMember I A Z k ∧ M.MemberSubset A D := by
  have hd := fk.1.output_mem_of_pairMember hDd
  have hDH := (image d).mpr ⟨D, fk.1.input_mem_of_pairMember hDd, hDd⟩
  obtain ⟨A, hA, hAZ⟩ := (image Z).mp (closed d Z hd hZ hDH sub)
  refine ⟨A, hA, hAZ, fun s hs => ?_⟩
  obtain ⟨x, hx, hsx⟩ := fk.1.2.2 s (hΓ A hA s hs)
  obtain ⟨r, hr, hrx⟩ := (pred D d hDd x).mp (sub x hx ((pred A Z hAZ x).mpr ⟨s, hs, hsx⟩))
  exact fk.2 r s x hrx hsx ▸ hr

/-- 每个实际坐标子集都是共同低层中的同一个集合，而不只是与之同构。 -/
theorem Rt_source_d.recover_l (hZF : M.Models ZF) {ω c X R c' Y S q H Γ k D d t P : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (hΓ : M.TransitiveSet Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ a, M.PairMember I a H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x a k)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    (hDd : M.PairMember I D d k) (ht : M.IsRestrictionOf I t k D)
    (hP : Rt_source_d I Y S D t P) : M.MemberSubset P Γ := by
  have hd := fk.1.output_mem_of_pairMember hDd
  have hDH := (image d).mpr ⟨D, fk.1.input_mem_of_pairMember hDd, hDd⟩
  intro A hA
  obtain ⟨Z, hZY, trace⟩ := (hP A).mp hA
  -- 先在原模型内截到 d；子集闭包把这个新集合码放回原常值像 H。
  obtain ⟨Q, hQ, cut⟩ := sc_cut_raw_l I hZF hω hX hm theory model hq true hd hZY
  have cut x hx : M.PairMember I x Q S ↔ M.PairMember I x d S ∧ M.PairMember I x Z S := cut x hx
  have hQH := closed d Q hd hQ hDH
    (fun x hx h => ((cut x hx).mp h).1)
  obtain ⟨A₀, hA₀, hAQ⟩ := (image Q).mp hQH
  -- 两向使用完整前驱方程和实现图的单射性，得到背景集合的字面相等。
  have eq : A = A₀ := hZF.1.eq_of_same_members A A₀ fun s => by
    constructor
    · intro hs
      obtain ⟨hsD, x, hsx, hxZ⟩ := (trace s).mp hs
      have sk := ((ht.2 s x).mp hsx).2
      have hxQ := (cut x (fk.1.output_mem_of_pairMember sk)).mpr
        ⟨(pred D d hDd x).mpr ⟨s, hsD, sk⟩, hxZ⟩
      obtain ⟨y, hy, hyx⟩ := (pred A₀ Q hAQ x).mp hxQ
      exact fk.2 y s x hyx sk ▸ hy
    · intro hs
      obtain ⟨x, hx, sk⟩ := fk.1.2.2 s (hΓ A₀ hA₀ s hs)
      obtain ⟨hxd, hxZ⟩ := (cut x hx).mp ((pred A₀ Q hAQ x).mpr ⟨s, hs, sk⟩)
      obtain ⟨y, hy, hyx⟩ := (pred D d hDd x).mp hxd
      have hsD : M.mem s D := fk.2 y s x hyx sk ▸ hy
      exact (trace s).mpr ⟨hsD, x, (ht.2 s x).mpr ⟨hsD, sk⟩, hxZ⟩
  exact eq.symm ▸ hA₀

theorem Rt_source_d.field_l (hZF : M.Models ZF) {ω c X R c' Y S q D d t P : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (hd : M.mem d Y) (ft : M.IsSetFunctionFromTo I t D Y)
    (domain : ∀ s x, M.PairMember I s x t → M.PairMember I x d S)
    (hP : Rt_source_d I Y S D t P) : Field_d D P := by
  have bounds A (hA : M.mem A P) : M.MemberSubset A D := by
    obtain ⟨_, _, trace⟩ := (hP A).mp hA
    exact fun s hs => ((trace s).mp hs).1
  refine ⟨bounds, (hP D).mpr ⟨d, hd, fun s => ⟨fun hs => ?_, And.left⟩⟩, ?_, ?_⟩
  · obtain ⟨x, _, hsx⟩ := ft.2.2 s hs
    exact ⟨hs, x, hsx, domain s x hsx⟩
  · intro A hA
    obtain ⟨B, hB, trA⟩ := (hP A).mp hA
    obtain ⟨Q, hQ, cut⟩ := sc_cut_raw_l I hZF hω hX hm theory model hq false hd hB
    obtain ⟨C, trC⟩ := rt_trace_exists_l I hZF D t S Q
    have hC := (hP C).mpr ⟨Q, hQ, trC⟩
    refine ⟨C, hC, fun s => ?_⟩
    by_cases hs : M.mem s D
    · obtain ⟨x, hx, hsx⟩ := ft.2.2 s hs
      exact (trC.value_l I ft hsx).trans ((cut x hx).trans
        ((and_iff_right (domain s x hsx)).trans
          ((not_congr (trA.value_l I ft hsx).symm).trans (and_iff_right hs).symm)))
    · exact iff_of_false (fun h => hs (bounds C hC s h)) (fun h => hs h.1)
  · intro A B hA hB
    obtain ⟨Z, hZ, trA⟩ := (hP A).mp hA
    obtain ⟨V, hV, trB⟩ := (hP B).mp hB
    obtain ⟨Q, hQ, cut⟩ := sc_cut_raw_l I hZF hω hX hm theory model hq true hZ hV
    obtain ⟨C, trC⟩ := rt_trace_exists_l I hZF D t S Q
    have hC := (hP C).mpr ⟨Q, hQ, trC⟩
    refine ⟨C, hC, fun s => ?_⟩
    by_cases hs : M.mem s D
    · obtain ⟨x, hx, hsx⟩ := ft.2.2 s hs
      exact (trC.value_l I ft hsx).trans ((cut x hx).trans
        (and_congr (trA.value_l I ft hsx).symm (trB.value_l I ft hsx).symm))
    · exact iff_of_false (fun h => hs (bounds C hC s h)) (fun h => hs (bounds A hA s h.1))

/-- 任意已有低层实现直接提供真实测度的原关系坐标与限制，供递归后继重用。 -/
theorem Smap_d.measure_raw_l (hZF : M.Models ZF) {ω c X R c' Y S q H Γ k N D U : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (hΓ : M.TransitiveSet Γ) (inside : M.MemberSubset Γ N) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, M.PairMember I z H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x z k)
    (pred : ∀ x z, M.PairMember I x z k → ∀ w, M.PairMember I w z S ↔ ∃ y, M.mem y x ∧ M.PairMember I y w k)
    (hD : M.mem D Γ) (measure : Sf_ultra_d N D U) : ∃ d t P U',
      M.PairMember I D d k ∧ M.PairMember I d H S ∧ M.IsRestrictionOf I t k D ∧ M.IsSetFunctionFromTo I t D Y ∧
      (∀ s x, M.PairMember I s x t → M.PairMember I x d S) ∧
      Rt_source_d I Y S D t P ∧ M.MemberSubset P N ∧ Rel_ultra_d D P U' ∧
        ∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U := by
  obtain ⟨d, hd, hDd⟩ := fk.1.2.2 D hD
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k D
  have ft := ht.isSetFunctionFromTo fk.1 (hΓ D hD)
  have domain s x (hsx : M.PairMember I s x t) := (pred D d hDd x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  obtain ⟨P, hP⟩ := rt_source_exists_l I hZF Y S D t
  have low := hP.recover_l I hZF hω hX hm theory model hq closed hΓ fk image pred hDd ht
  have contains : M.MemberSubset P N := fun A hA => inside A (low A hA)
  obtain ⟨U', ultra, restriction⟩ := measure.restrict_l (ZF.modelsKP hZF) contains
    (hP.field_l I hZF hω hX hm theory model hq hd ft domain)
  exact ⟨d, t, P, U', hDd, (image d).mpr ⟨D, hD, hDd⟩, ht, ft, domain, hP, contains, ultra, restriction⟩

end YesMetaZFC.SetTheory.Internal
