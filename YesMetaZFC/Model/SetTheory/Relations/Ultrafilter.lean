import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter

/-! # 原关系源实际拥有的子集族

每个背景子集必须由原模型中的集合码沿既有坐标图读出。
分离构造这一精确的集合族；任意内部逐点真值集都落在同一族中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rt_trace_d (D t R B A : M.Domain) : Prop := ∀ s, M.mem s A ↔ M.mem s D ∧
  ∃ x, M.PairMember I s x t ∧ M.PairMember I x B R

def rt_trace_m {d} (D t R B A : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest A.weaken) (.conj (.mem .newest D.weaken) (.existsE
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest t.weaken.weaken)
      (Formula.orderedPairMem 𝒞 .newest B.weaken.weaken R.weaken.weaken)))))
derive_free_closed rt_trace_m

theorem rt_trace_sat_l {d} (ρ : Env M d) (D t R B A : Term d) :
    Formula.satisfies ρ (rt_trace_m (𝒞 := 𝒞) D t R B A) ↔
      Rt_trace_d I (D.eval ρ) (t.eval ρ) (R.eval ρ) (B.eval ρ) (A.eval ρ) := by
  simp only [rt_trace_m, Rt_trace_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Rt_source_d (X R D t P : M.Domain) : Prop := ∀ A, M.mem A P ↔
  ∃ B, M.mem B X ∧ Rt_trace_d I D t R B A

theorem rt_trace_exists_l (hZF : M.Models ZF) (D t R B : M.Domain) : ∃ A, Rt_trace_d I D t R B A := by
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases R (fun _ => B)), fun _ => D⟩
  let φ : UnarySchema 3 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 4) (.bound 3))) }
  obtain ⟨A, spec⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨A, fun s => (spec s).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I]; rfl

theorem rt_source_exists_l (hZF : M.Models ZF) (X R D t : M.Domain) : ∃ P, Rt_source_d I X R D t P := by
  let ρ : Env M 4 := ⟨Fin.cases D (Fin.cases t (Fin.cases R (fun _ => X))), fun _ => X⟩
  let φ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 4)
      (rt_trace_m (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 4) .newest (.bound 1)) }
  obtain ⟨Q, power⟩ := ZF.exists_powerSet hZF D
  obtain ⟨P, spec⟩ := ZF.separation_exists_d hZF φ ρ Q
  have read A : φ.denote ρ A ↔ ∃ B, M.mem B X ∧ Rt_trace_d I D t R B A := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rt_trace_sat_l I]; rfl
  refine ⟨P, fun A => (spec A).trans ?_⟩
  exact ⟨fun h => (read A).mp h.2, fun h => ⟨(power A).mpr (fun s hs => h.elim fun _ hb => ((hb.2 s).mp hs).1),
    (read A).mpr h⟩⟩

theorem Rt_trace_d.value_l {X R D t B A s x} (trace : Rt_trace_d I D t R B A)
    (ft : M.IsSetFunctionFromTo I t D X) (hsx : M.PairMember I s x t) :
    M.mem s A ↔ M.PairMember I x B R := (trace s).trans
  ⟨fun ⟨_, y, hsy, hy⟩ => ft.1.2 s y x hsy hsx ▸ hy,
    fun hx => ⟨ft.input_mem_of_pairMember hsx, x, hsx, hx⟩⟩

theorem Rt_source_d.pointwise_l {X R D t P d B A b E F n r a}
    (h : Rt_source_d I X R D t P) (ft : M.IsSetFunctionFromTo I t D X)
    (domain : ∀ s x, M.PairMember I s x t → M.PairMember I x d R)
    (hB : M.mem B X) (trace : Rt_trace_d I D t R B A)
    (truth : ∀ x, M.mem x X → (M.PairMember I x B R ↔
      M.PairMember I x d R ∧ Pe_sat_d I b d X R E F n r a x)) :
    M.mem A P ∧ ∀ s x, M.PairMember I s x t →
      (M.mem s A ↔ Pe_sat_d I b d X R E F n r a x) := by
  refine ⟨(h A).mpr ⟨B, hB, trace⟩, fun s x hsx => ?_⟩
  exact (trace.value_l I ft hsx).trans ((truth x (ft.output_mem_of_pairMember hsx)).trans
    (and_iff_right (domain s x hsx)))

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系内部测度的实际坐标超滤

坐标图覆盖定义域的全部原关系成员。内部测度沿该图读成背景中的集合，
并在模型实际拥有的坐标子集上满足相对超滤公理。测度对象不要求位于
共同低层，原关系模型也不要求传递或良基。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 内部滤子成员的全部实际坐标迹由一次背景分离构造。 -/
theorem rt_measure_exists_l (hZF : M.Models ZF) (X R D t U : M.Domain) :
    ∃ V, ∀ A, M.mem A V ↔ ∃ B, M.mem B X ∧ M.PairMember I B U R ∧ Rt_trace_d I D t R B A := by
  let ρ : Env M 5 := ⟨Fin.cases U (Fin.cases t (Fin.cases R (Fin.cases D (fun _ => X)))), fun _ => X⟩
  let φ : UnarySchema 5 := {
    body := Formula.existsMem (.bound 5)
      (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))
      (rt_trace_m (𝒞 := 𝒞) (.bound 5) (.bound 3) (.bound 4) .newest (.bound 1))) }
  have read A : φ.denote ρ A ↔ ∃ B, M.mem B X ∧ M.PairMember I B U R ∧ Rt_trace_d I D t R B A := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rt_trace_sat_l I]; rfl
  obtain ⟨Q, power⟩ := ZF.exists_powerSet hZF D
  obtain ⟨V, spec⟩ := ZF.separation_exists_d hZF φ ρ Q
  refine ⟨V, fun A => (spec A).trans ?_⟩
  exact ⟨fun h => (read A).mp h.2, fun h => ⟨(power A).mpr
    (fun s hs => h.elim fun _ h => ((h.2.2 s).mp hs).1), (read A).mpr h⟩⟩

/-- 原滤基的全部坐标迹仍是滤基；所属结构无需满足任何集合论公理。 -/
theorem rt_base_l (hZF : M.Models ZF) {X R D t V : M.Domain}
    (nx : ∃ x, M.mem x X) (d u : (smdl_structure_l I (R := R) nx).Domain)
    (ft : M.IsSetFunctionFromTo I t D X)
    (domain : ∀ s x, M.PairMember I s x t → M.PairMember I x d.val R)
    (base : Base_d d u)
    (spec : ∀ A, M.mem A V ↔ ∃ B, M.mem B X ∧ M.PairMember I B u.val R ∧ Rt_trace_d I D t R B A) :
    Base_d D V := by
  have top : Rt_trace_d I D t R d.val D := fun s => ⟨fun hs => by
    obtain ⟨x, _, hsx⟩ := ft.2.2 s hs
    exact ⟨hs, x, hsx, domain s x hsx⟩, And.left⟩
  have bounds A (hA : M.mem A V) : M.MemberSubset A D := by
    obtain ⟨_, _, _, tr⟩ := (spec A).mp hA
    exact fun s hs => ((tr s).mp hs).1
  refine ⟨bounds, (spec D).mpr ⟨d.val, d.property, base.top, top⟩, ?_⟩
  intro A B hA hB
  obtain ⟨a, ha, hau, trA⟩ := (spec A).mp hA
  obtain ⟨b, hb, hbu, trB⟩ := (spec B).mp hB
  obtain ⟨c, hcu, ca, cb⟩ := base.meet ⟨a, ha⟩ ⟨b, hb⟩ hau hbu
  obtain ⟨C, trC⟩ := rt_trace_exists_l I hZF D t R c.val
  have pull {a : (smdl_structure_l I (R := R) nx).Domain} {A : M.Domain}
      (trA : Rt_trace_d I D t R a.val A) (ca : (smdl_structure_l I (R := R) nx).MemberSubset c a) :
      M.MemberSubset C A := by
    rintro s hs
    obtain ⟨hsD, x, hsx, hxc⟩ := (trC s).mp hs
    exact (trA s).mpr ⟨hsD, x, hsx, ca ⟨x, ft.output_mem_of_pairMember hsx⟩ hxc⟩
  exact ⟨C, (spec C).mpr ⟨c.val, c.property, hcu, trC⟩, pull trA ca, pull trB cb⟩

/-- 满坐标上的内部极大滤子给出精确子集代数上的真实超滤。 -/
theorem rt_ultra_l (hZF : M.Models ZF) {X R D t P V : M.Domain}
    (nx : ∃ x, M.mem x X) (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (d u : (smdl_structure_l I (R := R) nx).Domain)
    (ft : M.IsSetFunctionFromTo I t D X)
    (domain : ∀ s x, M.PairMember I s x t → M.PairMember I x d.val R)
    (onto : ∀ x, M.mem x X → M.PairMember I x d.val R → ∃ s, M.mem s D ∧ M.PairMember I s x t)
    (power : ∃ p, (smdl_structure_l I (R := R) nx).IsPowerSetOf p d)
    (source : Rt_source_d I X R D t P) (measure : Maximal_d d u)
    (spec : ∀ A, M.mem A V ↔ ∃ B, M.mem B X ∧ M.PairMember I B u.val R ∧ Rt_trace_d I D t R B A) :
    Rel_ultra_d D P V := by
  let N := smdl_structure_l I (R := R) nx
  obtain ⟨p, power⟩ := power
  have bounds A (hA : M.mem A P) : M.MemberSubset A D := by
    obtain ⟨_, _, trace⟩ := (source A).mp hA
    exact fun s hs => ((trace s).mp hs).1
  have top : Rt_trace_d I D t R d.val D := fun s => ⟨fun hs => by
    obtain ⟨x, _, hsx⟩ := ft.2.2 s hs
    exact ⟨hs, x, hsx, domain s x hsx⟩, And.left⟩
  -- 任意坐标迹先在原模型内截到 d，随后才作子集比较。
  have normalize A (hA : M.mem A P) : ∃ a : N.Domain, N.MemberSubset a d ∧ Rt_trace_d I D t R a.val A := by
    obtain ⟨B, hB, trace⟩ := (source A).mp hA
    obtain ⟨a, cut⟩ := KP.intersection_exists_d hN d (⟨B, hB⟩ : N.Domain)
    refine ⟨a, fun x hx => ((cut x).mp hx).1, fun s => ?_⟩
    by_cases hs : M.mem s D
    · obtain ⟨x, hx, hsx⟩ := ft.2.2 s hs
      apply (trace.value_l I ft hsx).trans
      exact ⟨fun h => ⟨hs, x, hsx, (cut ⟨x, hx⟩).mpr ⟨domain s x hsx, h⟩⟩,
        fun ⟨_, y, hsy, hy⟩ => ft.1.2 s y x hsy hsx ▸ ((cut ⟨y, ft.output_mem_of_pairMember hsy⟩).mp hy).2⟩
    · exact iff_of_false (fun h => hs (bounds A hA s h)) (fun h => hs h.1)
  have reflect {a b : N.Domain} {A B : M.Domain} (ad : N.MemberSubset a d)
      (ha : Rt_trace_d I D t R a.val A) (hb : Rt_trace_d I D t R b.val B)
      (ab : M.MemberSubset A B) : N.MemberSubset a b := by
    intro x hx
    obtain ⟨s, _, hsx⟩ := onto x.val x.property (ad x hx)
    exact (hb.value_l I ft hsx).mp (ab s ((ha.value_l I ft hsx).mpr hx))
  have field : Field_d D P := by
    refine ⟨bounds, (source D).mpr ⟨d.val, d.property, top⟩, ?_, ?_⟩
    · intro A hA
      obtain ⟨a, _, ha⟩ := normalize A hA
      obtain ⟨b, diff⟩ := KP.difference_exists_d hN a d
      obtain ⟨B, hb⟩ := rt_trace_exists_l I hZF D t R b.val
      refine ⟨B, (source B).mpr ⟨b.val, b.property, hb⟩, fun s => ?_⟩
      by_cases hs : M.mem s D
      · obtain ⟨x, hx, hsx⟩ := ft.2.2 s hs
        exact (hb.value_l I ft hsx).trans ((diff ⟨x, hx⟩).trans
          ((and_iff_right (domain s x hsx)).trans
            ((not_congr (ha.value_l I ft hsx).symm).trans (and_iff_right hs).symm)))
      · exact iff_of_false (fun h => hs ((hb s).mp h).1) (fun h => hs h.1)
    · intro A B hA hB
      obtain ⟨a, _, ha⟩ := normalize A hA
      obtain ⟨b, _, hb⟩ := normalize B hB
      obtain ⟨c, inter⟩ := KP.intersection_exists_d hN a b
      obtain ⟨C, hc⟩ := rt_trace_exists_l I hZF D t R c.val
      refine ⟨C, (source C).mpr ⟨c.val, c.property, hc⟩, fun s => ?_⟩
      by_cases hs : M.mem s D
      · obtain ⟨x, hx, hsx⟩ := ft.2.2 s hs
        exact (hc.value_l I ft hsx).trans ((inter ⟨x, hx⟩).trans
          (and_congr (ha.value_l I ft hsx).symm (hb.value_l I ft hsx).symm))
      · exact iff_of_false (fun h => hs ((hc s).mp h).1) (fun h => hs (bounds A hA s h.1))
  have admissible : M.MemberSubset V P := fun A hA => by
    obtain ⟨a, ha, _, trace⟩ := (spec A).mp hA
    exact (source A).mpr ⟨a, ha, trace⟩
  refine ⟨field, rt_base_l I hZF nx d u ft domain measure.1.base_l spec, admissible, ?_, ?_, ?_⟩
  · intro A B hA hB ab
    obtain ⟨a, ha, hau, trA⟩ := (spec A).mp hA
    obtain ⟨b, bd, trB⟩ := normalize B hB
    have au := (show N.mem (⟨a, ha⟩ : N.Domain) u from hau)
    exact (spec B).mpr ⟨b.val, b.property,
      measure.1.2.2.1 ⟨a, ha⟩ b au (reflect (measure.1.1 _ au) trA trB ab) bd, trB⟩
  · intro A hA
    obtain ⟨a, ha, hau, trace⟩ := (spec A).mp hA
    obtain ⟨x, hx⟩ := measure.2.1 (⟨a, ha⟩ : N.Domain) hau
    obtain ⟨s, _, hsx⟩ := onto x.val x.property (measure.1.1 (⟨a, ha⟩ : N.Domain) hau x hx)
    exact ⟨s, (trace.value_l I ft hsx).mpr hx⟩
  · intro A B hA hB comp
    obtain ⟨a, ad, trA⟩ := normalize A hA
    obtain ⟨b, bd, trB⟩ := normalize B hB
    have complement x : N.mem x b ↔ N.mem x d ∧ ¬ N.mem x a := by
      by_cases hx : N.mem x d
      · obtain ⟨s, hs, hsx⟩ := onto x.val x.property hx
        exact (trB.value_l I ft hsx).symm.trans ((comp s).trans
          (and_congr (iff_of_true hs hx) (not_congr (trA.value_l I ft hsx))))
      · exact iff_of_false (fun h => hx (bd x h)) (fun h => hx h.1)
    exact (maximal_decides_d hN power measure ad complement).imp
      (fun h => (spec A).mpr ⟨a.val, a.property, h, trA⟩)
      (fun h => (spec B).mpr ⟨b.val, b.property, h, trB⟩)

/-- 满坐标精确读取任意内部子集的测度成员资格，不要求坐标子集本身是源对象码。 -/
theorem rt_measure_read_l {X R D t V A : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (d u a : (smdl_structure_l I (R := R) nx).Domain)
    (ft : M.IsSetFunctionFromTo I t D X)
    (onto : ∀ x, M.mem x X → M.PairMember I x d.val R → ∃ s, M.mem s D ∧ M.PairMember I s x t)
    (sub : (smdl_structure_l I (R := R) nx).MemberSubset a d)
    (trace : Rt_trace_d I D t R a.val A)
    (bounded : ∀ b : (smdl_structure_l I (R := R) nx).Domain,
      M.PairMember I b.val u.val R → (smdl_structure_l I (R := R) nx).MemberSubset b d)
    (spec : ∀ B, M.mem B V ↔ ∃ b, M.mem b X ∧ M.PairMember I b u.val R ∧ Rt_trace_d I D t R b B) :
    M.mem A V ↔ M.PairMember I a.val u.val R := by
  refine ⟨?_, fun h => (spec A).mpr ⟨a.val, a.property, h, trace⟩⟩
  intro hA
  obtain ⟨b, hb, hbu, tr⟩ := (spec A).mp hA
  let b' : (smdl_structure_l I (R := R) nx).Domain := ⟨b, hb⟩
  have eq : b' = a := ext.eq_of_same_members b' a (fun x => by
    constructor
    · intro hx
      obtain ⟨s, _, hsx⟩ := onto x.val x.property (bounded b' hbu x hx)
      exact (trace.value_l I ft hsx).mp ((tr.value_l I ft hsx).mpr hx)
    · intro hx
      obtain ⟨s, _, hsx⟩ := onto x.val x.property (sub x hx)
      exact (tr.value_l I ft hsx).mp ((trace.value_l I ft hsx).mpr hx))
  exact (show b = a.val from congrArg Subtype.val eq) ▸ hbu

end YesMetaZFC.SetTheory.Internal
