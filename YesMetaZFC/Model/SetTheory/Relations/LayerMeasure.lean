import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Relations.Small

/-! # 原关系测度在共同低层上的读取

共同层中的每个坐标子集均由完整前驱图实现，故原关系内部的极大滤子
决定该层的全部子集。测度仍可包含层外集合；施加时再限制到源的实际
可测族，不要求所属模型传递、外部可数闭合或整体坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 已实现集合的坐标迹就是该背景集合本身。 -/
theorem Rr_layer_d.trace_l {Γ Y S H k D A a t : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k) (ha : M.PairMember I A a k)
    (ht : M.IsRestrictionOf I t k D) (sub : M.MemberSubset A D) : Rt_trace_d I D t S a A := by
  intro s
  constructor
  · intro hs
    obtain ⟨x, _, hsx⟩ := layer.injection.1.2.2 s
      (layer.transitive A (layer.injection.1.input_mem_of_pairMember ha) s hs)
    exact ⟨sub s hs, x, (ht.2 s x).mpr ⟨sub s hs, hsx⟩,
      (layer.predecessors A a ha x).mpr ⟨s, hs, hsx⟩⟩
  · rintro ⟨_, x, hsx, hxa⟩
    obtain ⟨r, hr, hrx⟩ := (layer.predecessors A a ha x).mp hxa
    exact layer.injection.2 r s x hrx ((ht.2 s x).mp hsx).2 ▸ hr

/-- 原关系中的实际测度给出共同低层上的相对超滤。 -/
theorem Rr_layer_d.measure_l (hZF : M.Models ZF)
    {Γ Y S H k D : M.Domain} (layer : Rr_layer_d I Γ Y S H k)
    (hN : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Models KP)
    (d u : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hDd : M.PairMember I D d.val k)
    (power : ∃ p, (smdl_structure_l I (R := S) ⟨H, layer.member⟩).IsPowerSetOf p d)
    (measure : Maximal_d d u) :
    ∃ t P U, M.IsRestrictionOf I t k D ∧ Rt_source_d I Y S D t P ∧
      Rel_ultra_d D P U ∧ Sf_ultra_d Γ D U ∧
      ∀ A, M.mem A U ↔ ∃ B, M.mem B Y ∧ M.PairMember I B u.val S ∧ Rt_trace_d I D t S B A := by
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k D
  have ft := ht.isSetFunctionFromTo layer.injection.1
    (layer.transitive D (layer.injection.1.input_mem_of_pairMember hDd))
  obtain ⟨P, hP⟩ := rt_source_exists_l I hZF Y S D t
  obtain ⟨U, spec⟩ := rt_measure_exists_l I hZF Y S D t u.val
  have ultra := rt_ultra_l I hZF ⟨H, layer.member⟩ hN d u ft
    (fun s x hsx => (layer.predecessors D d.val hDd x).mpr
      ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩)
    (fun x _ hx => by
      obtain ⟨s, hs, hsx⟩ := (layer.predecessors D d.val hDd x).mp hx
      exact ⟨s, hs, (ht.2 s x).mpr ⟨hs, hsx⟩⟩) power hP measure spec
  have measurable A (hA : M.mem A Γ) (sub : M.MemberSubset A D) : M.mem A P := by
    obtain ⟨a, ha, hAa⟩ := layer.injection.1.2.2 A hA
    exact (hP A).mpr ⟨a, ha, layer.trace_l I hAa ht sub⟩
  exact ⟨t, P, U, ht, hP, ultra, ⟨ultra.base, ultra.proper,
    fun A B ha hb sub hab => ultra.upward A B ha (measurable B hb sub) hab,
    fun A B ha sub hb hc => ultra.decides A B (measurable A ha sub)
      (measurable B hb (fun x hx => ((hc x).mp hx).1)) hc⟩, spec⟩


/-- 原测度的所有成员均为有限幂的内部子集，子集闭包把其坐标迹完整回收到共同层。 -/
theorem Rr_layer_d.measure_capture_l (hE : Extensional M) {Γ Y S H k D t U : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k) (closed : Rr_closed_d I Y S H)
    (d u : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hDd : M.PairMember I D d.val k) (ht : M.IsRestrictionOf I t k D)
    (bounded : ∀ b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain,
      M.PairMember I b.val u.val S → ∀ x : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain,
        M.PairMember I x.val b.val S → M.PairMember I x.val d.val S)
    (spec : ∀ A, M.mem A U ↔ ∃ b, M.mem b Y ∧ M.PairMember I b u.val S ∧ Rt_trace_d I D t S b A) :
    ∀ A, M.mem A U ↔ ∃ b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain,
      M.PairMember I A b.val k ∧ M.PairMember I b.val u.val S := by
  have recover (b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain) (hb : M.PairMember I b.val u.val S) :=
    rr_capture_l I closed layer.transitive layer.injection layer.image layer.predecessors hDd b.property
      (fun x hx hxb => bounded b hb ⟨x, hx⟩ hxb)
  intro A
  constructor
  · intro hA
    obtain ⟨b, hb, hbu, trace⟩ := (spec A).mp hA
    obtain ⟨B, _, hBb, sub⟩ := recover ⟨b, hb⟩ hbu
    have eq := hE.eq_of_same_members A B (fun s => (trace s).trans (layer.trace_l I hBb ht sub s).symm)
    exact ⟨⟨b, hb⟩, eq.symm ▸ hBb, hbu⟩
  · rintro ⟨b, hAb, hbu⟩
    obtain ⟨B, _, hBb, sub⟩ := recover b hbu
    have eq := layer.injection.2 B A b.val hBb hAb
    subst B
    exact (spec A).mpr ⟨b.val, b.property, hbu, layer.trace_l I hAb ht sub⟩

end YesMetaZFC.SetTheory.Internal
