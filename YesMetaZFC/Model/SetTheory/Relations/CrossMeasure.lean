import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.Relations.Small

/-! # 完整前驱图上的同一坐标迹

共同图搬运集合对象；其完整前驱方程把原对象的恒等坐标迹逐点识别为
施加源中的坐标迹。这里不要求任一载体传递，也不使用测度公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rr_trace_transport_l {T Γ Y S k D i t a A B : M.Domain}
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x y, M.PairMember I x y k → ∀ v,
      M.PairMember I v y S ↔ ∃ s, M.PairMember I s x T ∧ M.PairMember I s v k)
    (ft : M.IsSetFunctionFromTo I t D Y)
    (id : ∀ s x, M.PairMember I s x i ↔ M.mem s D ∧ s = x)
    (rt : M.IsRestrictionOf I t k D) (ha : M.PairMember I a A k) :
    Rt_trace_d I D i T a B ↔ Rt_trace_d I D t S A B := by
  apply forall_congr'
  intro s
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro hs
  obtain ⟨x, _, hsx⟩ := ft.2.2 s hs
  have atoms : M.PairMember I s a T ↔ M.PairMember I x A S := by
    refine ⟨fun h => (pred a A ha x).mpr ⟨s, h, ((rt.2 s x).mp hsx).2⟩, ?_⟩
    rintro h
    obtain ⟨r, hr, hrx⟩ := (pred a A ha x).mp h
    exact fk.2 r s x hrx ((rt.2 s x).mp hsx).2 ▸ hr
  have left : (∃ y, M.PairMember I s y i ∧ M.PairMember I y a T) ↔ M.PairMember I s a T :=
    ⟨fun ⟨y, hsy, hy⟩ => ((id s y).mp hsy).2.symm ▸ hy,
      fun h => ⟨s, (id s s).mpr ⟨hs, rfl⟩, h⟩⟩
  have right : (∃ y, M.PairMember I s y t ∧ M.PairMember I y A S) ↔ M.PairMember I x A S :=
    ⟨fun ⟨y, hsy, hy⟩ => ft.1.2 s y x hsy hsx ▸ hy, fun h => ⟨x, hsx, h⟩⟩
  exact left.trans (atoms.trans right.symm)

/-- 施加源中的集合迹，精确读取所属模型中同一集合对象的测度成员资格。 -/
theorem rr_measure_read_l {N T Γ Y S k D i t A B V : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := T) nx))
    (d u a : (smdl_structure_l I (R := T) nx).Domain)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ M.PairMember I x d.val T)
    (fi : M.IsSetFunctionFromTo I i D N)
    (id : ∀ s x, M.PairMember I s x i ↔ M.mem s D ∧ s = x)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x y, M.PairMember I x y k → ∀ v,
      M.PairMember I v y S ↔ ∃ s, M.PairMember I s x T ∧ M.PairMember I s v k)
    (ft : M.IsSetFunctionFromTo I t D Y) (rt : M.IsRestrictionOf I t k D)
    (ha : M.PairMember I a.val A k) (sub : (smdl_structure_l I (R := T) nx).MemberSubset a d)
    (bounded : ∀ b : (smdl_structure_l I (R := T) nx).Domain,
      M.PairMember I b.val u.val T → (smdl_structure_l I (R := T) nx).MemberSubset b d)
    (spec : ∀ C, M.mem C V ↔ ∃ b, M.mem b N ∧ M.PairMember I b u.val T ∧ Rt_trace_d I D i T b C)
    (trace : Rt_trace_d I D t S A B) : M.mem B V ↔ M.PairMember I a.val u.val T := by
  apply rt_measure_read_l I nx ext d u a fi ?_ sub
    ((rr_trace_transport_l I fk pred ft id rt ha).mpr trace) bounded spec
  intro x hx hxd
  have hD := (dc x).mpr ⟨hx, hxd⟩
  exact ⟨x, hD, (id x x).mpr ⟨hD, rfl⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 两个原关系切片之间的同一可测族

两侧任意集合先在各自模型内截到实际定义域。子集闭包把截集放回共同
切片，完整前驱图遂识别两侧的全部坐标迹。原测度因此直接成为施加源
实际子集族上的相对超滤；共同载体只保存对象码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_cross_measure_l {ω c X R c' Y S q N T Γ H k : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U d u : (smdl_structure_l I (R := T) nx).Domain)
    (trans : (smdl_structure_l I (R := T) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y S ↔ ∃ a, Rd_entry_d a x T ∧ Rd_entry_d a z k)
    (closed : Rr_closed_d I Y S H) (hdU : (smdl_structure_l I (R := T) nx).mem d U)
    (power : ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (measure : Maximal_d d u) :
    ∃ D t₀ t b P V, (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) ∧
      M.IsSetFunctionFromTo I t₀ D N ∧ (∀ x y, Rd_entry_d x y t₀ ↔ M.mem x D ∧ x = y) ∧
      M.IsRestrictionOf I t k D ∧ M.IsSetFunctionFromTo I t D Y ∧
      Rd_entry_d d.val b k ∧ Rd_entry_d b H S ∧
      (∀ s x, Rd_entry_d s x t → Rd_entry_d x b S) ∧
      (∀ x, Rd_entry_d x b S → ∃ s, M.mem s D ∧ Rd_entry_d s x t) ∧
      Rt_source_d I N T D t₀ P ∧ Rt_source_d I Y S D t P ∧ Rel_ultra_d D P V ∧
      ∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d I D t₀ T B A := by
  let N₀ := smdl_structure_l I (R := T) nx
  let ρ : Env M 2 := ⟨Fin.cases d.val (fun _ => T), fun _ => N⟩
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ ρ N
  have dc x : M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T :=
    (ds x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  have inside x (hx : M.mem x D) : M.mem x Γ :=
    (carrier x).mpr ⟨((dc x).mp hx).1, trans d hdU ⟨x, ((dc x).mp hx).1⟩ ((dc x).mp hx).2⟩
  let ψ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let η : Env M 0 := ⟨Fin.elim0, fun _ => N⟩
  have identity x y : ψ.denote η x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨t₀, ft₀, ts₀⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η
    (source := D) (target := N) (fun x _ => ⟨x, (identity x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((identity x y).mp hy).symm.trans ((identity x z).mp hz))
    (fun x y hx hy => (identity x y).mp hy ▸ ((dc x).mp hx).1)
  have id x y : Rd_entry_d x y t₀ ↔ M.mem x D ∧ x = y :=
    (ts₀ x y).trans (and_congr_right fun _ => identity x y)
  have dom₀ s x (hsx : Rd_entry_d s x t₀) : Rd_entry_d x d.val T :=
    ((id s x).mp hsx).2 ▸ ((dc s).mp ((id s x).mp hsx).1).2
  have onto₀ x (hxN : M.mem x N) (hx : Rd_entry_d x d.val T) : ∃ s, M.mem s D ∧ Rd_entry_d s x t₀ := by
    have hxD := (dc x).mpr ⟨hxN, hx⟩
    exact ⟨x, hxD, (id x x).mpr ⟨hxD, rfl⟩⟩
  obtain ⟨t, rt⟩ := ZF.exists_restriction hZF I k D
  have ft := rt.isSetFunctionFromTo fk.1 inside
  obtain ⟨b, hb, hdb⟩ := fk.1.2.2 d.val ((carrier d.val).mpr ⟨d.property, hdU⟩)
  have hbH := (image b).mpr ⟨d.val, (carrier d.val).mpr ⟨d.property, hdU⟩, hdb⟩
  have dom s x (hsx : Rd_entry_d s x t) : Rd_entry_d x b S :=
    (pred d.val b hdb x).mpr ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  have onto x (hx : Rd_entry_d x b S) : ∃ s, M.mem s D ∧ Rd_entry_d s x t := by
    obtain ⟨s, hs, hsx⟩ := (pred d.val b hdb x).mp hx
    have hsD := (dc s).mpr ⟨((carrier s).mp (fk.1.input_mem_of_pairMember hsx)).1, hs⟩
    exact ⟨s, hsD, (rt.2 s x).mpr ⟨hsD, hsx⟩⟩
  have traces a a' (ha : Rd_entry_d a a' k) A : Rt_trace_d I D t₀ T a A ↔ Rt_trace_d I D t S a' A :=
    rr_trace_transport_l I fk pred ft id rt ha
  obtain ⟨P, source⟩ := rt_source_exists_l I hZF N T D t₀
  have target : Rt_source_d I Y S D t P := by
    intro A
    constructor
    · intro hA
      obtain ⟨B, hB, trace⟩ := (source A).mp hA
      obtain ⟨a, cut⟩ := KP.intersection_exists_d hN d (⟨B, hB⟩ : N₀.Domain)
      have haU := ownerClosed d.val a.val d.property a.property hdU
        (fun x hx hxa => ((cut ⟨x, hx⟩).mp hxa).1)
      obtain ⟨a', ha', haa⟩ := fk.1.2.2 a.val ((carrier a.val).mpr ⟨a.property, haU⟩)
      refine ⟨a', ha', (traces a.val a' haa A).mp (fun s => (trace s).trans ?_)⟩
      exact and_congr_right fun _ => exists_congr fun x => and_congr_right fun hsx =>
        ((cut ⟨x, ft₀.output_mem_of_pairMember hsx⟩).trans (and_iff_right (dom₀ s x hsx))).symm
    · rintro ⟨B, hB, trace⟩
      obtain ⟨a', ha', cut⟩ := sc_cut_raw_l I hZF hω mx theory model hq true hb hB
      obtain ⟨a, ha, haa⟩ := (image a').mp (closed b a' hb ha' hbH
        (fun x hx hxa => ((cut x hx).mp hxa).1))
      refine (source A).mpr ⟨a, ((carrier a).mp ha).1, (traces a a' haa A).mpr (fun s => (trace s).trans ?_)⟩
      exact and_congr_right fun _ => exists_congr fun x => and_congr_right fun hsx =>
        ((cut x (ft.output_mem_of_pairMember hsx)).trans (and_iff_right (dom s x hsx))).symm
  obtain ⟨V, spec⟩ := rt_measure_exists_l I hZF N T D t₀ u.val
  have ultra := rt_ultra_l I hZF nx hN d u ft₀ dom₀ onto₀ power source measure spec
  exact ⟨D, t₀, t, b, P, V, dc, ft₀, id, rt, ft, hdb, hbH, dom, onto, source, target, ultra, spec⟩

end YesMetaZFC.SetTheory.Internal
