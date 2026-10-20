import YesMetaZFC.Model.SetTheory.Internal.RelationRealization
import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded

/-! # 原关系模型中共同低层的完整解释

只实现指定传递层的全部成员和全部前驱。高层载体可以尚未坍塌；全公式的
量词在该层内解释，不能把高层对象码当成背景集合来读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Rr_layer_d (Γ Y S H k : M.Domain) : Prop where
  transitive : M.TransitiveSet Γ
  member : M.mem H Y
  injection : M.IsSetInjectionFromTo I k Γ Y
  image : ∀ z, M.PairMember I z H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x z k
  predecessors : ∀ x z, M.PairMember I x z k → ∀ w,
    M.PairMember I w z S ↔ ∃ y, M.mem y x ∧ M.PairMember I y w k

/-- 用实际限制图实现任意传递子层；新层的成员方程就是原前驱方程。 -/
theorem Rr_layer_d.restrict_l (hZF : M.Models ZF) {Γ Y S H k B b : M.Domain}
    (h : Rr_layer_d I Γ Y S H k) (trans : M.TransitiveSet B) (image : M.PairMember I B b k) :
    ∃ t, Rr_layer_d I B Y S b t ∧ M.IsRestrictionOf I t k B := by
  have inside := h.transitive B (h.injection.1.input_mem_of_pairMember image)
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k B
  refine ⟨t, ⟨trans, h.injection.1.output_mem_of_pairMember image,
    ⟨ht.isSetFunctionFromTo h.injection.1 inside, fun x y z hx hy =>
      h.injection.2 x y z ((ht.2 x z).mp hx).2 ((ht.2 y z).mp hy).2⟩, ?_, ?_⟩, ht⟩
  · intro z
    apply (h.predecessors B b image z).trans
    exact exists_congr fun x => and_congr_right fun hx =>
      ⟨fun e => (ht.2 x z).mpr ⟨hx, e⟩, fun e => ((ht.2 x z).mp e).2⟩
  · intro x z hx w
    obtain ⟨hxB, hxz⟩ := (ht.2 x z).mp hx
    apply (h.predecessors x z hxz w).trans
    exact exists_congr fun y => and_congr_right fun hy =>
      ⟨fun e => (ht.2 y w).mpr ⟨trans x hxB y hy, e⟩, fun e => ((ht.2 y w).mp e).2⟩

/-- 原隶属模型的实际低层以恒等限制图实现，作为生产调用的初始实例。 -/
theorem rr_layer_mem_l (hZF : M.Models ZF) {c Y S Γ : M.Domain} (model : Smem_d I c Y S)
    (hY : M.TransitiveSet Y) (hΓ : M.mem Γ Y) (trans : M.TransitiveSet Γ) :
    ∃ k, Rr_layer_d I Γ Y S Γ k ∧ ∀ x y, M.PairMember I x y k ↔ M.mem x Γ ∧ x = y := by
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Γ⟩
  have read x y : φ.denote ρ x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨k, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := Γ) (target := Y) (fun x _ => ⟨x, (read x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((read x y).mp hy).symm.trans ((read x z).mp hz))
    (fun x y hx hy => (read x y).mp hy ▸ hY Γ hΓ x hx)
  have graph x y : M.PairMember I x y k ↔ M.mem x Γ ∧ x = y :=
    (spec x y).trans (and_congr Iff.rfl (read x y))
  refine ⟨k, ⟨trans, hΓ, ⟨fn, fun x y z hx hy => ((graph x z).mp hx).2.trans ((graph y z).mp hy).2.symm⟩, ?_, ?_⟩, graph⟩
  · intro z
    apply (model.2 z Γ).trans
    exact ⟨fun h => ⟨z, h.2.2, (graph z z).mpr ⟨h.2.2, rfl⟩⟩,
      fun ⟨x, hx, hz⟩ => ((graph x z).mp hz).2 ▸ ⟨hY Γ hΓ x hx, hΓ, hx⟩⟩
  · intro x z hz w
    obtain ⟨hx, rfl⟩ := (graph x z).mp hz
    apply (model.2 w x).trans
    exact ⟨fun h => ⟨w, h.2.2, (graph w w).mpr ⟨trans x hx w h.2.2, rfl⟩⟩,
      fun ⟨y, hy, hw⟩ => ((graph y w).mp hw).2 ▸ ⟨hY Γ hΓ y (trans x hx y hy), hY Γ hΓ x hx, hy⟩⟩

/-- 全量词相对化与低层原真值等价；前驱满性同时处理两个定义原子。 -/
theorem Rr_layer_d.relative_l {Γ Y S H k : M.Domain} (h : Rr_layer_d I Γ Y S H k)
    (nc : Nonempty {x // M.mem x Γ}) {n d} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l Γ nc) n) (η : Env (smdl_structure_l I (R := S) ⟨H, h.member⟩) d)
    (T : Term d) (a : Fin n → Term d) (hT : (T.eval η).val = H)
    (params : ∀ i, M.PairMember I (ρ.bound i).val ((a i).eval η).val k) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η (lr_rel_m φ T a) := by
  have term {n d} (ρ : Env (rt_model_l Γ nc) n)
      (η : Env (smdl_structure_l I (R := S) ⟨H, h.member⟩) d) (a : Fin n → Term d)
      (ha : ∀ i, M.PairMember I (ρ.bound i).val ((a i).eval η).val k)
      (t : Term n) (ht : t.freeSupport = []) : M.PairMember I (t.eval ρ).val ((t.bind a).eval η).val k := by
    cases t with
    | free _ => cases ht
    | bound i => exact ha i
  have mem (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      M.mem x.val y.val ↔ M.PairMember I v.val w.val S :=
    ⟨fun e => (h.predecessors y.val w.val hy v.val).mpr ⟨x.val, e, hx⟩,
      fun e => ((h.predecessors y.val w.val hy v.val).mp e).elim fun z hz =>
        h.injection.2 z x.val v.val hz.2 hx ▸ hz.1⟩
  have sub (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      (rt_model_l Γ nc).MemberSubset x y ↔ (smdl_structure_l I (R := S) ⟨H, h.member⟩).MemberSubset v w := by
    constructor
    · intro hs z hz
      obtain ⟨b, hb, hbk⟩ := (h.predecessors x.val v.val hx z.val).mp hz
      exact (mem ⟨b, h.transitive x.val x.property b hb⟩ y z w hbk hy).mp
        (hs ⟨b, h.transitive x.val x.property b hb⟩ hb)
    · intro hs z hz
      obtain ⟨b, hb, hzb⟩ := h.injection.1.2.2 z.val z.property
      exact (mem z y ⟨b, hb⟩ w hzb hy).mpr (hs ⟨b, hb⟩ ((mem z x ⟨b, hb⟩ v hzb hx).mp hz))
  have equal (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      (rt_model_l Γ nc).SameMembers x y ↔ (smdl_structure_l I (R := S) ⟨H, h.member⟩).SameMembers v w :=
    ⟨fun hs z => ⟨(sub x y v w hx hy).mp (fun b => (hs b).mp) z,
      (sub y x w v hy hx).mp (fun b => (hs b).mpr) z⟩,
      fun hs z => ⟨(sub x y v w hx hy).mpr (fun b => (hs b).mp) z,
        (sub y x w v hy hx).mpr (fun b => (hs b).mpr) z⟩⟩
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at closed
  case falsum | truth => rfl
  case mem s t => exact mem _ _ _ _ (term ρ η a params s closed.1) (term ρ η a params t closed.2)
  case atom r hr ts =>
    cases r <;> simp only [lr_rel_m, Formula.satisfies_atom_extensionalEq_iff,
      Formula.satisfies_atom_subset_iff, Definitional.TermVector.get_bind]
    · exact equal _ _ _ _ (term ρ η a params (ts 0) (closed 0)) (term ρ η a params (ts 1) (closed 1))
    · exact sub _ _ _ _ (term ρ η a params (ts 0) (closed 0)) (term ρ η a params (ts 1) (closed 1))
  case neg φ ih => exact not_congr (ih closed ρ η T a hT params)
  case conj φ ψ ih jh => exact and_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case disj φ ψ ih jh => exact or_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case imp φ ψ ih jh => exact imp_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case iff φ ψ ih jh => exact iff_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case existsE φ ih | forallE φ ih =>
    have next (x : (rt_model_l Γ nc).Domain) (y : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
        (hy : M.PairMember I x.val y.val k) := ih closed (ρ.push x) (η.push y) T.weaken
          (Fin.cases .newest (fun i => (a i).weaken)) (by simpa using hT)
          (Fin.cases hy (fun i => by
            simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
            simpa only [Env.push, fin_cases_succ] using params i))
    first
    | rw [lr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨y, hy, hxy⟩ := h.injection.1.2.2 x.val x.property
        refine ⟨⟨y, hy⟩, ?_, (next x ⟨y, hy⟩ hxy).mp hx⟩
        change M.PairMember I y (T.eval η).val S
        rw [hT]
        exact (h.image y).mpr ⟨x.val, x.property, hxy⟩
      · rintro ⟨y, hy, truth⟩
        change M.PairMember I y.val (T.eval η).val S at hy
        rw [hT] at hy
        obtain ⟨x, hx, hxy⟩ := (h.image y.val).mp hy
        exact ⟨⟨x, hx⟩, (next ⟨x, hx⟩ y hxy).mpr truth⟩
    | rw [lr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff]
      constructor
      · intro truth y hy
        change M.PairMember I y.val (T.eval η).val S at hy
        rw [hT] at hy
        obtain ⟨x, hx, hxy⟩ := (h.image y.val).mp hy
        exact (next ⟨x, hx⟩ y hxy).mp (truth ⟨x, hx⟩)
      · intro truth x
        obtain ⟨y, hy, hxy⟩ := h.injection.1.2.2 x.val x.property
        apply (next x ⟨y, hy⟩ hxy).mpr (truth ⟨y, hy⟩ ?_)
        change M.PairMember I y (T.eval η).val S
        rw [hT]
        exact (h.image y).mpr ⟨x.val, x.property, hxy⟩

end YesMetaZFC.SetTheory.Internal
