import YesMetaZFC.Model.SetTheory.Internal.RelationRealization
import YesMetaZFC.Model.SetTheory.Internal.SourceSmall

/-! # 原关系低层的内在闭包

小性与子集封闭直接量化当前关系模型的全部对象。初等过渡保持这两条
原句，因此递归中新出现的低层无需是最初传递源中某个对象的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rr_closed_d (Y S H : M.Domain) : Prop := ∀ a b, M.mem a Y → M.mem b Y →
  M.PairMember I a H S → (∀ x, M.mem x Y → M.PairMember I x b S → M.PairMember I x a S) → M.PairMember I b H S

def Rf_small_d (Y S a : M.Domain) : Prop := ∃ ha : M.mem a Y,
  Formula.satisfies (⟨fun _ => ⟨a, ha⟩, fun _ => ⟨a, ha⟩⟩ :
    Env (smdl_structure_l I (R := S) ⟨a, ha⟩) 1) (sc_small_m .newest)

def Rr_small_d (Y S H : M.Domain) : Prop := ∀ a, M.mem a Y → M.PairMember I a H S → Rf_small_d I Y S a

def rr_closed_m : Formula 1 1 := Formula.forallMem .newest (.forallE
  (.imp (Formula.subset .newest (.bound 1)) (.mem .newest (.bound 2))))

def rr_small_m : Formula 1 1 := Formula.forallMem .newest (sc_small_m .newest)
derive_free_closed rr_closed_m
derive_free_closed rr_small_m

theorem rr_closed_native_l {Y S} (ny : ∃ y, M.mem y Y) (H : (smdl_structure_l I (R := S) ny).Domain) :
    Formula.satisfies (⟨fun _ => H, fun _ => H⟩ : Env (smdl_structure_l I (R := S) ny) 1) rr_closed_m ↔
      Rr_closed_d I Y S H.val := by
  simp only [rr_closed_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff]
  exact ⟨fun h a b ha hb haH sub => h ⟨a, ha⟩ haH ⟨b, hb⟩ (fun x => sub x.val x.property),
    fun h a ha b sub => h a.val b.val a.property b.property ha (fun x hx => sub ⟨x, hx⟩)⟩

theorem rr_small_native_l {Y S} (ny : ∃ y, M.mem y Y) (H : (smdl_structure_l I (R := S) ny).Domain) :
    Formula.satisfies (⟨fun _ => H, fun _ => H⟩ : Env (smdl_structure_l I (R := S) ny) 1) rr_small_m ↔
      Rr_small_d I Y S H.val := by
  rw [rr_small_m, Formula.satisfies_forallMem_iff]
  exact ⟨fun h a ha haH => ⟨ha, h ⟨a, ha⟩ haH⟩,
    fun h a ha => (h a.val a.property ha).elim fun _ valid => valid⟩

theorem Rf_small_d.index_l {Y S} (ny : ∃ y, M.mem y Y)
    (d : (smdl_structure_l I (R := S) ny).Domain) (h : Rf_small_d I Y S d.val) :
    ∃ μ e : (smdl_structure_l I (R := S) ny).Domain,
      Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
        Env (smdl_structure_l I (R := S) ny) 3) (sc_index_m .newest (.bound 1) (.bound 2)) := by
  obtain ⟨_, valid⟩ := h
  change Formula.satisfies (⟨fun _ => d, fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 1)
    (sc_small_m .newest) at valid
  simp only [sc_small_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨μ, e, index⟩ := valid
  refine ⟨μ, e, ?_⟩
  simpa [sc_index_m, sc_total0_m, KP.ord0_m, rd_entry0_m, kpair0_m, pair0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Function.comp_def, Env.push, fin_cases, Fin.cases, Fin.induction, Fin.induction.go] using index

theorem Smap_d.rr_closed_l (hZF : M.Models ZF) {ω c Y S o C W j H H' : M.Domain}
    (hω : M.IsOmega ω) (my : Smdl_d I c Y S) (mc : Smdl_d I o C W)
    (hj : Smap_d I ω c o Y C j) (hH : M.PairMember I H H' j) :
    Rr_closed_d I Y S H ↔ Rr_closed_d I C W H' := by
  let a : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨H, hj.1.1.input_mem_of_pairMember hH⟩
  let b : (smdl_structure_l I (R := W) mc.2.1).Domain := ⟨H', hj.1.1.output_mem_of_pairMember hH⟩
  exact (rr_closed_native_l I my.2.1 a).symm.trans
    ((smap_source_l I hZF hω my mc hj rr_closed_m
      (by simp -implicitDefEqProofs [rr_closed_m, Formula.forallMem, Definitional.Formula.FreeClosed])
      ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hH)).trans (rr_closed_native_l I mc.2.1 b))

theorem Smap_d.rr_small_l (hZF : M.Models ZF) {ω c Y S o C W j H H' : M.Domain}
    (hω : M.IsOmega ω) (my : Smdl_d I c Y S) (mc : Smdl_d I o C W)
    (hj : Smap_d I ω c o Y C j) (hH : M.PairMember I H H' j) :
    Rr_small_d I Y S H ↔ Rr_small_d I C W H' := by
  let a : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨H, hj.1.1.input_mem_of_pairMember hH⟩
  let b : (smdl_structure_l I (R := W) mc.2.1).Domain := ⟨H', hj.1.1.output_mem_of_pairMember hH⟩
  exact (rr_small_native_l I my.2.1 a).symm.trans
    ((smap_source_l I hZF hω my mc hj rr_small_m (by simp -implicitDefEqProofs [rr_small_m])
      ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hH)).trans (rr_small_native_l I mc.2.1 b))

end YesMetaZFC.SetTheory.Internal
