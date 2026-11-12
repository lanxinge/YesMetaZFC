import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.Model.SetTheory.Embedding.Theory

/-! # 全乘积及顺序的返回像恒定

每次原根图都搬运同一个全乘积和顺序。原返回交换律使这两列在固定返回目标
中的值恒定；归纳针对实际记录坐标公式，仍覆盖全部内部自然数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_run_d.return_column_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F b r₀ E : M.Domain} {v₀ : Fin 26 → M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (a : Fin 26) (coordinate : a = 5 ∨ a = 6)
    (start : Rd_entry_d b r₀ F) (tuple₀ : Rt_tuple_d v₀ r₀)
    (returned : Rd_entry_d (v₀ a) E (v₀ 3)) :
    ∀ j r (v : Fin 26 → M.Domain),
      Rd_entry_d j r F → Rt_tuple_d v r → (b = j ∨ M.mem b j) → Rd_entry_d (v a) E (v 3) := by
  have columns {i r : M.Domain} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) :
      Rd_entry_d i (v 0) (v 23) ∧ Rd_entry_d i (v 3) (v 25) := by
    obtain ⟨w,wr,code,ret,_⟩ := run.columns_l hZF.1 model trans ir
    exact rt_tuple_inj_l wr vr ▸ ⟨code,ret⟩
  let ρ : Env M 3 := ⟨fun k => [F,b,E].get k,fun _ => F⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∀ r C σ,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term 4)⌝ₛ,r,⌜(.bound 1 : Term 4)⌝ₛ) →
    ⌜(rt_coord_m a)⌝ₚ(r,C) → ⌜(rt_coord_m (3 : Fin 26))⌝ₚ(r,σ) →
    (⌜(.bound 2 : Term 4)⌝ₛ = ⌜(.bound 0 : Term 4)⌝ₛ ∨ ⌜(.bound 2 : Term 4)⌝ₛ ∈ ⌜(.bound 0 : Term 4)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(C,⌜(.bound 3 : Term 4)⌝ₛ,σ)⟫ }
  have read j : φ.denote ρ j ↔ ∀ r C σ, Rd_entry_d j r F → Rt_coord_d a r C → Rt_coord_d (3 : Fin 26) r σ →
      (b = j ∨ M.mem b j) → Rd_entry_d C E σ := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all j : φ.denote ρ j := ZF.mem_ind_l M hZF I φ ρ (by
    intro j ih
    apply (read j).mpr
    intro r C σ jr cC cσ above
    obtain ⟨v,vr,_,_⟩ := run.columns_l hZF.1 model trans jr
    have coord {k : Fin 26} {x : M.Domain} (cx : Rt_coord_d k r x) : v k = x := by
      obtain ⟨w,wr,eq⟩ := cx
      exact (congrFun (rt_tuple_inj_l vr wr) k).trans eq
    have eC := coord cC
    have eσ := coord cσ
    have value : Rd_entry_d (v a) E (v 3) := by
      rcases above with eq | bj
      · have rr := (fn0_function_l (ZF.modelsKP hZF) run.function).1.2 j r r₀ jr (eq ▸ start)
        have ev := rt_tuple_inj_l vr (rr.symm ▸ tuple₀)
        exact ev.symm ▸ returned
      · obtain ⟨i,hi,succ⟩ := hΩ.exists_predecessor_of_mem_of_nonempty hZF (run.function.bound_l jr).1 ⟨b,bj⟩
        obtain ⟨s,_,is⟩ := run.function.2.1 i hi
        obtain ⟨w,ws,_,_⟩ := run.columns_l hZF.1 model trans is
        have bi : b = i ∨ M.mem b i := ((succ b).mp bj).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members b i eq))
        have old := (read i).mp (ih i succ.predecessor_mem)
          s (w a) (w 3) is ⟨w,ws,rfl⟩ ⟨w,ws,rfl⟩ bi
        obtain ⟨f,edge,product,order,_⟩ := run.step_links_l hZF.1 model trans succ is jr ws vr
        have keep := run.keep_l hZF.1 model trans succ is jr ws vr
        have hist := run.histories j r v jr vr
        have left := (run.queues i s w is ws).frame
        have right := (run.queues j r v jr vr).frame
        have oldCode := keep.1 i (w 0) (columns is ws).1
        have oldReturn := keep.2.2 i (w 3) (columns is ws).2
        have leg := hist.diagram.elementary i j f (w 0) (w 1) (w 2) (v 0) (v 1) (v 2)
          edge oldCode (columns jr vr).1 left.model.1 right.model.1
        have square := hist.returns.comp_l hZF hist.diagram (fun _ h => h) edge oldReturn (columns jr vr).2
        have image : Rd_entry_d (w a) (v a) f := coordinate.elim (fun eq => eq.symm ▸ product)
          (fun eq => eq.symm ▸ order)
        obtain ⟨Z,xZ,ZE⟩ := (square.2 (w a) E).mp old
        exact leg.1.1.1.2 _ _ _ xZ image ▸ ZE
    exact eC ▸ eσ ▸ value) j
  exact fun j r v jr vr above => (read j).mp (all j) r (v a) (v 3) jr ⟨v,vr,rfl⟩ ⟨v,vr,rfl⟩ above

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原全乘积的固定返回偏序

首行的实际全乘积经原返回嵌入确定条件域和顺序。所有后续行返回同一对集合；
偏序证书由该实际乘积运输得到，不另设公共目标偏序假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

structure Ab_return_order_d (F C U : M.Domain) : Prop where
  order : Cond_order_d M C U C
  rows : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    Rd_entry_d (v 5) C (v 3) ∧ Rd_entry_d (v 6) U (v 3)

variable (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_run_d.return_order_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∃ C U : (smdl_structure_l I (R := R) model.1.2.1).Domain, Ab_return_order_d F C.val U.val := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  obtain ⟨o,empty,ho⟩ := hΩ.1.1
  obtain ⟨r₀,_,start⟩ := run.function.2.1 o ho
  obtain ⟨v₀,tuple,_⟩ := run.columns_l hZF.1 model trans start
  have data := (run.queues o r₀ v₀ start tuple).frame
  have returns := data.returns
  let A := smdl_structure_l I (R := v₀ 2) data.model.1.2.1
  let B := smdl_structure_l I (R := S.val) run.target.1.2.1
  have hA := ZFC.models_zf_l (data.theory.native_l I hZF hΩ)
  have hB := (data.target_l hZF hΩ run.target run.transitive).1
  let w : A.Domain := ⟨ω.val,data.inside.1⟩
  let a : A.Domain := ⟨v₀ 4,data.inside.2.1⟩
  let p : A.Domain := ⟨v₀ 5,data.inside.2.2.1⟩
  let t : A.Domain := ⟨v₀ 6,data.inside.2.2.2.1⟩
  let n : A.Domain := ⟨v₀ 7,data.inside.2.2.2.2.1⟩
  let c₀ : A.Domain := ⟨v₀ 8,data.inside.2.2.2.2.2.1⟩
  let u₀ : A.Domain := ⟨v₀ 9,data.inside.2.2.2.2.2.2.1⟩
  obtain ⟨_,_,product,_⟩ := (ab_kernel_read_l I data.model data.transitive hA w a p t n c₀ u₀).mp data.kernel
  obtain ⟨e,elem,values⟩ := returns.project_l I hZF hΩ data.model.1 run.target.1
  have product' := fp_product_image_l hA hB e elem product
  have inj : Function.Injective (Subtype.val : B.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have order := image_cond_order_l (ZF.modelsKP hB) hZF.1 Subtype.val inj
    (smem_full_l I run.target run.transitive) (product'.order_l hB)
  let C : N.Domain := ⟨(e p).val,trans Y.val Y.property _ (e p).property⟩
  let U : N.Domain := ⟨(e t).val,trans Y.val Y.property _ (e t).property⟩
  refine ⟨C,U,order,?_⟩
  intro i r v ir vr
  have above : o = i ∨ M.mem o i := by
    rcases (hΩ.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare o ho i (run.function.bound_l ir).1 with eq | lt | gt
    · exact Or.inl (hZF.1.eq_of_same_members o i eq)
    · exact Or.inr lt
    · exact (empty i gt).elim
  exact ⟨run.return_column_l hZF model trans hΩ 5 (Or.inl rfl) start tuple (values p) i r v ir vr above,
    run.return_column_l hZF model trans hΩ 6 (Or.inr rfl) start tuple (values t) i r v ir vr above⟩

end YesMetaZFC.SetTheory.LargeCardinal
