import YesMetaZFC.Model.Forcing.Boolean.DenseImage
import YesMetaZFC.Model.Forcing.Boolean.RegularAlgebra
import YesMetaZFC.SetTheory.Boolean.OrderIsomorphism

/-! # 内部稠密映射诱导实际完备布尔同构 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Dmap_d.completion_l {P R z Q S w F : M.Domain} (h : Dmap_d P R z Q S w F)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) : ∃ A T e C V d G,
      (∀ U, M.mem U A ↔ Ropen_d P R z U) ∧
      (∀ U W, Entry_d M U W T ↔ M.mem U A ∧ M.mem W A ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I A T e ∧
      (∀ U, M.mem U C ↔ Ropen_d Q S w U) ∧
      (∀ U W, Entry_d M U W V ↔ M.mem U C ∧ M.mem W C ∧ M.MemberSubset U W) ∧ BooleanZF.Cba_d I C V d ∧
      M.IsSetBijectionFromTo I G C A ∧ BooleanZF.Cbh_d I C V d A T e G ∧
      ∀ U W, Entry_d M U W G ↔ M.mem U C ∧ Rpull_d P z F U W := by
  obtain ⟨A,T,e,source,_,sourceOrder,sourceAlgebra⟩ := ropen_completion_l hZF O
  obtain ⟨C,V,d,target,_,targetOrder,targetAlgebra⟩ := ropen_completion_l hZF L
  let ρ : Env M 3 := ⟨fun i => [P,z,F].get i,fun _ => P⟩
  let φ : BinarySchema 3 := { body := rpull_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat U W : φ.denote ρ U W ↔ Rpull_d P z F U W := rpull_sat_l hZF.1 ..
  obtain ⟨G,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := A)
    (fun U _ => (rpull_exists_l hZF P z F U).imp fun W hw => (sat U W).mpr hw)
    (fun U _ X Y hx hy => hZF.1.eq_of_same_members X Y (fun p =>
      (((sat U X).mp hx) p).trans (((sat U Y).mp hy) p).symm))
    (fun U W hu hw => (source W).mpr (((sat U W).mp hw).regular_l h L ((target U).mp hu)))
  have graph U W : Entry_d M U W G ↔ M.mem U C ∧ Rpull_d P z F U W :=
    (values U W).trans (and_congr_right fun _ => sat U W)
  have reflect U W X Y (ux : Entry_d M U X G) (wy : Entry_d M W Y G) :
      Entry_d M X Y T ↔ Entry_d M U W V := by
    have hu := fn.input_mem_of_pairMember ux
    have hw := fn.input_mem_of_pairMember wy
    have hx := fn.output_mem_of_pairMember ux
    have hy := fn.output_mem_of_pairMember wy
    have order := (((graph U X).mp ux).2).order_l h L ((graph W Y).mp wy).2 ((target U).mp hu) ((target W).mp hw)
    exact ((sourceOrder X Y).trans (and_iff_right hx |>.trans (and_iff_right hy))).trans
      (order.trans ((targetOrder U W).trans (and_iff_right hu |>.trans (and_iff_right hw))).symm)
  have bij : M.IsSetBijectionFromTo I G C A := by
    refine ⟨⟨fn,fun U W X ux wx => ?_⟩,fun X hx => ?_⟩
    · have hu := fn.input_mem_of_pairMember ux
      have hw := fn.input_mem_of_pairMember wx
      have xx := sourceAlgebra.order.refl X (fn.output_mem_of_pairMember ux)
      exact targetAlgebra.order.antisymm U W hu hw ((reflect U W X X ux wx).mp xx) ((reflect W U X X wx ux).mp xx)
    · obtain ⟨U,hu,pull⟩ := h.ropen_image_l hZF L ((source X).mp hx)
      exact ⟨U,(target U).mpr hu,(graph U X).mpr ⟨(target U).mpr hu,pull⟩⟩
  exact ⟨A,T,e,C,V,d,G,source,sourceOrder,sourceAlgebra,target,targetOrder,targetAlgebra,bij,
    targetAlgebra.order_iso_l I sourceAlgebra.toBoolean_d bij reflect,graph⟩

end YesMetaZFC.Model.Forcing.Internal
