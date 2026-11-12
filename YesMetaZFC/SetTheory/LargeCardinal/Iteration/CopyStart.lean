import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax

/-! # 从实际操作图读取唯一支撑列

载荷是原集合中的二重有序对；其支撑落在操作图的传递闭包内。
直接分离所需二元关系，不重选扩展器或另附支撑存在性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_levels_l {E : M.Domain} (function : M.IsSetFunction I E) :
    ∃ L, M.IsSetFunction I L ∧
      ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F := by
  obtain ⟨T,trans,hET,_⟩ := ZF.tc_exists_l I hZF E
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ p κ F,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,p,⌜(.bound 2 : Term 3)⌝ₛ) ∧
      ⌜it_payload_m⌝ₚ(p,κ,⌜(.newest : Term 3)⌝ₛ,F)⟫ }
  let η : Env M 1 := ⟨fun _ => E,fun _ => E⟩
  have sat i ρ : φ.denote η i ρ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,it_payload_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨L,relation,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I φ η T
  have law i ρ : Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F := by
    change M.PairMember I i ρ L ↔ _
    rw [graph,sat]
    refine ⟨fun h => h.2.2,fun h => ?_⟩
    obtain ⟨p,κ,F,⟨t,pair,ht⟩,r,pr,rf⟩ := h
    have bounds := pair.mem_l M trans (trans E hET t ht)
    exact ⟨bounds.1,(rf.mem_l M trans (pr.mem_l M trans bounds.2).2).1,
      p,κ,F,⟨t,pair,ht⟩,r,pr,rf⟩
  refine ⟨L,⟨relation.1,?_⟩,law⟩
  intro i ρ σ hi hj
  obtain ⟨p,κ,F,ip,pay⟩ := (law i ρ).mp hi
  obtain ⟨q,κ',F',iq,pay'⟩ := (law i σ).mp hj
  have eq := function.2 i p q ip iq
  exact (pay.unique_l (eq.symm ▸ pay')).2.1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定根嵌入实际生成复制初帧 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_row_d.frame_l {ω c₀ c X R A π z Z α o m T Q G E χ : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (succ : M.SuccessorOf m o)
    (empty : ∀ x, ¬ M.mem x o) (node : Rd_entry_d o c Q)
    (model : Smdl_d I c X R) (hχ : M.mem χ X)
    (zero : ∀ x, M.mem x X → ¬ Rd_entry_d x χ R) :
    ∃ H S Q' G', Ic_frame_d hZF ω (fun i => [o,m,T,Q,G,E,X,R,χ].get i) H S Q' G' ∧
      Ic_at_d H o X A π z Z α := by
  obtain ⟨Λ,lf,levels⟩ := it_levels_l hZF tree.move_function
  obtain ⟨m₀,H,S,Q',G',succ₀,hist,first⟩ := row.start_l hZF (E := E) (L := Λ) tree.diagram empty node
  have eq := succ₀.eq hZF.1 succ
  subst m₀
  let N := smdl_structure_l I (R := R) model.2.1
  let χ₀ : N.Domain := ⟨χ,hχ⟩
  have ordinal : Formula.satisfies (⟨fun _ => χ₀,fun _ => χ₀⟩ : Env N 1) (KP.ord0_m .newest) := by
    refine ⟨fun x hx => (zero x.val x.property hx).elim,?_,?_⟩
    · exact fun x hx => (zero x.val x.property hx).elim
    · exact fun x hx => (zero x.val x.property hx).elim
  have bound : Ic_bound_d I H Q X R π o χ :=
    ⟨(rr_truth_native_l I model.2.1 (KP.ord0_m .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => χ₀)).mpr ordinal,
      Or.inl zero,fun i _ hi _ => (empty i hi).elim⟩
  exact ⟨H,S,Q',G',⟨num_mem_l hZF.1 tree.omega (show Num_d 0 o from empty),
    Λ,lf,levels,hist,A,π,z,Z,α,first,bound⟩,first⟩

end YesMetaZFC.SetTheory.LargeCardinal
