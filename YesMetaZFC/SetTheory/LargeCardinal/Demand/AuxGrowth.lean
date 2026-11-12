import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 奇父边上的辅助图延长和待填字母入图

四个旧坐标为长度、第一图、第二图、待填字母；新图取同次完整回合的
实际坐标。保存有限原公式，供内部递归及极限锥直接运输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u v
variable {M : Structure.{u}}

def td_aux_growth0_m : Formula 1 7 := .conj (KP.succ0_m (.bound 4) (.bound 0))
  (.conj (Formula.subset (.bound 1) (.bound 5))
    (.conj (Formula.subset (.bound 2) (.bound 6)) (rd_entry0_m (.bound 0) (.bound 3) (.bound 5))))

theorem td_aux_growth0_closed_l : td_aux_growth0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_aux_growth0_m,Definitional.Formula.FreeClosed]

theorem td_aux_growth0_delta_l : td_aux_growth0_m.IsDelta0 :=
  .conj (KP.succ0_delta_l ..) (.conj (.atom ..) (.conj (.atom ..) (rd_entry0_delta_l ..)))

def td_aux_growth_values_d {α : Type u} (v : Fin 4 → α) (w : Fin 62 → α) : Fin 7 → α :=
  fun i => [v 0,v 1,v 2,v 3,w 25,w 45,w 46].get i

def Td_aux_growth_d (I : kpair_convention_l.Interpretation M) (X R j : M.Domain)
    (v w : Fin 62 → M.Domain) : Prop := ∃ q : Fin 4 → M.Domain,
  (∀ i, Rd_entry_d (v ([25,45,46,49].get i)) (q i) j) ∧
    Rr_truth_d I X R td_aux_growth0_m (td_aux_growth_values_d q w)

theorem td_aux_growth_save_l (I : kpair_convention_l.Interpretation M) {X R j : M.Domain}
    (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (v : Fin 62 → M.Domain) (ρ ψ : Env (smdl_structure_l I (R := R) nx) 62)
    (points : ∀ i : Fin 4, Rd_entry_d (v ([25,45,46,49].get i)) (ρ.bound ([25,45,46,49].get i)).val j)
    (step : (smdl_structure_l I (R := R) nx).SuccessorOf (ψ.bound 25) (ρ.bound 25))
    (sa : (smdl_structure_l I (R := R) nx).MemberSubset (ρ.bound 45) (ψ.bound 45))
    (sb : (smdl_structure_l I (R := R) nx).MemberSubset (ρ.bound 46) (ψ.bound 46))
    (hit : Rd_entry_d (ρ.bound 25) (ρ.bound 49) (ψ.bound 45)) :
    Td_aux_growth_d I X R j v (fun i => (ψ.bound i).val) := by
  let q := fun i : Fin 4 => ρ.bound ([25,45,46,49].get i)
  let η : Env (smdl_structure_l I (R := R) nx) 7 := ⟨td_aux_growth_values_d q ψ.bound,fun _ => q 0⟩
  have valid : Formula.satisfies η td_aux_growth0_m := by
    simp only [td_aux_growth0_m,Formula.satisfies_conj_iff,KP.succ0_sat_l ext,
      Formula.satisfies_subset_iff,rd_entry0_sat_l ext]
    exact ⟨step,sa,sb,hit⟩
  have raw := (rr_truth_native_l I nx td_aux_growth0_m td_aux_growth0_closed_l η.bound).mpr valid
  have vals : (fun i => (η.bound i).val) =
      td_aux_growth_values_d (fun i => (q i).val) (fun i => (ψ.bound i).val) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))
  exact ⟨fun i => (q i).val,points,Eq.mp (congrArg (Rr_truth_d I X R td_aux_growth0_m) vals) raw⟩

theorem td_aux_growth_values_map_l {α : Type u} {β : Type v} (f : α → β) (q : Fin 4 → α) (w : Fin 62 → α) :
    (fun i => f (td_aux_growth_values_d q w i)) = td_aux_growth_values_d (fun i => f (q i)) (fun i => f (w i)) :=
  funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))

def td_aux_growth_m {d} (X R j : Term d) (v w : Fin 62 → Term d) : Formula 1 d :=
  let e : Term d → Term (4+d) := fun t => t.rename (Fin.natAdd 4)
  let q : Fin 4 → Term (4+d) := fun i => .bound (i.castAdd d)
  rb_exists_m (.conj (rb_conj_m (fun i : Fin 4 => rd_entry0_m (e (v ([25,45,46,49].get i))) (q i) (e j)))
    (rr_truth_m (𝒞 := kpair_convention_l) td_aux_growth0_m (e X) (e R)
      (td_aux_growth_values_d q (fun i => e (w i)))))

@[simp] theorem td_aux_growth_closed_l {d} (X R j : Term d) (v w : Fin 62 → Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hj : j.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = []) :
    (td_aux_growth_m X R j v w).FreeClosed := by
  simp -implicitDefEqProofs [td_aux_growth_m,Definitional.Formula.FreeClosed,hj,hv]
  apply rr_truth_closed_l td_aux_growth0_m td_aux_growth0_closed_l <;>
    simp [hX,hR,hw,td_aux_growth_values_d,Fin.forall_fin_succ]

theorem td_aux_growth_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (X R j : Term d) (v w : Fin 62 → Term d) :
    Formula.satisfies ρ (td_aux_growth_m X R j v w) ↔
      Td_aux_growth_d I (X.eval ρ) (R.eval ρ) (j.eval ρ) (fun i => (v i).eval ρ) (fun i => (w i).eval ρ) := by
  simp only [td_aux_growth_m,Td_aux_growth_d,rb_exists_sat_l,Formula.satisfies_conj_iff,rb_conj_sat_l,
    rd_entry0_sat_l hE,rr_truth_sat_l I _ td_aux_growth0_m td_aux_growth0_closed_l,
    td_aux_growth_values_map_l,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  rfl


end YesMetaZFC.SetTheory.LargeCardinal
